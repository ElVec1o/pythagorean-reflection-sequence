// t2abs_iv -- verified enclosure of the rectangle bound of Lemma lem:T2abs (paper 2).
//
// See README.md for the statement being certified, the arithmetic model, and the
// division of labour between this program (tau in [2/wmax^2, 0.02]) and the
// analytic small-tau lemma.
//
// Usage:
//   t2abs_iv point <w> [prec]                 one (tau, X) = (2/w^2, w) point, piecewise table
//   t2abs_iv scan <wmax> [prec] [threads]     branch-and-bound over w in [10, wmax],
//                                             X in [W(tau), w(tau)]
//
// All arithmetic is MPFR interval arithmetic with outward rounding (see iv.rs).

mod iv;
use iv::{prec, set_prec, Cx, Iv};
use rug::float::Round;
use rug::ops::AddAssignRound;
use std::collections::BinaryHeap;
use std::sync::atomic::{AtomicUsize, Ordering as AOrd};
use std::sync::Mutex;

// ---------------------------------------------------------------- constants
// The two amplitude constants imported from Lemma lem:Bbounded of the paper.
const C_CRUDE: f64 = 30.3; // |B_s| <= 30.3 sqrt(tau)      (eq:Bbounds)
const C_TRUNC: f64 = 0.02; // eq:Btrunc remainder constant
static TARGET_C_CELL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
fn target_c() -> f64 {
    f64::from_bits(TARGET_C_CELL.load(AOrd::Relaxed))
}

// ---------------------------------------------------------------- context
struct Ctx {
    w: Iv,       // w = sqrt(2/tau)
    x: Iv,       // the argument X, with tau X^2 in [2e^{-tau}, 2]
    xhalf: Iv,   // X/2, the half-height of the rectangle
    lnx: Iv,
    lnpi: Iv,
    crude: Iv,   // 1 + exp(C_CRUDE sqrt(tau))
    tau2_24: Iv, // tau^2/24
    rem: Iv,     // C_TRUNC tau^{3/2}
    hconst: Iv,  // (1/2)log 2pi - log(1-e^{-pi X}) - (1/2)log X
    sstar: f64,  // right edge, the largest half-odd-integer < 2w
    jj: i64,     // sstar = jj + 1/2
}

impl Ctx {
    fn new(wlo: f64, whi: f64, xlo: f64, xhi: f64, jj: i64) -> Ctx {
        let w = Iv::ab(wlo, whi);
        let x = Iv::ab(xlo, xhi);
        let tau = Iv::c(2.0).div(&w.sqr());
        let xhalf = x.scal(0.5);
        let pi = Iv::pi();
        let sq = tau.sqrt();
        let crude = sq.scal(C_CRUDE).exp().shift(1.0);
        let tau2_24 = tau.sqr().div(&Iv::c(24.0));
        let rem = tau.mul(&sq).scal(C_TRUNC);
        // (1/2)log(2pi) - log(1 - e^{-pi X}) - (1/2)log X
        let hconst = pi
            .scal(2.0)
            .ln()
            .scal(0.5)
            .sub(&Iv::one().sub(&pi.mul(&x).neg().exp()).ln())
            .sub(&x.ln().scal(0.5));
        Ctx {
            w,
            lnx: x.ln(),
            x,
            xhalf,
            lnpi: pi.ln(),
            crude,
            tau2_24,
            rem,
            hconst,
            sstar: jj as f64 + 0.5,
            jj,
        }
    }
}

// ------------------------------------------------- amplitude majorant |g_s|
// |g_s| <= 1 + e^{30.3 sqrt tau} everywhere on the strip S (eq:Bbounds), and
// |g_s| <= |B_s| e^{|B_s|} with |B_s| <= (tau^2/24)|M^3/3 + M^2/2 - M/3| +
// 0.02 tau^{3/2} on the sub-region |M| <= 2w (eq:Btrunc), M = 2s.
fn amp(s: &Cx, c: &Ctx) -> Iv {
    if s.abs().hi <= c.w.lo {
        let three = Iv::c(3.0);
        let m = s.scal(2.0);
        let m2 = m.mul(&m);
        let m3 = m2.mul(&m);
        let p = Cx {
            re: m3.re.div(&three).add(&m2.re.scal(0.5)).sub(&m.re.div(&three)),
            im: m3.im.div(&three).add(&m2.im.scal(0.5)).sub(&m.im.div(&three)),
        }
        .abs();
        let b = c.tau2_24.mul(&p).add(&c.rem);
        b.mul(&b.exp()).min(&c.crude)
    } else {
        c.crude.clone()
    }
}

// |Gamma(1+iy)|^2 = pi y / sinh(pi y): even, decreasing in |y|, equal to 1 at y=0.
fn gam1sq(y: &Iv) -> Iv {
    let ay = y.abs();
    let pi = Iv::pi();
    let far = pi.mul(&Iv::of(ay.hi.clone(), ay.hi.clone()));
    let lo = far.div(&far.sinh()).lo.clone();
    let hi = if ay.lo == 0.0 {
        iv::fl(1.0)
    } else {
        let near = pi.mul(&Iv::of(ay.lo.clone(), ay.lo.clone()));
        near.div(&near.sinh()).hi.clone()
    };
    Iv::of(lo, hi)
}

// -------------------------------------------------------------- integrands
// Left edge, Re s = 1/2, s = 1/2 + it.  Here 2s+1 = 2+2it and
//   |Gamma(2+2it)| = |1+2it| |Gamma(1+2it)|,   |Gamma(1+2it)|^2 = 2 pi t/sinh(2 pi t),
// so the kernel collapses to the closed form
//   X^{2s}/|Gamma(2s+1)| * |pi/sin(pi s)| = X pi sqrt(g(pi t)) / sqrt(1+4t^2),
// with g(u) = tanh(u)/u.  The two exponentials cancel *symbolically* here, which
// is what keeps the interval enclosure tight; no Stirling is used on this edge.
fn tanh_over(u: &Iv) -> Iv {
    // g(u) = tanh(u)/u on u >= 0: even, decreasing in |u|, g(0) = 1.
    let a = u.abs();
    let hi = if a.lo == 0.0 {
        iv::fl(1.0)
    } else {
        let n = Iv::of(a.lo.clone(), a.lo.clone());
        n.tanh().div(&n).hi.clone()
    };
    let lo = if a.hi == 0.0 {
        iv::fl(1.0)
    } else {
        let f = Iv::of(a.hi.clone(), a.hi.clone());
        f.tanh().div(&f).lo.clone()
    };
    Iv::of(lo, hi)
}

fn f_left(t: &Iv, c: &Ctx) -> Iv {
    let pi = Iv::pi();
    let ker = c
        .x
        .mul(&pi)
        .mul(&tanh_over(&pi.mul(t)).sqrt())
        .div(&t.sqr().scal(4.0).shift(1.0).sqrt());
    let s = Cx { re: Iv::c(0.5), im: t.clone() };
    ker.mul(&amp(&s, c))
}

// Right edge, Re s = sstar = jj+1/2, so 2s+1 = m + 2it with m = 2jj+2 an even
// integer: |Gamma(m+iy)|^2 = gam1sq(y) prod_{k=1}^{m-1}(k^2+y^2), again exact.
fn f_right(t: &Iv, c: &Ctx) -> Iv {
    let pi = Iv::pi();
    let y = t.scal(2.0);
    let y2 = y.sqr();
    let m = 2 * c.jj + 2;
    let mut prod = gam1sq(&y);
    for k in 1..m {
        prod = prod.mul(&y2.shift((k * k) as f64));
    }
    let lngam = prod.ln().scal(0.5);
    let lnker = c
        .lnx
        .scal(2.0 * c.sstar)
        .add(&c.lnpi)
        .sub(&pi.mul(t).cosh().ln())
        .sub(&lngam);
    let s = Cx { re: Iv::c(c.sstar), im: t.clone() };
    lnker.exp().mul(&amp(&s, c))
}

// Horizontal edges, Im s = +-X/2, s = sigma + iX/2, so 2s+1 = a+iX with a = 2sigma+1,
// and |pi/sin(pi s)| <= pi/sinh(pi X/2) uniformly in sigma.  With u = a/X and
//     psi(u) = u - arctan u - (u/2) log(1+u^2),      psi'(u) = -(1/2)log(1+u^2) <= 0,
// Stirling gives, with no cancellation left between terms of size a log X,
//     log[ X^{2 sigma} pi / (sinh(pi X/2) |Gamma(a+iX)|) ]
//        = (1/2)log 2pi - log(1-e^{-pi X}) - (1/2)log X + X psi(u) + (1/4)log(1+u^2)
//          - Re mu(a+iX),          |Re mu| <= |mu| <= 1/(12 a)
// (Binet: |mu(z)| <= mu(Re z) <= 1/(12 Re z), the kernel of the first Binet integral
// being positive).  Integrating in u rather than sigma puts X in a single place in
// every factor, so the interval enclosure over an X-interval is tight; and psi is
// monotone, so its enclosure on a u-cell is exact up to rounding.  d sigma = (X/2) du.
fn psi_pt(x: &rug::Float) -> Iv {
    let z = Iv::of(x.clone(), x.clone());
    z.sub(&z.atan()).sub(&z.mul(&z.sqr().shift(1.0).ln()).scal(0.5))
}

fn f_horiz(uc: &Iv, c: &Ctx) -> Iv {
    let psi = Iv::of(psi_pt(&uc.hi).lo.clone(), psi_pt(&uc.lo).hi.clone());
    let q = uc.sqr().shift(1.0).ln().scal(0.25).exp();
    let a = uc.mul(&c.x);
    let mh = Iv::one().div(&a.scal(12.0)).hi.clone();
    let lnker = c.hconst.add(&c.x.mul(&psi)).add(&Iv::of(-mh.clone(), mh));
    let s = Cx { re: a.shift(-1.0).scal(0.5), im: c.xhalf.clone() };
    lnker.exp().mul(&q).mul(&amp(&s, c)).mul(&c.xhalf)
}

// ------------------------------------------------------- adaptive integrator
// Rigorous: on each cell, the integrand enclosure times the cell width brackets
// the cell's contribution, and the cells tile [a,b] exactly.
struct Cell {
    a: f64,
    b: f64,
    lo: f64,
    hi: f64,
}
impl PartialEq for Cell {
    fn eq(&self, o: &Cell) -> bool {
        (self.hi - self.lo) == (o.hi - o.lo)
    }
}
impl Eq for Cell {}
impl PartialOrd for Cell {
    fn partial_cmp(&self, o: &Cell) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Cell {
    fn cmp(&self, o: &Cell) -> std::cmp::Ordering {
        (self.hi - self.lo)
            .partial_cmp(&(o.hi - o.lo))
            .unwrap_or(std::cmp::Ordering::Equal)
    }
}

fn cell_of<F: Fn(&Iv, &Ctx) -> Iv>(f: &F, c: &Ctx, a: f64, b: f64) -> Cell {
    let v = f(&Iv::ab(a, b), c);
    let wdt = b - a;
    // f64 slack: three roundings at 2^-53 each, covered by 1e-15 outward.
    let lo = ((v.lo_f64() * wdt) * (1.0 - 1e-15)).max(0.0);
    let hi = (v.hi_f64() * wdt) * (1.0 + 1e-15);
    Cell { a, b, lo, hi }
}

fn integrate<F: Fn(&Iv, &Ctx) -> Iv>(
    f: F,
    c: &Ctx,
    a: f64,
    b: f64,
    init: usize,
    reltol: f64,
    maxcells: usize,
) -> (f64, f64, usize) {
    let mut heap: BinaryHeap<Cell> = BinaryHeap::with_capacity(maxcells + 8);
    for i in 0..init {
        let x0 = a + (b - a) * (i as f64) / (init as f64);
        let x1 = if i + 1 == init { b } else { a + (b - a) * ((i + 1) as f64) / (init as f64) };
        heap.push(cell_of(&f, c, x0, x1));
    }
    // The running sums are a heuristic only: rebuilt from scratch whenever the
    // heap doubles (an incremental f64 sum loses all its digits when the initial
    // enclosure is many orders of magnitude above the converged one), and the
    // returned totals are re-accumulated in MPFR with directed rounding.
    let (mut lo, mut hi) = totals_f64(&heap);
    let mut next_rebuild = 2 * heap.len();
    // The enclosure width has an irreducible floor (the Binet remainder bound
    // |mu| <= 1/(12a) is one-sided slack, and over a box the parameter interval
    // itself contributes), so refine until the UPPER bound stops improving.
    let mut hi_ref = f64::INFINITY;
    while hi - lo > reltol * hi && heap.len() < maxcells {
        let cl = match heap.pop() {
            Some(x) => x,
            None => break,
        };
        let mid = 0.5 * (cl.a + cl.b);
        if !(mid > cl.a && mid < cl.b) {
            heap.push(cl);
            break;
        }
        lo -= cl.lo;
        hi -= cl.hi;
        for (p, q) in [(cl.a, mid), (mid, cl.b)] {
            let nc = cell_of(&f, c, p, q);
            lo += nc.lo;
            hi += nc.hi;
            heap.push(nc);
        }
        if heap.len() >= next_rebuild {
            let t = totals_f64(&heap);
            lo = t.0;
            hi = t.1;
            if hi_ref - hi < 0.25 * reltol * hi {
                break;
            }
            hi_ref = hi;
            next_rebuild = 2 * heap.len();
        }
    }
    let n = heap.len();
    let (lo, hi) = totals_mpfr(&heap);
    (lo, hi, n)
}

fn totals_f64(heap: &BinaryHeap<Cell>) -> (f64, f64) {
    let mut lo = 0.0f64;
    let mut hi = 0.0f64;
    for c in heap.iter() {
        lo += c.lo;
        hi += c.hi;
    }
    (lo, hi)
}

/// Rigorous re-accumulation: MPFR, rounding down for the lower total and up for
/// the upper one, so no f64 summation error can eat into the enclosure.
fn totals_mpfr(heap: &BinaryHeap<Cell>) -> (f64, f64) {
    let mut lo = iv::fl(0.0);
    let mut hi = iv::fl(0.0);
    for c in heap.iter() {
        lo.add_assign_round(&iv::fl(c.lo), Round::Down);
        hi.add_assign_round(&iv::fl(c.hi), Round::Up);
    }
    (lo.to_f64_round(Round::Down), hi.to_f64_round(Round::Up))
}

// ------------------------------------------------------------------- tail
// sum_{n > sstar} X^{2n}/(2n)! with 0 <= g_n <= 1; n0 = floor(sstar)+1 = jj+1.
fn tail(c: &Ctx) -> f64 {
    let n0 = c.jj + 1;
    let two_n0 = (2 * n0) as f64;
    let lnt = c.lnx.scal(two_n0).sub(&Iv::c(two_n0 + 1.0).ln_gamma_incr());
    let t0 = lnt.exp();
    let r = c.x.sqr().div(&Iv::c((two_n0 + 1.0) * (two_n0 + 2.0)));
    assert!(r.hi < 0.9, "tail ratio not contractive");
    t0.div(&Iv::one().sub(&r)).hi_f64()
}

// ----------------------------------------------------------- box evaluation
struct BoxOut {
    total: f64,  // upper bound of the majorant over the whole box
    target: f64, // lower bound of 0.17 tau^{1/4} over the box
    l: f64,
    r: f64,
    h: f64,
    tl: f64,
    cells: usize,
}

fn eval_box(wlo: f64, whi: f64, xlo: f64, xhi: f64, jj: i64, reltol: f64, maxcells: usize) -> BoxOut {
    let c = Ctx::new(wlo, whi, xlo, xhi, jj);
    let tmax = xhi * 0.5;
    let (_, lh, n1) = integrate(f_left, &c, 0.0, tmax, 16, reltol, maxcells);
    let (_, rh, n2) = integrate(f_right, &c, 0.0, tmax, 8, 0.5, 64);
    let ulo = 2.0 / xhi;
    let uhi = (2.0 * c.sstar + 1.0) / xlo;
    let (hlo, hh, n3) = integrate(f_horiz, &c, ulo, uhi, 32, reltol, maxcells);
    if std::env::var("T2DBG").is_ok() {
        eprintln!("dbg horiz: lo={:.6e} hi={:.6e} cells={}  left cells={} ", hlo, hh, n3, n1);
    }
    let tl = tail(&c);
    let pil = Iv::pi().lo_f64();
    let total = ((lh + rh + hh) / pil) * (1.0 + 1e-14) + tl;
    let taumin = Iv::c(2.0).div(&Iv::c(whi).sqr());
    let q = taumin.ln().scal(0.25).exp().scal(target_c());
    BoxOut { total, target: q.lo_f64(), l: lh, r: rh, h: hh, tl, cells: n1 + n2 + n3 }
}

fn block_of(w: f64) -> i64 {
    // sstar = jj + 1/2 is the largest half-odd-integer < 2w, so w in ((2jj+1)/4, (2jj+3)/4].
    let mut jj = (2.0 * w - 0.5).floor() as i64;
    while (jj as f64) + 0.5 >= 2.0 * w {
        jj -= 1;
    }
    jj
}

// ------------------------------------------------------------------- modes
fn mode_point(w: f64, reltol: f64) {
    let jj = block_of(w);
    let o = eval_box(w, w, w, w, jj, reltol, 400000);
    let tau = 2.0 / (w * w);
    let pi = std::f64::consts::PI;
    println!(
        "w={:.6} tau={:.8} sstar={:.1}  H/pi={:.6e} L/pi={:.6e} R/pi={:.6e} tail={:.3e}",
        w, tau, jj as f64 + 0.5, o.h / pi, o.l / pi, o.r / pi, o.tl
    );
    println!(
        "  bound <= {:.9}   ratio |T2|/tau^(1/4) <= {:.7}   target {:.9}   cells {}",
        o.total,
        o.total / tau.powf(0.25),
        o.target,
        o.cells
    );
}

struct Job {
    wlo: f64,
    whi: f64,
    xlo: f64,
    xhi: f64,
    jj: i64,
}

fn mode_scan(wmax: f64, nthreads: usize) {
    let j0 = block_of(10.0);
    let j1 = block_of(wmax);
    let mut jobs: Vec<Job> = Vec::new();
    for jj in j0..=j1 {
        let wa = (((2 * jj + 1) as f64) / 4.0).max(10.0);
        let wb = (((2 * jj + 3) as f64) / 4.0).min(wmax);
        if wb <= wa {
            continue;
        }
        // X ranges over [W(tau), w(tau)] = [w e^{-tau/2}, w]; over the block,
        // X >= wa exp(-1/wa^2) and X <= wb.
        let xa = wa * (-1.0 / (wa * wa)).exp();
        jobs.push(Job { wlo: wa, whi: wb, xlo: xa, xhi: wb, jj });
    }
    println!(
        "blocks {}  w in [10,{}]  threads {}  prec {}  target {} tau^(1/4)",
        jobs.len(),
        wmax,
        nthreads,
        prec(),
        target_c()
    );

    let next = AtomicUsize::new(0);
    let worst: Mutex<(f64, f64, f64, f64)> = Mutex::new((0.0, 0.0, 0.0, 0.0));
    let failed: Mutex<Vec<(f64, f64, f64, f64, f64, f64)>> = Mutex::new(Vec::new());
    let boxes = AtomicUsize::new(0);
    let cells = AtomicUsize::new(0);
    let jobs = &jobs;

    std::thread::scope(|sc| {
        for _ in 0..nthreads {
            sc.spawn(|| loop {
                let i = next.fetch_add(1, AOrd::SeqCst);
                if i >= jobs.len() {
                    break;
                }
                let j = &jobs[i];
                let dbg = std::env::var("T2DBG").is_ok();
                let mut stack: Vec<(f64, f64, f64, f64, u32)> = vec![(j.wlo, j.whi, j.xlo, j.xhi, 0)];
                let mut lworst = (0.0f64, 0.0f64, 0.0f64, 0.0f64);
                while let Some((wa, wb, xa, xb, depth)) = stack.pop() {
                    // Clip to the admissible region tau X^2 in [2e^{-tau}, 2], i.e.
                    // W(tau) = w e^{-tau/2} <= X <= w, tau = 2/w^2.  Without this the
                    // branch and bound wastes its depth on (tau, X) pairs the lemma
                    // does not quantify over, where the bound genuinely is larger.
                    let xa = xa.max(wa * (-1.0 / (wa * wa)).exp());
                    let xb = xb.min(wb);
                    if xa > xb {
                        continue;
                    }
                    let mut o = eval_box(wa, wb, xa, xb, j.jj, 5e-2, 2500);
                    if o.total > o.target && o.total <= 1.4 * o.target {
                        o = eval_box(wa, wb, xa, xb, j.jj, 5e-3, 60000);
                    }
                    if dbg {
                        eprintln!(
                            "  j={} d={} w[{:.6},{:.6}] X[{:.6},{:.6}] tot {:.6e} tgt {:.6e} r {:.3} cells {}",
                            j.jj, depth, wa, wb, xa, xb, o.total, o.target, o.total / o.target, o.cells
                        );
                    }
                    boxes.fetch_add(1, AOrd::Relaxed);
                    cells.fetch_add(o.cells, AOrd::Relaxed);
                    if o.total <= o.target {
                        // Only ACCEPTED leaf boxes enter the reported supremum: a box
                        // that is about to be subdivided is not part of the cover, and
                        // mixing the two would report a number from a different regime
                        // than the one the verdict tests.
                        let ratio = o.total / (2.0f64 / (wb * wb)).powf(0.25);
                        if ratio > lworst.0 {
                            lworst = (ratio, wa, wb, xb);
                        }
                        continue;
                    }
                    if depth >= 26 {
                        failed.lock().unwrap().push((wa, wb, xa, xb, o.total, o.target));
                        continue;
                    }
                    if (wb - wa) / wa >= (xb - xa) / xa {
                        let m = 0.5 * (wa + wb);
                        stack.push((wa, m, xa, xb, depth + 1));
                        stack.push((m, wb, xa, xb, depth + 1));
                    } else {
                        let m = 0.5 * (xa + xb);
                        stack.push((wa, wb, xa, m, depth + 1));
                        stack.push((wa, wb, m, xb, depth + 1));
                    }
                }
                let mut g = worst.lock().unwrap();
                if lworst.0 > g.0 {
                    *g = lworst;
                }
            });
        }
    });

    let g = *worst.lock().unwrap();
    let f = failed.lock().unwrap();
    println!(
        "boxes {}  cells {}  worst enclosed ratio |T2|/tau^(1/4) <= {:.6}  at w in [{:.6},{:.6}], X <= {:.6}",
        boxes.load(AOrd::SeqCst),
        cells.load(AOrd::SeqCst),
        g.0,
        g.1,
        g.2,
        g.3
    );
    if f.is_empty() {
        println!("VERDICT: PASS -- |T2| <= {} tau^(1/4) on every box; 0 uncovered boxes", target_c());
    } else {
        println!("VERDICT: FAIL -- {} uncovered boxes:", f.len());
        for (wa, wb, xa, xb, t, q) in f.iter().take(30) {
            println!(
                "   w [{:.9},{:.9}] X [{:.9},{:.9}]  bound {:.9} > target {:.9}",
                wa, wb, xa, xb, t, q
            );
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: t2abs_iv point <w> [prec] | t2abs_iv scan <wmax> [prec] [threads]");
        std::process::exit(2);
    }
    set_prec(args.get(3).and_then(|s| s.parse().ok()).unwrap_or(96));
    let tc: f64 = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(0.17);
    TARGET_C_CELL.store(tc.to_bits(), AOrd::SeqCst);
    match args[1].as_str() {
        "point" => mode_point(
            args[2].parse().unwrap(),
            args.get(4).and_then(|s| s.parse().ok()).unwrap_or(1e-4),
        ),
        "scan" => mode_scan(
            args[2].parse().unwrap(),
            args.get(4).and_then(|s| s.parse().ok()).unwrap_or(6),
        ),
        _ => {
            eprintln!("unknown mode");
            std::process::exit(2);
        }
    }
}
