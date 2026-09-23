// Room 35: certified interval enclosure of rho_1, rho_2 at the poles q_m.
// Interval arithmetic: hand-rolled [lo,hi] over MPFR (rug) with directed rounding.
// Usage: r35cert <poles_json> <prec_bits> <digits_D> m1 m2 ...
use rug::float::Round;
use rug::Float;
use std::sync::atomic::{AtomicU32, Ordering};

static PREC: AtomicU32 = AtomicU32::new(512);
fn pr() -> u32 { PREC.load(Ordering::Relaxed) }
const MEM_CAP: f64 = 2.8e9; // bytes; hard guard (< 3GB)

#[derive(Clone, Debug)]
struct I { lo: Float, hi: Float }

fn dn<T>(e: T) -> Float where Float: rug::ops::AssignRound<T, Round = Round, Ordering = std::cmp::Ordering> { Float::with_val_round(pr(), e, Round::Down).0 }
fn up<T>(e: T) -> Float where Float: rug::ops::AssignRound<T, Round = Round, Ordering = std::cmp::Ordering> { Float::with_val_round(pr(), e, Round::Up).0 }
fn fmin(a: Float, b: Float) -> Float { if a < b { a } else { b } }
fn fmax(a: Float, b: Float) -> Float { if a > b { a } else { b } }

const SP: u32 = 256;
impl I {
    fn shrink(&self) -> I { I { lo: Float::with_val_round(SP, &self.lo, Round::Down).0, hi: Float::with_val_round(SP, &self.hi, Round::Up).0 } }
    fn pt(x: &Float) -> I { I { lo: dn(x), hi: up(x) } }
    fn n(v: i64) -> I { I { lo: dn(v), hi: up(v) } }
    fn s(st: &str) -> I {
        let p = Float::parse(st).expect("parse");
        let lo = Float::with_val_round(pr(), Float::parse(st).unwrap(), Round::Down).0;
        let hi = Float::with_val_round(pr(), p, Round::Up).0;
        I { lo, hi }
    }
    fn add(&self, o: &I) -> I { I { lo: dn(&self.lo + &o.lo), hi: up(&self.hi + &o.hi) } }
    fn sub(&self, o: &I) -> I { I { lo: dn(&self.lo - &o.hi), hi: up(&self.hi - &o.lo) } }
    fn neg(&self) -> I { I { lo: Float::with_val(pr(), -&self.hi), hi: Float::with_val(pr(), -&self.lo) } }
    fn mul(&self, o: &I) -> I {
        let c = [(&self.lo, &o.lo), (&self.lo, &o.hi), (&self.hi, &o.lo), (&self.hi, &o.hi)];
        let mut lo = dn(c[0].0 * c[0].1); let mut hi = up(c[0].0 * c[0].1);
        for (a, b) in c.iter().skip(1) { lo = fmin(lo, dn(*a * *b)); hi = fmax(hi, up(*a * *b)); }
        I { lo, hi }
    }
    fn div(&self, o: &I) -> I {
        assert!(o.lo > 0 || o.hi < 0, "division by interval containing 0");
        let c = [(&self.lo, &o.lo), (&self.lo, &o.hi), (&self.hi, &o.lo), (&self.hi, &o.hi)];
        let mut lo = dn(c[0].0 / c[0].1); let mut hi = up(c[0].0 / c[0].1);
        for (a, b) in c.iter().skip(1) { lo = fmin(lo, dn(*a / *b)); hi = fmax(hi, up(*a / *b)); }
        I { lo, hi }
    }
    fn sqrt(&self) -> I { assert!(self.lo >= 0); I { lo: dn(self.lo.sqrt_ref()), hi: up(self.hi.sqrt_ref()) } }
    fn exp(&self) -> I { I { lo: dn(self.lo.exp_ref()), hi: up(self.hi.exp_ref()) } }
    /// [0? , max|x|] as a point upper bound interval (nonneg)
    fn mag(&self) -> I {
        let a = Float::with_val(pr(), self.lo.abs_ref()); let b = Float::with_val(pr(), self.hi.abs_ref());
        let m = fmax(a, b); I { lo: m.clone(), hi: m }
    }
    fn widen(&self, d: &I) -> I { I { lo: dn(&self.lo - &d.hi), hi: up(&self.hi + &d.hi) } }
    fn sign(&self) -> i32 { if self.lo > 0 { 1 } else if self.hi < 0 { -1 } else { 0 } }
    fn maxu(&self, o: &I) -> I { let m = fmax(self.hi.clone(), o.hi.clone()); I { lo: m.clone(), hi: m } }
    fn mid(&self) -> Float { Float::with_val(pr(), &self.lo + &self.hi) / 2u32 }
    fn wid(&self) -> f64 { Float::with_val(pr(), &self.hi - &self.lo).to_f64() }
    fn f(&self) -> f64 { self.mid().to_f64() }
    fn pow(&self, k: u64) -> I { // k>=0, self>0
        let mut r = I::n(1); let mut b = self.clone(); let mut e = k;
        while e > 0 { if e & 1 == 1 { r = r.mul(&b); } b = b.mul(&b); e >>= 1; }
        r
    }
}

fn rss_bytes() -> f64 {
    unsafe {
        let mut u: libc::rusage = std::mem::zeroed();
        libc::getrusage(libc::RUSAGE_SELF, &mut u);
        u.ru_maxrss as f64 // bytes on macOS
    }
}
fn guard(tag: &str) {
    let r = rss_bytes();
    if r > MEM_CAP { eprintln!("MEMORY GUARD TRIPPED at {}: rss={:.2e}", tag, r); std::process::exit(3); }
}

/// B(q) = F(1,q) = sum_k (-2(1-q))^k q^{k^2}/(q;q)_{2k}, rigorous tail.

// ================= Room 39: certified zero count of B(q) on [lo,hi] =================
// B(q)=sum_k (-2(1-q))^k q^{k^2}/(q;q)_{2k}.  Per cell [m-h,m+h]:
//  B(m+u) = P(u) + E(u), P = degree-n Taylor poly of B_K (first K+1 terms) computed in interval
//  Taylor arithmetic at the exact point m;  |E| <= Rn + MT on the cell, |E'| <= Rn' + MT/(R-h), where
//  Rn, Rn' are Cauchy remainders with M_K = sup_{|z-m|<=R} |B_K(z)| <= sum_{k<=K} a_k (majorant),
//  MT >= sup_disc |sum_{k>K} t_k| via majorant tail; a_k = (2e)^k Z^{k^2}/prod_{j<=2k}(1-Z^j),
//  e = 1-m+R >= |1-z|, Z = m+R >= |z|, |1-z^j| >= 1-Z^j.
type Ser = Vec<I>;
fn smul(a: &Ser, b: &Ser, n: usize) -> Ser {
    let mut r: Ser = vec![I::n(0); n + 1];
    for i in 0..=n { if i >= a.len() { break; } for j in 0..=(n - i) { if j >= b.len() { break; } r[i + j] = r[i + j].add(&a[i].mul(&b[j])); } }
    r
}
fn sdiv(a: &Ser, d: &Ser, n: usize) -> Ser {
    let mut r: Ser = Vec::with_capacity(n + 1);
    for i in 0..=n {
        let mut s = if i < a.len() { a[i].clone() } else { I::n(0) };
        for j in 1..=i { if j < d.len() { s = s.sub(&d[j].mul(&r[i - j])); } }
        r.push(s.div(&d[0]));
    }
    r
}
fn one_minus(a: &Ser) -> Ser { let mut r: Ser = a.iter().map(|x| x.neg()).collect(); r[0] = I::n(1).add(&r[0]); r }

struct Cell { c: Ser, e0: I, e1: I }

fn tail_tiny() -> I { I::pt(&Float::with_val(pr(), Float::i_exp(1, -150))) }

fn cell_series(m: &Float, h: &Float, n: usize) -> Cell {
    let one = I::n(1); let two = I::n(2);
    let mi = I::pt(m); let hi_ = I::pt(h);
    let r = one.sub(&mi).div(&I::n(3)); // R = (1-m)/3 (interval; use lo for safety below)
    let rr = I { lo: r.lo.clone(), hi: r.lo.clone() }; // R exact-ish point = lower value, still valid radius
    assert!(hi_.hi < rr.lo, "h must be < R");
    // majorant
    let z = mi.add(&rr); let e = one.sub(&mi).add(&rr);
    assert!(z.hi < 1);
    let mut a = one.clone(); let mut mk = one.clone(); let mut zo = z.clone(); // Z^{2k-1}
    let z2 = z.mul(&z);
    // series
    let q: Ser = vec![mi.clone(), one.clone()];
    let q2 = smul(&q, &q, 2);
    let cser: Ser = vec![two.mul(&one.sub(&mi)).neg(), two.clone()]; // -2(1-q)
    let mut t: Ser = vec![I::n(0); n + 1]; t[0] = one.clone();
    let mut b: Ser = t.clone();
    let mut qo: Ser = q.clone(); qo.resize(n + 1, I::n(0));
    let mut k = 0usize;
    let mt;
    loop {
        k += 1;
        // series term k
        let qe = smul(&qo, &q, n);
        let num = smul(&smul(&t, &cser, n), &qo, n);
        let den = smul(&one_minus(&qo), &one_minus(&qe), n);
        t = sdiv(&num, &den, n);
        for i in 0..=n { b[i] = b[i].add(&t[i]); }
        // majorant term k
        let ze = zo.mul(&z);
        a = a.mul(&two).mul(&e).mul(&zo).div(&one.sub(&zo).mul(&one.sub(&ze)));
        mk = mk.add(&a);
        let zo2 = zo.mul(&z2); let ze2 = zo2.mul(&z);
        let rho = two.mul(&e).mul(&zo2).div(&one.sub(&zo2).mul(&one.sub(&ze2)));
        if rho.hi < 0.5 && k > 5 {
            let tb = a.mag().mul(&rho.maxu(&rho)).div(&one.sub(&rho.maxu(&rho)));
            if tb.hi < tail_tiny().lo { mt = tb; break; }
        }
        zo = zo2; qo = smul(&qo, &q2, n);
        if k > 100000 { panic!("no convergence"); }
    }
    let hr = hi_.div(&rr); let omhr = one.sub(&hr);
    let rn = mk.mag().mul(&hr.pow(n as u64 + 1)).div(&omhr);
    let rn1 = mk.mag().div(&rr).mul(&I::n(n as i64 + 1)).mul(&hr.pow(n as u64)).div(&omhr.mul(&omhr));
    let e0 = rn.add(&mt); let e1 = rn1.add(&mt.div(&rr.sub(&hi_)));
    Cell { c: b, e0: e0.maxu(&e0), e1: e1.maxu(&e1) }
}
fn pm(x: &I) -> I { I { lo: Float::with_val(pr(), -&x.hi), hi: x.hi.clone() } }
// enclosure of P(u) for u in [-h,h] (+E), P'(u) (+E'), and P(s*h) point (+E)
fn encl(c: &Cell, h: &Float) -> (I, I, I, I) {
    let hi_ = I::pt(h); let n = c.c.len() - 1;
    let mut s0 = I::n(0); let mut s1 = I::n(0); let mut hp = I::n(1);
    for j in 1..=n { s0 = s0.add(&c.c[j].mag().mul(&hp.mul(&hi_))); if j >= 2 { s1 = s1.add(&c.c[j].mag().mul(&I::n(j as i64)).mul(&hp)); } hp = hp.mul(&hi_); }
    let f = c.c[0].add(&pm(&s0)).add(&pm(&c.e0));
    let d = c.c[1].add(&pm(&s1)).add(&pm(&c.e1));
    let mut pl = I::n(0); let mut pr_ = I::n(0);
    let nh = hi_.neg();
    for j in (0..=n).rev() { pl = pl.mul(&nh).add(&c.c[j]); pr_ = pr_.mul(&hi_).add(&c.c[j]); }
    (f, d, pl.add(&pm(&c.e0)), pr_.add(&pm(&c.e0)))
}
struct St { cells: usize, excl: usize, mono: usize, roots: Vec<(Float, Float)>, n: usize, maxdepth: usize }
fn cert(a: &Float, b: &Float, depth: usize, st: &mut St) {
    guard("cert");
    let m = Float::with_val(pr(), a + b) / 2u32; let h = Float::with_val(pr(), b - a) / 2u32;
    let m = Float::with_val(pr(), m); let h = Float::with_val(pr(), h);
    assert!(Float::with_val(pr(), &m - &h) == *a && Float::with_val(pr(), &m + &h) == *b, "cell not exactly [a,b]");
    st.cells += 1; if depth > st.maxdepth { st.maxdepth = depth; }
    let c = cell_series(&m, &h, st.n);
    let (f, d, fl, fr) = encl(&c, &h);
    if f.sign() != 0 { st.excl += 1; return; }
    if d.sign() != 0 {
        let (sl, sr) = (fl.sign(), fr.sign());
        if sl != 0 && sr != 0 { st.mono += 1; if sl != sr { st.roots.push((a.clone(), b.clone())); } return; }
    }
    if depth > 200 { eprintln!("FAIL at {} {}", a, b); std::process::exit(4); }
    cert(a, &m, depth + 1, st); cert(&m, b, depth + 1, st);
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    PREC.store(args[3].parse().unwrap(), Ordering::Relaxed);
    // Reviewer-F fix: snap endpoints to f64 dyadics so all midpoints are exact at pr() bits.
    let lo = Float::with_val(pr(), args[1].parse::<f64>().unwrap());
    let hi = Float::with_val(pr(), args[2].parse::<f64>().unwrap());
    let n: usize = args[4].parse().unwrap(); let div: f64 = args[5].parse().unwrap();
    let t0 = std::time::Instant::now();
    let mut st = St { cells: 0, excl: 0, mono: 0, roots: vec![], n, maxdepth: 0 };
    let mut a = lo.clone(); let mut top = 0;
    while a < hi {
        // initial width: (1-a)/div rounded down to a power of 2
        let w = (1.0 - a.to_f64()) / div; let e = w.log2().floor() as i32;
        let wf = Float::with_val(pr(), Float::i_exp(1, e));
        let mut b = Float::with_val(pr(), &a + &wf); if b > hi { b = hi.clone(); }
        cert(&a, &b, 0, &mut st); top += 1; a = b;
    }
    println!("interval [{}, {}] prec={} n={} top-cells={} cells={} excluded={} monotone={} maxdepth={} time={:.1}s rss={:.2e}",
        args[1], args[2], pr(), n, top, st.cells, st.excl, st.mono, st.maxdepth, t0.elapsed().as_secs_f64(), rss_bytes());
    println!("ROOTS: {}", st.roots.len());
    for (a, b) in &st.roots { println!("  root in [{:.25}, {:.25}] width {:.2e}", a.to_f64(), b.to_f64(), Float::with_val(pr(), b - a).to_f64()); }
}
