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
/// Tail: ratio r_k = 2(1-q) q^{2k-1}/((1-q^{2k-1})(1-q^{2k})) is decreasing in k,
/// so sum_{j>k}|t_j| <= |t_k| rho/(1-rho), rho = r_{k+1}.
fn bfun(q: &I) -> I {
    let one = I::n(1); let two = I::n(2);
    let omq = one.sub(q); let c = two.mul(&omq).neg();
    let q2 = q.mul(q);
    let mut t = one.clone(); let mut s = one.clone();
    let mut qo = q.clone(); // q^{2k-1}
    let tiny = I::pt(&Float::with_val(pr(), Float::i_exp(1, -(pr() as i32) - 20)));
    let half = I::s("0.5");
    loop {
        let qe = qo.mul(q);
        t = t.mul(&c).mul(&qo).div(&one.sub(&qo).mul(&one.sub(&qe)));
        s = s.add(&t);
        let qo2 = qo.mul(&q2); let qe2 = qo2.mul(q);
        let rho = two.mul(&omq).mul(&qo2).div(&one.sub(&qo2).mul(&one.sub(&qe2)));
        if rho.hi < half.lo && t.mag().hi < tiny.lo {
            let tail = t.mag().mul(&rho.maxu(&rho)).div(&one.sub(&rho.maxu(&rho)));
            return s.widen(&tail);
        }
        qo = qo2;
    }
}

fn certify_pole(qstr: &str) -> I {
    let val = |x: &Float| -> Float { bfun(&I::pt(x)).mid() };
    let mut x0 = Float::with_val(pr(), Float::parse(qstr).unwrap());
    let mut x1 = Float::with_val(pr(), &x0 * Float::with_val(pr(), Float::parse("1.0000000000000000000000000000001").unwrap()));
    let mut f0 = val(&x0); let mut f1 = val(&x1);
    let tol = Float::with_val(pr(), Float::i_exp(1, -(pr() as i32) + 40));
    for _ in 0..200 {
        if f1 == f0 { break; }
        let x2 = Float::with_val(pr(), &x1 - Float::with_val(pr(), &f1 * Float::with_val(pr(), &x1 - &x0)) / Float::with_val(pr(), &f1 - &f0));
        let d = Float::with_val(pr(), &x2 - &x1).abs();
        x0 = x1; f0 = f1; x1 = x2; f1 = val(&x1);
        if d < tol { break; }
    }
    for g in [48i32, 96, 160, 256, 400, 640, 1000] {
        let dl = Float::with_val(pr(), Float::i_exp(1, -(pr() as i32) + g));
        let lo = Float::with_val_round(pr(), &x1 - &dl, Round::Down).0; let hi = Float::with_val_round(pr(), &x1 + &dl, Round::Up).0;
        let sl = bfun(&I::pt(&lo)).sign(); let sh = bfun(&I::pt(&hi)).sign();
        if sl != 0 && sh != 0 && sl != sh { return I { lo, hi }; }
    }
    panic!("could not certify sign change");
}

struct Res { r1: I, r2: I, n: usize, prods: Vec<I> }

/// y: 0 => y=1, 1 => y=q
fn pipeline(q: &I, ycase: u8, n: usize) -> Res {
    let k = n + 2;
    let per = 2.0 * (SP as f64 / 8.0 + 48.0);
    let est = 7.0 * k as f64 * per + 5e7;
    if est > MEM_CAP { eprintln!("MEMORY GUARD: estimated {:.2e} bytes > cap; abort", est); std::process::exit(3); }
    let one = I::n(1); let two = I::n(2); let four = I::n(4);
    let omq = one.sub(q); let q2 = q.mul(q); let omq2 = one.sub(&q2);
    let x = q.sqrt();
    // ---------- travel ----------
    let mut rv: Vec<I> = Vec::with_capacity(k); let mut lv: Vec<I> = Vec::with_capacity(k);
    let mut a = I::n(0); let mut b = I::n(1); let mut qs = I::n(1);
    for _s in 0..k {
        let l = qs.mul(&a).add(&b);
        let r = two.mul(q).mul(&qs).mul(&l);
        a = a.add(&r); b = b.sub(&qs.mul(&r));
        rv.push(r.shrink()); lv.push(l.shrink()); qs = qs.mul(q);
    }
    guard("travel");
    let qk = qs.clone(); // q^K
    let xk = a.mag().add(&b.mag());
    let e_t = four.mul(&qk).mul(q).div(&omq).exp();
    let aa = e_t.mul(&xk);
    let c_rt = two.mul(&aa).mul(q);
    let beta = b.mag().add(&two.mul(&aa).mul(&qk.mul(&qk).mul(q)).div(&omq2));
    // ---------- bulk ----------
    let g = if ycase == 0 { q.div(&omq) } else { q.div(&omq2) };
    let kb = k; // P_b for b=1..=kb, Pt_s = P_{s+1}, s=0..k-1
    let run = |bet: &I, store: bool| -> (I, I, I, Vec<I>) {
        let mut a = I::n(0); let mut b = bet.clone(); let mut qb = I::n(1);
        let gb = g.mul(bet);
        let mut out = Vec::new(); if store { out.reserve(kb); }
        for _ in 1..=kb {
            qb = qb.mul(q);
            let p = two.mul(&qb).mul(&one.add(&qb.mul(&a)).add(&b).add(&qb.mul(&gb)));
            a = a.add(&p); b = b.sub(&qb.mul(&p));
            if store { out.push(p.shrink()); }
        }
        // tail: Z = |A|+|B|+1+|g beta|; |p_b| <= 2 Eb Z q^b (b>kb)
        let z = a.mag().add(&b.mag()).add(&one).add(&gb.mag());
        let eb = four.mul(&qb).mul(q).div(&omq).exp();
        let db = two.mul(&eb).mul(&z).mul(&qb.mul(&qb).mul(&q2)).div(&omq2);
        let binf = b.widen(&db);
        (binf, eb, z, out)
    };
    let (b0, _, _, _) = run(&I::n(0), false);
    let (b1, _, _, _) = run(&I::n(1), false);
    let t = b0.neg().div(&b1.sub(&b0));
    let (_bt, eb, zc, pt) = run(&t, true);
    guard("bulk");
    let c_pt = two.mul(&eb).mul(&zc).mul(q);
    // ---------- suffix sums for M ----------
    let tl = aa.mul(&qk.mul(&qk)).div(&omq2).add(&beta.mul(&qk).div(&omq)); // |sum_{t>=K} q^t L_t|
    let mut suf: Vec<I> = vec![I::n(0); k + 1];
    suf[k] = I::n(0).widen(&tl);
    let mut qpows: Vec<I> = Vec::with_capacity(k);
    { let mut qq = I::n(1); for _ in 0..k { qpows.push(qq.shrink()); qq = qq.mul(q); } }
    for s in (0..k).rev() { suf[s] = suf[s + 1].add(&qpows[s].mul(&lv[s])).shrink(); }
    let mut mv: Vec<I> = Vec::with_capacity(k);
    let mut pre = I::n(0);
    for s in 0..k { pre = pre.add(&lv[s]); mv.push(qpows[s].mul(&pre).add(&suf[s + 1]).shrink()); }
    drop(suf);
    guard("M");
    let sfull = pre.mag();
    let km = sfull.add(&aa.add(&beta).div(&omq)).add(&tl);
    // ---------- bounds valid for s >= S0 = K-1 ----------
    let s0 = k - 1; let qq0 = qpows[s0].clone();
    let a2 = aa.maxu(&lv[s0].mag().div(&qq0));
    let cr2 = c_rt.maxu(&rv[s0].mag().div(&qq0));
    let cp2 = c_pt.maxu(&pt[s0].mag().div(&qq0));
    let km2 = km.maxu(&mv[s0].mag());
    let base = a2.mul(&qq0.mul(&qq0)).div(&omq2).add(&beta.mul(&qq0).div(&omq));
    let t_lr = cr2.mul(&base); let t_lp = cp2.mul(&base);
    let t_rw2 = two.mul(&km2).mul(&cr2).mul(&qq0).div(&omq);
    let t_pw2 = two.mul(&km2).mul(&cp2).mul(&qq0).div(&omq);
    // ---------- inner products over s = 0..=K-2 ----------
    let z = I::n(0);
    let (mut lr, mut lp, mut rw1, mut pw1, mut rw2, mut pw2) = (z.clone(), z.clone(), z.clone(), z.clone(), z.clone(), z.clone());
    let (mut ra, mut pa, mut rd, mut pd) = (z.clone(), z.clone(), z.clone(), z.clone());
    for s in 0..s0 {
        let w1 = lv[s + 1].add(&x.mul(&lv[s]));
        let w2 = mv[s].add(&mv[s + 1]);
        lr = lr.add(&lv[s].mul(&rv[s])); lp = lp.add(&lv[s].mul(&pt[s]));
        rw1 = rw1.add(&rv[s].mul(&w1)); pw1 = pw1.add(&pt[s].mul(&w1));
        rw2 = rw2.add(&rv[s].mul(&w2)); pw2 = pw2.add(&pt[s].mul(&w2));
        // room 43: w_A = L_{s+1} + q L_s (A = <E,R> = <P~,w_A>), w_D = M_{s+1} + q M_s (D = <L,E> = <P~,w_D>)
        let wa = lv[s + 1].add(&q.mul(&lv[s]));
        let wd = mv[s + 1].add(&q.mul(&mv[s]));
        ra = ra.add(&rv[s].mul(&wa)); pa = pa.add(&pt[s].mul(&wa));
        rd = rd.add(&rv[s].mul(&wd)); pd = pd.add(&pt[s].mul(&wd));
    }
    // tails: |w_A| obeys the same bound as |w_1| (q <= x <= 1), |w_D| the same as |w_2| (q <= 1)
    let ra = ra.widen(&two.mul(&t_lr)); let pa = pa.widen(&two.mul(&t_lp));
    let rd = rd.widen(&t_rw2); let pd = pd.widen(&t_pw2);
    let lr = lr.widen(&t_lr); let lp = lp.widen(&t_lp);
    let rw1 = rw1.widen(&two.mul(&t_lr)); let pw1 = pw1.widen(&two.mul(&t_lp));
    let rw2 = rw2.widen(&t_rw2); let pw2 = pw2.widen(&t_pw2);
    let r1 = pw1.mul(&lr).div(&lp.mul(&rw1)).sub(&one);
    let r2 = pw2.mul(&lr).div(&lp.mul(&rw2)).sub(&one);
    let ra_ = pa.mul(&lr).div(&lp.mul(&ra)).sub(&one);
    let rd_ = pd.mul(&lr).div(&lp.mul(&rd)).sub(&one);
    // Pi_tot = 2AB + 2CB + AD/2 with X = A+2C = (1+x)<P~,w1>, B = (x/2)<P~,w2>: Pi_tot = B(A+X) + AD/2
    let xx = one.add(&x).mul(&pw1); let bb = x.mul(&pw2).div(&two);
    let pit = bb.mul(&pa.add(&xx)).add(&pa.mul(&pd).div(&two));
    let cc = xx.sub(&pa).div(&two);
    Res { r1, r2, n, prods: vec![lr, lp, rw1, pw1, rw2, pw2, t, ra, rd, ra_, rd_, pit, pa, bb, cc, pd] }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let js = std::fs::read_to_string(&args[1]).unwrap();
    let qstrs: Vec<String> = js.split('"').enumerate().filter(|(i, _)| i % 2 == 1).map(|(_, s)| s.to_string()).collect();
    let cfac: f64 = args[2].split(',').next().unwrap().parse().unwrap();
    let extra: f64 = args[2].split(',').nth(1).unwrap().parse().unwrap();
    let d0: f64 = args[3].split(',').next().unwrap().parse().unwrap(); let d1: f64 = args[3].split(',').nth(1).unwrap_or("0").parse().unwrap();
    for m in args[4..].iter().map(|s| s.parse::<usize>().unwrap()) {
        let t0 = std::time::Instant::now();
        let qf: f64 = qstrs[m - 1][..20].parse().unwrap();
        let bits = (cfac / (1.0 - qf) + extra).ceil() as u32;
        PREC.store(bits, Ordering::Relaxed);
        println!("m={} working precision {} bits", m, bits);
        let q = certify_pole(&qstrs[m - 1]);
        let eps = 1.0 - q.f();
        let dig = d0 + d1 / eps; let n = (dig * 10f64.ln() / (-(q.f().ln()))).ceil() as usize;
        println!("m={} q_m in [{:.40}, ...] width {:.2e}  (B(q_lo),B(q_hi) opposite certified signs)  N={}", m, q.lo.to_f64(), q.wid(), n);
        let _ = eps;
        let yset: Vec<u8> = match std::env::var("YONLY").ok().as_deref() { Some("1") => vec![0], Some("q") => vec![1], _ => vec![0, 1] };
        for yc in yset {
            let r = pipeline(&q, yc, n);
            let ys = if yc == 0 { "1" } else { "q" };
            let pos1 = r.r1.lo > -1; let pos2 = r.r2.lo > -1;
            println!("  y={} rho1 in [{:.12e}, {:.12e}] w={:.2e} | rho2 in [{:.12e}, {:.12e}] w={:.2e} | 1+rho1>0:{} 1+rho2>0:{}",
                ys, r.r1.lo.to_f64(), r.r1.hi.to_f64(), r.r1.wid(), r.r2.lo.to_f64(), r.r2.hi.to_f64(), r.r2.wid(), pos1, pos2);
            println!("     rho1 mid={:.15}  rho2 mid={:.15}  <L,R>={:.6e} alpha={:.6e} N={}", r.r1.f(), r.r2.f(), r.prods[0].f(), r.prods[1].f()/r.prods[0].f(), r.n);
            let p = &r.prods;
            println!("     Q_A=<R,wA> in [{:.6e},{:.6e}] Q_D=<R,wD> in [{:.6e},{:.6e}]", p[7].lo.to_f64(), p[7].hi.to_f64(), p[8].lo.to_f64(), p[8].hi.to_f64());
            println!("     rhoA in [{:.12e},{:.12e}] rhoD in [{:.12e},{:.12e}] 1+rhoA>0:{} 1+rhoD>0:{}", p[9].lo.to_f64(), p[9].hi.to_f64(), p[10].lo.to_f64(), p[10].hi.to_f64(), p[9].lo > -1, p[10].lo > -1);
            println!("     A={:.6e} B={:.6e} C={:.6e} D={:.6e} signs {} {} {} {}", p[12].f(), p[13].f(), p[14].f(), p[15].f(), p[12].sign(), p[13].sign(), p[14].sign(), p[15].sign());
            println!("     PI_TOT in [{:.12e},{:.12e}] relw={:.1e} CERTIFIED_POSITIVE:{}", p[11].lo.to_f64(), p[11].hi.to_f64(), p[11].wid()/p[11].f().abs(), p[11].lo > 0);
            println!("     inner-product rel widths: {}", r.prods.iter().map(|p| format!("{:.1e}", p.wid()/p.f().abs())).collect::<Vec<_>>().join(" "));
        }
        println!("  time {:.1}s rss {:.2e}", t0.elapsed().as_secs_f64(), rss_bytes());
    }
}
