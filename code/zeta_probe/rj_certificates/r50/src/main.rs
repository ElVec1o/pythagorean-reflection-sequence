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

// ===== Room 50 certification =====
fn pi() -> I { use rug::float::Constant; I { lo: Float::with_val_round(pr(), Constant::Pi, Round::Down).0, hi: Float::with_val_round(pr(), Constant::Pi, Round::Up).0 } }
fn imax(a: &I, b: &I) -> I { I { lo: fmax(a.lo.clone(), b.lo.clone()), hi: fmax(a.hi.clone(), b.hi.clone()) } }
fn iv(lo: &Float, hi: &Float) -> I { I { lo: lo.clone(), hi: hi.clone() } }

/// Returns (B, eps*Gammahat) on box t in T (t=1/k), u in Uu (om = k + u/k), g fixed.
/// None if a denominator (Prufer-admissibility / None-branch) is not certified positive.
fn eval(t: &I, u: &I, g: &I) -> Option<(I, I)> {
    let one = I::n(1); let two = I::n(2); let p = pi();
    let t2 = t.mul(t);
    let om_ = one.add(&u.mul(&t2)); // Omega
    let o2 = om_.mul(&om_);
    let den = o2.add(&two.mul(&t2));
    let eps = two.mul(&t2).div(&den);
    let q = o2.div(&den);
    let ef = |x: &I| -> I { x.div(&den).add(&I::n(4).mul(&x.pow(3)).div(&I::n(70).mul(&den.mul(&den)))) };
    let xh = one.add(&p.add(&one).mul(t));
    let xl = one.sub(&p.sub(&one).mul(t));
    if xl.lo <= 0 { return None; }
    let eh = ef(&xh); let el = ef(&xl);
    let ph = one.add(&p.mul(t)).sub(&t2.mul(&eh));
    let pl = one.sub(&p.mul(t)).add(&t2.mul(&el));
    let dh = p.sub(&t.mul(&eh)).sub(&u.mul(t));
    let dl = p.add(&u.mul(t)).sub(&t.mul(&el));
    let ph2 = ph.mul(&ph); let pl2 = pl.mul(&pl);
    let denh = o2.mul(&dh).mul(&ph.add(&om_)).add(&two.mul(&ph2).mul(t));
    let denl = o2.mul(&dl).mul(&pl.add(&om_)).sub(&two.mul(&pl2).mul(t));
    if denh.lo <= 0 || denl.lo <= 0 { return None; }
    let wh = two.mul(&ph2).div(&denh);
    let wl = two.mul(&pl2).div(&denl);
    let w = imax(&wh, &wl); // wmax / t
    let sS = two.mul(&om_).div(&den); // s/t
    let s = t.mul(&sS);
    let a = s.div(&two.sub(&s));
    let uu = a.exp().div(&one.sub(&s.div(&two))).sqrt();
    let g1 = g.sub(&one);
    let one_a = one.sub(&a); if one_a.lo <= 0 { return None; }
    let qq = one.add(&q).add(&q.mul(&q));
    let qt = om_.mul(&uu).mul(&t.div(&g1.mul(&one_a.sqrt())).add(&om_.mul(g).div(&g1.mul(&qq.sqrt()))));
    let dB = one.add(&q.sqrt()).sub(&s); if dB.lo <= 0 { return None; }
    let b = sS.div(&dB).mul(&w).mul(&qt);
    let egh = two.div(&den).mul(&t.mul(&w)).mul(&qt);
    let _ = eps;
    Some((b, egh))
}

// Adaptive bisection: certify f(box) < target; returns (ok, max upper bound over leaves, leaves)
fn cert(t: I, u: I, g: &I, which: usize, target: f64, depth: u32, st: &mut (f64, u64, bool)) {
    st.1 += 1; if st.1 % 100000 == 0 { guard("cert"); }
    let r = eval(&t, &u, g);
    let hi = r.as_ref().map(|(b, e)| if which == 0 { b.hi.to_f64() } else { e.hi.to_f64() });
    match hi {
        Some(h) if h < target => { if h > st.0 { st.0 = h; } return; }
        _ => {}
    }
    if depth == 0 { st.2 = false; eprintln!("FAIL leaf t=[{:.6e},{:.6e}] u=[{:.4},{:.4}] hi={:?}", t.lo.to_f64(), t.hi.to_f64(), u.lo.to_f64(), u.hi.to_f64(), hi); if let Some(h)=hi { if h> st.0 {st.0=h;} } return; }
    // split the wider (relative) coordinate
    let tw = t.wid(); let uw = u.wid() * 1e-2;
    if tw > uw && tw > 0.0 {
        let m = t.mid(); cert(iv(&t.lo, &m), u.clone(), g, which, target, depth - 1, st); cert(iv(&m, &t.hi), u, g, which, target, depth - 1, st);
    } else {
        let m = u.mid(); cert(t.clone(), iv(&u.lo, &m), g, which, target, depth - 1, st); cert(t, iv(&m, &u.hi), g, which, target, depth - 1, st);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    PREC.store(128, Ordering::Relaxed);
    let m1: i64 = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(200);
    let g = I::s("28.4");
    let rad = I::s("1.06"); // |u| <= 1.06 k/(k-1) = 1.06/(1-t)
    let one = I::n(1);
    // sanity: point value vs python
    { let k = I::n(13).div(&I::n(2)).mul(&pi()); let t = one.div(&k); let u = I::n(0);
      let (b, e) = eval(&t, &u, &g).unwrap(); println!("check m=7 u=0: B in [{:.10},{:.10}] epsGh in [{:.10},{:.10}]", b.lo.to_f64(), b.hi.to_f64(), e.lo.to_f64(), e.hi.to_f64()); }
    for (which, name, target, m0) in [(0usize, "B (|rho_1| bound)", 0.265f64, 7i64), (1, "eps*Gammahat", 0.01548, 10)] {
        let mut worst = 0f64; let mut worst_m = 0; let mut allok = true; let mut leaves = 0u64;
        let mut table = vec![];
        for m in m0..=m1 {
            let k = I::n(2 * m - 1).div(&I::n(2)).mul(&pi());
            let t = one.div(&k);
            let r = rad.div(&one.sub(&t)); let u = iv(&r.neg().lo, &r.hi);
            let mut st = (0f64, 0u64, true);
            cert(t, u, &g, which, target, 40, &mut st);
            allok &= st.2; leaves += st.1;
            if st.0 > worst { worst = st.0; worst_m = m; }
            if m <= m0 + 5 || m % 50 == 0 { table.push((m, st.0)); }
        }
        // tail: t in [0, 1/k_{m1+1}], continuous
        let kt = I::n(2 * (m1 + 1) - 1).div(&I::n(2)).mul(&pi());
        let tt = one.div(&kt); let t = iv(&Float::with_val(pr(), 0), &tt.hi);
        let r = rad.div(&one.sub(&t)); let u = iv(&r.neg().lo, &r.hi);
        let mut st = (0f64, 0u64, true);
        cert(t, u, &g, which, target, 60, &mut st);
        println!("== {} target {}: m={}..{} certified={} max_upper={:.6} at m={} ; tail m>{} certified={} max_upper={:.6} ; boxes={}",
            name, target, m0, m1, allok, worst, worst_m, m1, st.2, st.0, leaves + st.1);
        for (m, v) in table { println!("   m={} upper={:.6}", m, v); }
    }
    guard("end");
    println!("peak rss bytes {:.3e}", rss_bytes());
}
