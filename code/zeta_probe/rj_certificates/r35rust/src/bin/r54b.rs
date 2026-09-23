// Room 35: certified interval enclosure of rho_1, rho_2 at the poles q_m.
// Interval arithmetic: hand-rolled [lo,hi] over MPFR (rug) with directed rounding.
// Usage: r35cert <poles_json> <prec_bits> <digits_D> m1 m2 ...
#![allow(dead_code)]
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


/// Room 54b: <lambda,R> = 2q(1+x)/(1-q) * (t1 + (1+x)/(2x)) / (1 - g t1), R_0 = 2q normalisation.
/// t1 = v^T (I-M0)^{-1} u, u_b = 2q^{2b}, via affine shooting in beta with rigorous tail.
fn run(q: &I, beta: &I, src: bool, k: usize) -> I {
    let one = I::n(1); let two = I::n(2); let four = I::n(4);
    let omq = one.sub(q); let q2 = q.mul(q);
    let mut a = I::n(0); let mut b = beta.clone(); let mut qb = I::n(1);
    for _ in 1..=k {
        qb = qb.mul(q);
        let s = if src { qb.clone() } else { I::n(0) };
        let p = two.mul(&qb).mul(&s.add(&qb.mul(&a)).add(&b));
        a = a.add(&p); b = b.sub(&qb.mul(&p));
    }
    // tail: b>=K+1, M_b <= M_K exp(4 q^{K+1}/(1-q)), M = 1+|A|+|B|; sum q^b|p_b| <= 2 M* q^{2K+2}/(1-q^2)
    let mk = one.add(&a.mag()).add(&b.mag());
    let qk1 = qb.mul(q);
    let ms = mk.mul(&four.mul(&qk1).div(&omq).exp());
    let db = two.mul(&ms).mul(&qk1.mul(&qk1)).div(&one.sub(&q2));
    guard("run");
    b.widen(&db)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let js = std::fs::read_to_string(&args[1]).unwrap();
    let qstrs: Vec<String> = js.split('"').enumerate().filter(|(i, _)| i % 2 == 1).map(|(_, s)| s.to_string()).collect();
    let cfac: f64 = args[2].split(',').next().unwrap().parse().unwrap();
    let extra: f64 = args[2].split(',').nth(1).unwrap().parse().unwrap();
    for m in args[3..].iter().map(|s| s.parse::<usize>().unwrap()) {
        let t0 = std::time::Instant::now();
        let qf: f64 = qstrs[m - 1][..20].parse().unwrap();
        let bits = (cfac / (1.0 - qf) + extra).ceil() as u32;
        PREC.store(bits, Ordering::Relaxed);
        let q = certify_pole(&qstrs[m - 1]);
        let k = ((0.5 * bits as f64 * 2f64.ln() + 60.0) / (-(qf.ln()))).ceil() as usize;
        let one = I::n(1); let two = I::n(2);
        let b0 = run(&q, &I::n(0), true, k);
        let bh = run(&q, &I::n(1), false, k); // homogeneous slope = B1-B0
        let t1 = b0.neg().div(&bh);
        let x = q.sqrt(); let omq = one.sub(&q);
        let qq = t1.add(&one.add(&x).div(&two.mul(&x)));
        let gv = q.div(&omq); let gu = q.div(&one.sub(&q.mul(&q)));
        let dv = one.sub(&gv.mul(&t1)); let du = one.sub(&gu.mul(&t1));
        let pref = two.mul(&q).mul(&one.add(&x)).div(&omq).mul(&qq);
        let lv = pref.div(&dv); let lu = pref.div(&du);
        let s = gv.mul(&t1);
        println!("m={} bits={} K={} q=[{:.30e} w {:.1e}] slope_sign={} t1=[{:.15e},{:.15e}] s=gV*t1={:.12} Q=t1+(1+x)/2x=[{:.12e},{:.12e}] 1-gVt1={:.12} 1-gUt1={:.12} <lam,R>_y=1=[{:.12e},{:.12e}] <lam,R>_y=q=[{:.12e},{:.12e}] CERT_Q>0:{} CERT_D>0:{} CERT_L>0:{} time {:.1}s rss {:.2e}",
            m, bits, k, q.lo.to_f64(), q.wid(), bh.sign(), t1.lo.to_f64(), t1.hi.to_f64(), s.f(), qq.lo.to_f64(), qq.hi.to_f64(), dv.f(), du.f(),
            lv.lo.to_f64(), lv.hi.to_f64(), lu.lo.to_f64(), lu.hi.to_f64(), qq.lo > 0, dv.lo > 0 && du.lo > 0, lv.lo > 0 && lu.lo > 0,
            t0.elapsed().as_secs_f64(), rss_bytes());
    }
}
