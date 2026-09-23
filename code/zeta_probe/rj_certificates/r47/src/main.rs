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

// ---------------- room 47 additions ----------------
use rug::float::Constant;
impl I {
    fn ln(&self) -> I { assert!(self.lo > 0); I { lo: dn(self.lo.ln_ref()), hi: up(self.hi.ln_ref()) } }
    fn hull(&self, o: &I) -> I { I { lo: fmin(self.lo.clone(), o.lo.clone()), hi: fmax(self.hi.clone(), o.hi.clone()) } }
    fn abs(&self) -> I {
        if self.lo >= 0 { self.clone() } else if self.hi <= 0 { self.neg() }
        else { let m = fmax(Float::with_val(pr(), -&self.lo), self.hi.clone()); I { lo: Float::with_val(pr(), 0), hi: m } }
    }
    fn up_f(&self) -> f64 { Float::with_val_round(53, &self.hi, Round::Up).0.to_f64() }
    fn lo_f(&self) -> f64 { Float::with_val_round(53, &self.lo, Round::Down).0.to_f64() }
}
fn pi() -> I { I { lo: Float::with_val_round(pr(), Constant::Pi, Round::Down).0, hi: Float::with_val_round(pr(), Constant::Pi, Round::Up).0 } }
fn gam() -> I { I { lo: Float::with_val_round(pr(), Constant::Euler, Round::Down).0, hi: Float::with_val_round(pr(), Constant::Euler, Round::Up).0 } }
fn dec(s: &str) -> I { I::s(s) }

/// Cin(x) = sum_{k>=1} (-1)^{k+1} x^{2k}/(2k (2k)!), for x>0 interval with hi <= 60.
/// Terms t_k = x^{2k}/(2k(2k)!): t_{k+1}/t_k = x^2 (2k)/((2k+1)(2k+2)^2) is decreasing in k; once it is
/// <1 for x=hi the series is alternating with decreasing terms, so |remainder after K| <= t_{K+1}.
fn cin_series(x: &I) -> I {
    let x2 = x.mul(x);
    let mut p = x2.div(&I::n(2)); // x^{2k}/(2k)!, k=1
    let mut s = I::n(0); let mut k: i64 = 1;
    loop {
        let t = p.div(&I::n(2 * k));
        s = if k % 2 == 1 { s.add(&t) } else { s.sub(&t) };
        let pn = p.mul(&x2).div(&I::n((2 * k + 1) * (2 * k + 2)));
        let tn = pn.div(&I::n(2 * k + 2));
        let xhi2 = x2.hi.to_f64();
        let ratio_ok = xhi2 * (2 * k) as f64 / (((2 * k + 1) * (2 * k + 2) * (2 * k + 2)) as f64) < 0.5;
        if ratio_ok && tn.hi.to_f64() < 1e-60 {
            let r = I { lo: Float::with_val(pr(), -&tn.hi), hi: tn.hi.clone() };
            return s.add(&r);
        }
        p = pn; k += 1;
    }
}
/// Cin(j*pi) for integer j>=1. Series if j*pi<40; else Cin = gamma + ln x - Ci(x), Ci(j pi) = -(-1)^j g(j pi),
/// g(x) = int_0^inf t e^{-xt}/(1+t^2) dt in [1/x^2 - 6/x^4, 1/x^2]  (A&S 5.2.9, 5.2.13).
fn cin_jpi(j: i64) -> I {
    let x = I::n(j).mul(&pi());
    if (j as f64) * 3.2 < 40.0 { return cin_series(&x); }
    let x2 = x.mul(&x);
    let ghi = I::n(1).div(&x2); let glo = ghi.sub(&I::n(6).div(&x2.mul(&x2)));
    let g = I { lo: glo.lo.clone(), hi: ghi.hi.clone() };
    let ci = if j % 2 == 0 { g.neg() } else { g };
    gam().add(&x.ln()).sub(&ci)
}
/// C0'(m) enclosure: sum_{n != m, n <= N} |mu_mn| plus rigorous tail bound for n > N.
/// |mu_mn| = 8 a^2/(pi^2 b^2 |a^2-b^2|) * J_mn/J_mm, a=2m-1, b=2n-1, J_mn = (Cin((m+n-1)pi) - Cin(|m-n| pi))/2.
fn c0(m: i64) -> (I, I) {
    let a = 2 * m - 1; let pi = pi(); let pi2 = pi.mul(&pi);
    let jmm = cin_jpi(a).div(&I::n(2));
    let nn = 4 * m + 40;
    let mut tot = I::n(0);
    for n in 1..=nn {
        if n == m { continue; }
        let b = 2 * n - 1;
        let j = cin_jpi(m + n - 1).sub(&cin_jpi((m - n).abs())).div(&I::n(2));
        assert!(j.lo > 0);
        let w = I::n(8 * a * a).div(&pi2.mul(&I::n(b * b)).mul(&I::n((a * a - b * b).abs())));
        tot = tot.add(&w.mul(&j).div(&jmm));
    }
    // tail n>N (proof in report): |mu| <= (2a^2 (a/2 + 1/pi^2)/(pi^2 J_mm)) / (4 d^5), d=n-m; sum_{d>D} d^-5 <= 1/(4 D^4)
    let dd = nn - m;
    let k = I::n(2 * a * a).mul(&I::n(a).div(&I::n(2)).add(&I::n(1).div(&pi2))).div(&pi2.mul(&jmm));
    let tail = k.div(&I::n(16).mul(&I::n(dd).pow(4)));
    (tot, tail)
}
/// Room 46 c4.py, eta4 constant c(M), replicated with directed rounding and rigorous gamma.
fn eta4(mm: i64) -> (f64, f64, Vec<(String, f64)>) {
    let pi = pi(); let m = I::n(mm);
    let k = m.sub(&dec("0.5")).mul(&pi);
    let c20 = dec("2.0055");
    let e = c20.div(&k.mul(&k)); let q = I::n(1).sub(&e);
    let rmax = I::n(6 * mm - 1).div(&I::n(2 * mm - 1));
    let sn = e.mul(&rmax).mul(&k).div(&I::n(1).sub(&e));
    let an = sn.div(&I::n(2).sub(&sn));
    let snn = an.exp().div(&I::n(1).add(&q).sub(&sn));
    let sm = I::n(2).mul(&e).sqrt(); let am = sm.div(&I::n(2).sub(&sm));
    let smm = am.exp().div(&I::n(1).add(&q).sub(&sm));
    let sig = smm.mul(&snn).sqrt();
    let om = I::n(1).sub(&e);
    let c1 = c20.mul(&sig).div(&I::n(2).mul(&om).mul(&om));
    let eh = e.mul(&dec("6.5").add(&dec("1.4").mul(&k.ln())));
    let mut out: Vec<(String, I)> = vec![];
    let pi2 = pi.mul(&pi);
    let dl = I::n(5).div(&pi2.mul(&I::n(mm * mm)));
    let r0 = I::n(1).div(&I::n(2 * mm - 1));
    out.push(("n<m far".into(), r0.div(&r0.sub(&dl).sub(&eh))));
    out.push(("n<m near".into(), I::n(1).div(&I::n(1).sub(&eh.div(&I::n(mm - 1).div(&I::n(2 * mm - 1)))))));
    let k2 = I::n(2).mul(&k);
    let jmm = gam().add(&k2.ln()).sub(&I::n(2).div(&k2.mul(&k2))).div(&I::n(2));
    out.push(("n=m".into(), I::n(1).div(&jmm.sub(&eh))));
    for d in 1..=10 {
        let n = mm + d; let r = I::n(2 * n - 1).div(&I::n(2 * mm - 1));
        let l = I::n(1).add(&r).div(&r.sub(&I::n(1))).ln().div(&I::n(2));
        let dl = I::n(1).div(&pi2.mul(&I::n(d * d))).add(&I::n(1).div(&pi2.mul(&I::n((2 * mm - 1 + d) * (2 * mm - 1 + d)))));
        out.push((format!("d={}", d), r.div(&l.sub(&dl).sub(&eh))));
    }
    let l = I::n(1).add(&rmax).div(&rmax.sub(&I::n(1))).ln().div(&I::n(2));
    let dl = I::n(1).div(&I::n(100).mul(&pi2)).add(&I::n(1).div(&pi2.mul(&I::n(4 * mm * mm))));
    out.push(("d>10 (at rmax)".into(), rmax.div(&l.sub(&dl).sub(&eh))));
    let mut w = out[0].1.clone();
    for (_, v) in &out { assert!(v.lo > 0, "nonpositive denominator"); w = w.maxu(v); }
    let c = c1.mul(&w).add(&c20.div(&k2));
    (c.up_f(), w.up_f(), out.iter().map(|(s, v)| (s.clone(), v.up_f())).collect())
}
fn main() {
    PREC.store(256, Ordering::Relaxed);
    let args: Vec<String> = std::env::args().collect();
    let mode = args[1].as_str();
    if mode == "c0" {
        let m1: i64 = args[2].parse().unwrap(); let m2: i64 = args[3].parse().unwrap();
        let mut worst = 0.0f64; let mut wm = 0;
        for m in m1..m2 {
            let (t, tl) = c0(m); let u = t.add(&tl);
            let up = u.up_f();
            if up > worst { worst = up; wm = m; }
            if m < 14 || m % 50 == 0 || m == m2 - 1 {
                println!("m={} sum in [{:.12e}, {:.12e}] width {:.2e} tail<= {:.3e} upper {:.10}", m, t.lo_f(), t.up_f(), t.wid(), tl.up_f(), up);
            }
            guard("c0");
        }
        println!("C0' interval part m in [{},{}): max upper = {:.10} at m={}  (<= 0.063512: {})", m1, m2, worst, wm, worst <= 0.063512);
    } else if mode == "eta4" {
        for a in &args[2..] {
            let mm: i64 = a.parse().unwrap();
            let (c, w, v) = eta4(mm);
            println!("M={} c(M) <= {:.6}  w={:.6}  (c<=5.95: {})", mm, c, w, c <= 5.95);
            if mm <= 12 { for (s, x) in v { println!("    {:16} {:.6}", s, x); } }
        }
    } else if mode == "xcheck" {
        // cross-check series vs envelope for j*pi in [13,19]
        for j in 5..=13 {
            let x = I::n(j).mul(&pi());
            let s = cin_series(&x);
            let x2 = x.mul(&x); let ghi = I::n(1).div(&x2); let glo = ghi.sub(&I::n(6).div(&x2.mul(&x2)));
            let g = I { lo: glo.lo.clone(), hi: ghi.hi.clone() };
            let ci = if j % 2 == 0 { g.neg() } else { g };
            let env = gam().add(&x.ln()).sub(&ci);
            println!("j={} series [{:.15},{:.15}] env [{:.15},{:.15}] overlap {}", j, s.lo_f(), s.up_f(), env.lo_f(), env.up_f(), !(s.hi < env.lo || env.hi < s.lo));
        }
    }
}
