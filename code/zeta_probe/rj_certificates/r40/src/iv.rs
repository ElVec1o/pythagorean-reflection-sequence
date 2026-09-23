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
