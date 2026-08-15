// Interval (outward-rounded) arithmetic over MPFR, via rug.
//
// Every operation returns an interval that provably contains the exact result
// for every argument in the input intervals.  MPFR is correctly rounded for all
// the functions used here (add, sub, mul, div, sqrt, exp, log, sinh, cosh,
// atan, lgamma), so directed rounding of the endpoints is exact outward
// rounding: no epsilon fudge factors appear anywhere in this file.

use rug::float::{Constant, Round};
use rug::ops::{AddAssignRound, DivAssignRound, MulAssignRound, SubAssignRound};
use rug::Float;
use std::sync::atomic::{AtomicU32, Ordering as AOrd};

static PREC: AtomicU32 = AtomicU32::new(96);

pub fn set_prec(p: u32) {
    PREC.store(p, AOrd::SeqCst);
}
pub fn prec() -> u32 {
    PREC.load(AOrd::Relaxed)
}
pub fn fl(x: f64) -> Float {
    Float::with_val(prec(), x)
}

fn fmin(a: Float, b: Float) -> Float {
    if a < b {
        a
    } else {
        b
    }
}
fn fmax(a: Float, b: Float) -> Float {
    if a > b {
        a
    } else {
        b
    }
}

#[derive(Clone, Debug)]
pub struct Iv {
    pub lo: Float,
    pub hi: Float,
}

impl Iv {
    pub fn c(x: f64) -> Iv {
        Iv { lo: fl(x), hi: fl(x) }
    }
    pub fn ab(a: f64, b: f64) -> Iv {
        debug_assert!(a <= b);
        Iv { lo: fl(a), hi: fl(b) }
    }
    pub fn of(lo: Float, hi: Float) -> Iv {
        Iv { lo, hi }
    }
    pub fn zero() -> Iv {
        Iv::c(0.0)
    }
    pub fn one() -> Iv {
        Iv::c(1.0)
    }
    pub fn pi() -> Iv {
        let lo = Float::with_val_round(prec(), Constant::Pi, Round::Down).0;
        let hi = Float::with_val_round(prec(), Constant::Pi, Round::Up).0;
        Iv { lo, hi }
    }
    pub fn hi_f64(&self) -> f64 {
        self.hi.to_f64_round(Round::Up)
    }
    pub fn lo_f64(&self) -> f64 {
        self.lo.to_f64_round(Round::Down)
    }

    pub fn add(&self, o: &Iv) -> Iv {
        let mut lo = self.lo.clone();
        lo.add_assign_round(&o.lo, Round::Down);
        let mut hi = self.hi.clone();
        hi.add_assign_round(&o.hi, Round::Up);
        Iv { lo, hi }
    }
    pub fn sub(&self, o: &Iv) -> Iv {
        let mut lo = self.lo.clone();
        lo.sub_assign_round(&o.hi, Round::Down);
        let mut hi = self.hi.clone();
        hi.sub_assign_round(&o.lo, Round::Up);
        Iv { lo, hi }
    }
    pub fn neg(&self) -> Iv {
        // negation is exact in binary floating point
        Iv { lo: -self.hi.clone(), hi: -self.lo.clone() }
    }
    pub fn mul(&self, o: &Iv) -> Iv {
        let ends = [(&self.lo, &o.lo), (&self.lo, &o.hi), (&self.hi, &o.lo), (&self.hi, &o.hi)];
        let mut lo: Option<Float> = None;
        let mut hi: Option<Float> = None;
        for (a, b) in ends {
            let mut p = a.clone();
            p.mul_assign_round(b, Round::Down);
            lo = Some(match lo {
                None => p,
                Some(m) => fmin(m, p),
            });
            let mut q = a.clone();
            q.mul_assign_round(b, Round::Up);
            hi = Some(match hi {
                None => q,
                Some(m) => fmax(m, q),
            });
        }
        Iv { lo: lo.unwrap(), hi: hi.unwrap() }
    }
    /// requires 0 not in [o.lo, o.hi]
    pub fn div(&self, o: &Iv) -> Iv {
        assert!(o.lo > 0.0 || o.hi < 0.0, "interval division by an interval containing 0");
        let ends = [(&self.lo, &o.lo), (&self.lo, &o.hi), (&self.hi, &o.lo), (&self.hi, &o.hi)];
        let mut lo: Option<Float> = None;
        let mut hi: Option<Float> = None;
        for (a, b) in ends {
            let mut p = a.clone();
            p.div_assign_round(b, Round::Down);
            lo = Some(match lo {
                None => p,
                Some(m) => fmin(m, p),
            });
            let mut q = a.clone();
            q.div_assign_round(b, Round::Up);
            hi = Some(match hi {
                None => q,
                Some(m) => fmax(m, q),
            });
        }
        Iv { lo: lo.unwrap(), hi: hi.unwrap() }
    }
    pub fn scal(&self, c: f64) -> Iv {
        self.mul(&Iv::c(c))
    }
    pub fn shift(&self, c: f64) -> Iv {
        self.add(&Iv::c(c))
    }
    pub fn sqr(&self) -> Iv {
        let (a, b) = (&self.lo, &self.hi);
        if *a >= 0.0 {
            let mut lo = a.clone();
            lo.mul_assign_round(a, Round::Down);
            let mut hi = b.clone();
            hi.mul_assign_round(b, Round::Up);
            Iv { lo, hi }
        } else if *b <= 0.0 {
            let mut lo = b.clone();
            lo.mul_assign_round(b, Round::Down);
            let mut hi = a.clone();
            hi.mul_assign_round(a, Round::Up);
            Iv { lo, hi }
        } else {
            let mut h1 = a.clone();
            h1.mul_assign_round(a, Round::Up);
            let mut h2 = b.clone();
            h2.mul_assign_round(b, Round::Up);
            Iv { lo: fl(0.0), hi: fmax(h1, h2) }
        }
    }
    pub fn sqrt(&self) -> Iv {
        assert!(self.lo >= 0.0, "sqrt of an interval reaching below 0");
        let mut lo = self.lo.clone();
        lo.sqrt_round(Round::Down);
        let mut hi = self.hi.clone();
        hi.sqrt_round(Round::Up);
        Iv { lo, hi }
    }
    pub fn exp(&self) -> Iv {
        let mut lo = self.lo.clone();
        lo.exp_round(Round::Down);
        let mut hi = self.hi.clone();
        hi.exp_round(Round::Up);
        Iv { lo, hi }
    }
    pub fn ln(&self) -> Iv {
        assert!(self.lo > 0.0, "ln of an interval reaching 0");
        let mut lo = self.lo.clone();
        lo.ln_round(Round::Down);
        let mut hi = self.hi.clone();
        hi.ln_round(Round::Up);
        Iv { lo, hi }
    }
    pub fn sinh(&self) -> Iv {
        let mut lo = self.lo.clone();
        lo.sinh_round(Round::Down);
        let mut hi = self.hi.clone();
        hi.sinh_round(Round::Up);
        Iv { lo, hi }
    }
    pub fn tanh(&self) -> Iv {
        let mut lo = self.lo.clone();
        lo.tanh_round(Round::Down);
        let mut hi = self.hi.clone();
        hi.tanh_round(Round::Up);
        Iv { lo, hi }
    }
    pub fn atan(&self) -> Iv {
        let mut lo = self.lo.clone();
        lo.atan_round(Round::Down);
        let mut hi = self.hi.clone();
        hi.atan_round(Round::Up);
        Iv { lo, hi }
    }
    /// |x| as an interval (even, so use the near/far endpoints)
    pub fn abs(&self) -> Iv {
        let near = if self.lo <= 0.0 && self.hi >= 0.0 {
            fl(0.0)
        } else {
            fmin(self.lo.clone().abs(), self.hi.clone().abs())
        };
        let far = fmax(self.lo.clone().abs(), self.hi.clone().abs());
        Iv { lo: near, hi: far }
    }
    /// cosh is even and increasing in |x|
    pub fn cosh(&self) -> Iv {
        let a = self.abs();
        let mut lo = a.lo.clone();
        lo.cosh_round(Round::Down);
        let mut hi = a.hi.clone();
        hi.cosh_round(Round::Up);
        Iv { lo, hi }
    }
    pub fn min(&self, o: &Iv) -> Iv {
        Iv { lo: fmin(self.lo.clone(), o.lo.clone()), hi: fmin(self.hi.clone(), o.hi.clone()) }
    }
    /// ln Gamma of a real interval, valid only where lnGamma is increasing (x >= 2)
    pub fn ln_gamma_incr(&self) -> Iv {
        assert!(self.lo >= 2.0);
        let mut lo = self.lo.clone();
        lo.ln_gamma_round(Round::Down);
        let mut hi = self.hi.clone();
        hi.ln_gamma_round(Round::Up);
        Iv { lo, hi }
    }
}

/// Rectangular complex interval.
#[derive(Clone, Debug)]
pub struct Cx {
    pub re: Iv,
    pub im: Iv,
}

impl Cx {
    pub fn mul(&self, o: &Cx) -> Cx {
        Cx {
            re: self.re.mul(&o.re).sub(&self.im.mul(&o.im)),
            im: self.re.mul(&o.im).add(&self.im.mul(&o.re)),
        }
    }
    pub fn add(&self, o: &Cx) -> Cx {
        Cx { re: self.re.add(&o.re), im: self.im.add(&o.im) }
    }
    pub fn sub(&self, o: &Cx) -> Cx {
        Cx { re: self.re.sub(&o.re), im: self.im.sub(&o.im) }
    }
    pub fn scal(&self, c: f64) -> Cx {
        Cx { re: self.re.scal(c), im: self.im.scal(c) }
    }
    pub fn abs(&self) -> Iv {
        self.re.sqr().add(&self.im.sqr()).sqrt()
    }
}
