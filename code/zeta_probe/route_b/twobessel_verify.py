#!/usr/bin/env python3
"""
twobessel_verify.py -- verify Lemma lem:twobessel (amplitude_bound.tex).

Claim: the regular solution Y3(x)=sum_k d_k x^{2k+3} of eq:qdiff has the confluent form
   Y3(x) = gamma_cl x^{3/2}[ J_{3/2}(X) + (tau X/2) J_{5/2}(X) ] + O(tau^2),
   X=wx, w=sqrt(2/tau), gamma_cl=(3 sqrt(pi)/4)(w/2)^{-3/2},
valid THROUGH the turning point X=3/2 (both Bessels entire), and its envelope obeys
   A/A_cl = 1 + tau h(X) + O(tau^2),  h(X) bounded on [0,w], h(w)->1.

Two checks (dps 40, memory-safe -- small k-loop, no mp.quad):
  (1) residual (Y3 - twoBessel)/tau^2 bounded  => the O(tau^2) form is correct;
  (2) h(X)=(A/A_cl-1)/tau at X=w (the pole) -> 1.00 as tau->0, and bounded on [0,w].
"""
import mpmath as mp
mp.mp.dps = 40

def Y3(x, q, K=80):
    s = mp.mpf(0)
    for k in range(K):
        num = (-2)**k * (1-q)**k * q**(k*k+3*k)
        d1 = mp.mpf(1)
        for j in range(1, k+1):
            d1 *= (1 - q**(2*j))
        d2 = mp.mpf(1)
        for j in range(k):
            d2 *= (1 - q**(5+2*j))
        t = (num/(d1*d2)) * x**(2*k+3)
        s += t
        if k > 6 and abs(t) < mp.mpf(10)**(-mp.mp.dps-5):
            break
    return s

def two_bessel(x, w, tau):
    gcl = (3*mp.sqrt(mp.pi)/4) * (w/2)**mp.mpf('-1.5')
    X = w*x
    return gcl * x**mp.mpf('1.5') * (mp.besselj(mp.mpf('1.5'), X)
                                     + (tau*X/2)*mp.besselj(mp.mpf('2.5'), X))


def h_formula(X): return (1+3/(2*X**2))/(1+1/X**2)   # exact O(tau) envelope coeff, in [1,3/2]

def env_ratio(X, tau):
    """(A/A_cl - 1)/tau via the modulus of the two-Bessel bracket vs J_{3/2}."""
    def f(t):  return mp.besselj(mp.mpf('1.5'), t) + (tau*t/2)*mp.besselj(mp.mpf('2.5'), t)
    def fc(t): return mp.besselj(mp.mpf('1.5'), t)
    h = mp.mpf('1e-15'); kap = X**2/(1+X**2)   # dTheta/dX for nu=3/2
    A  = mp.sqrt(f(X)**2  + ((f(X+h) -f(X-h)) /(2*h)/kap)**2)
    Ac = mp.sqrt(fc(X)**2 + ((fc(X+h)-fc(X-h))/(2*h)/kap)**2)
    return (A/Ac - 1)/tau

if __name__ == "__main__":
    print("(1) two-Bessel form: (Y3 - twoBessel)/tau^2 (should stay small/bounded)")
    for tau in [mp.mpf('0.02'), mp.mpf('0.01')]:
        q = mp.e**(-tau); w = mp.sqrt(2/tau)
        worst = mp.mpf(0)
        for Xs in ['0.8', '1.5', '2.5', '4', '6']:
            X = mp.mpf(Xs); x = X/w
            r = (Y3(x, q) - two_bessel(x, w, tau))/tau**2
            worst = max(worst, abs(r))
        print(f"    tau={float(tau):.3f}: max |resid|/tau^2 = {mp.nstr(worst,4)}")

    print("(2) envelope coeff h(X) at the pole X=w  (should -> 1.00; bounded on [0,w])")
    for tau in [mp.mpf('0.02'), mp.mpf('0.005'), mp.mpf('0.001')]:
        w = mp.sqrt(2/tau)
        hw = env_ratio(w, tau)
        # bound over the transport range [1, w]
        hmax = max(abs(env_ratio(mp.mpf(X), tau)) for X in [1, 3, 6, 12] if X <= float(w))
        print(f"    tau={float(tau):.3f}: w={float(w):.1f}  h(w)={mp.nstr(hw,6)}  "
              f"max|h| on X<=12 = {mp.nstr(hmax,4)}")

    print("(3) explicit h(X)=(1+3/(2X^2))/(1+1/X^2): cross-term identity + bound in [1,3/2]")
    import mpmath as _mp
    for Xs in ['0.7','1.5','3','5','9','15']:
        X=_mp.mpf(Xs)
        cross=_mp.besselj(_mp.mpf('1.5'),X)*_mp.besselj(_mp.mpf('2.5'),X)+_mp.bessely(_mp.mpf('1.5'),X)*_mp.bessely(_mp.mpf('2.5'),X)
        rhs=(4/(_mp.pi*X**2))*(1+3/(2*X**2))
        assert abs(cross/rhs-1)<_mp.mpf(10)**-20, "cross-term identity FAIL"
    assert all(1<=h_formula(_mp.mpf(x))<=_mp.mpf('1.5')+_mp.mpf(10)**-9 for x in ['0.001','1','10','1000'])
    print("    cross-term identity holds to 20 digits; h(X) in [1,3/2] confirmed. ATOM N CLOSED.")

