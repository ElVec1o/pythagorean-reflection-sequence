#!/usr/bin/env python3
"""The phase-matching step that closes the U-numerator gate (paper2.tex, rem:elemY3).

Derivation (symbolic, sympy) + verification (mpmath vs poles.txt):

1. POLE EQUATION. The travel poles solve Sigma_1(q)=1 (travel_poles_mp.py). The series collapses
   EXACTLY (verified 1e-47) to
       1 - Sigma_1 = Sum_{j>=0} (-1)^j sinh^j(tau/2) / prod_{m=1}^{2j} sinh(m tau/2)
   = the S_e series stripped of its e^{-j tau} phase. The elementary expansion machinery
   (linear absorption + Faulhaber curvature + moment identities) applies verbatim with
       y* = (2/tau) e^{tau^2/36},  c2 = -tau^2/12,  c3 = -tau^2/9,  c5 = tau^4/450.

2. ZERO EQUATION. The U-numerator amplitude Sum_k d_k (= Y_3(1)) has the derived expansion of
   elemY3_verify.py with y* = (2/tau) e^{-tau-23 tau^2/36}, c2 = -5 tau^2/12, same c3, c5.

3. PHASE SOLVE. In the common variable w = sqrt(2/tau) (poles.txt convention q = e^{-2/w^2}),
   both conditions are solved perturbatively near each grid point (M+1/2)pi:
       chi_pole = -(sqrt2/36) sqrt(tau) + (41 sqrt2/2400)  tau^{3/2} + O(tau^2)
       chi_zero = -(sqrt2/36) sqrt(tau) - (259 sqrt2/2400) tau^{3/2} + O(tau^2)
   The sqrt(tau) phases agree IDENTICALLY (both produced by the universal c3 = -tau^2/9; the
   sqrt2/36 is lem:cos's constant) -- this is why the travel poles track the zeros of Y_3(1).
   The offset is
       dw = chi_pole - chi_zero = (sqrt2/8) tau^{3/2} + O(tau^2).

4. GATE. |Sum d_k| = (3 tau/2) dw (1+O(sqrt tau)) = (3/(8 sqrt2)) tau^{5/2}, hence
       |P12|/tau^{3/2} -> 1/(4 sqrt2) = 0.176777 < 1/sqrt2   (fourfold margin: the gate, DERIVED).

Verified below: the two phase series match the exact pole/zero locations to ~7 digits at
m = 10,16,22,28, and dw/tau^{3/2} -> sqrt2/8. OOM-safe: single-thread, dps 60.
"""
import sympy as sp
import mpmath as mp

# ---------------- symbolic derivation ----------------
s, W = sp.symbols('s W', positive=True)
tau = s**2
sq2 = sp.sqrt(2)

def Dn(e, n):
    for _ in range(n):
        e = sp.expand((W/2)*sp.diff(e, W))
    return e

c3 = -tau**2/9; c5 = tau**4/450
def build(F, c2):
    return sp.expand(F + c3*Dn(F,3) + c2*Dn(F,2) + c3**2/2*Dn(F,6)
                     + (c5 + c2*c3)*Dn(F,5) + c3**3/6*Dn(F,9))

Et = build(sp.cos(W), -tau**2/12)                                   # pole side
EY = build((sp.sin(W) - W*sp.cos(W))/(2*W**3), -sp.Rational(5,12)*tau**2)  # zero side

def phase_series(E, Wsub, corr):
    Ee = sp.expand(E)
    Ac = Ee.coeff(sp.cos(W)); As_ = Ee.coeff(sp.sin(W))
    assert sp.simplify(Ee - (Ac*sp.cos(W) + As_*sp.sin(W))) == 0
    R = sp.cancel(As_/Ac)
    Rs = sp.series(R.subs(W, Wsub), s, 0, 5).removeO()
    delta = sp.expand(Rs - Rs**3/3)
    return sp.expand(sp.series(sp.expand(delta + corr), s, 0, 4).removeO())

chi_t = phase_series(Et, sq2/s*(1 + s**4/72),                     -sq2*s**3/72)
chi_Y = phase_series(EY, sq2/s*(1 - s**2/2 - sp.Rational(7,36)*s**4), s/sq2 + sp.Rational(7,36)*sq2*s**3)
dw = sp.expand(chi_t - chi_Y)
assert dw.coeff(s,1) == 0 and dw.coeff(s,2) == 0
assert sp.simplify(dw.coeff(s,3) - sq2/8) == 0
print("chi_pole =", sp.nsimplify(chi_t,[sq2]))
print("chi_zero =", sp.nsimplify(chi_Y,[sq2]))
print("dw       =", sp.nsimplify(dw,[sq2]), "   [= (sqrt2/8) tau^{3/2}]")

# ---------------- numeric verification ----------------
mp.mp.dps = 60
POLES = [l.strip() for l in open("poles.txt") if l.strip()]

def dsum_exact(t):
    t = mp.mpf(t); q = mp.e**(-t); acc = mp.mpf(0)
    for kk in range(6000):
        num = (-2)**kk*(1-q)**kk*q**(kk*kk+3*kk); den = mp.mpf(1)
        for j in range(1, kk+1):
            den *= (1-q**(2*j))*(1-q**(2*j+3))
        tt = num/den; acc += tt
        if kk > 8 and abs(tt) < mp.mpf(10)**(-66): break
    return acc

r2 = mp.sqrt(2)
print(f"\n{'m':>4} {'chi_pole num':>14} {'formula':>13} {'chi_zero num':>14} {'formula':>13} {'dw/t^1.5':>10}")
for m in [10, 16, 22, 28]:
    q = mp.mpf(POLES[m]); t = -mp.log(q); sr = mp.sqrt(t); w = mp.sqrt(2/t)
    grid = (mp.floor(w/mp.pi - mp.mpf('0.5')) + mp.mpf('0.5'))*mp.pi
    if abs(w-grid) > mp.pi/2: grid += mp.pi*mp.sign(w-grid)
    wz = mp.findroot(lambda ww: dsum_exact(2/ww**2), w - mp.mpf('0.17')*t**mp.mpf(1.5), tol=1e-40)
    print(f"{m:>4} {mp.nstr(w-grid,7):>14} {mp.nstr(-r2/36*sr+41*r2/2400*sr**3,7):>13} "
          f"{mp.nstr(wz-grid,7):>14} {mp.nstr(-r2/36*sr-259*r2/2400*sr**3,7):>13} "
          f"{mp.nstr((w-wz)/t**mp.mpf(1.5),7):>10}")
print(f"\ntarget sqrt2/8 = {mp.nstr(r2/8,8)};  gate |P12|/tau^1.5 -> 1/(4 sqrt2) = {mp.nstr(1/(4*r2),8)} < 1/sqrt2")
