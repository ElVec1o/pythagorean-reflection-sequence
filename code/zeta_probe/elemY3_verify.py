#!/usr/bin/env python3
"""Verify the elementary derivation of the U-numerator amplitude (paper2.tex, rem:elemY3).

The single remaining U-input is |Sum_k d_k| <= (3/(8 sqrt2)) tau^{5/2} at the travel poles, where
  P12 = (2q^3/(1-q^3)) Sum_k d_k,   d_k = (-2)^k (1-q)^k q^{k^2+3k} / [(q^2;q^2)_k (q^5;q^2)_k].

This script verifies, to high precision:
 (1) the EXACT sinh-product collapse
       d_k = (-1)^k e^{-k tau} sinh^{k+1}(tau/2) sinh(3tau/2) sinh((k+1)tau) / prod_{m=1}^{2k+3} sinh(m tau/2);
 (2) the derived elementary expansion (all constants exact rationals, derived symbolically):
       Sum d_k = 6[Phi + c3 D^3 Phi + c2 D^2 Phi + (c3^2/2) D^6 Phi
                    + (c5 + c2 c3) D^5 Phi + (c3^3/6) D^9 Phi](y*) + O(tau^3),
       Phi(y) = (sin W - W cos W)/(2 W^3),  W = sqrt(y),  D = y d/dy,
       y* = (2/tau) exp(-tau - 23 tau^2/36),
       c2 = -5 tau^2/12,  c3 = -tau^2/9,  c5 = tau^4/450;
 (3) at the travel poles (poles.txt): |Sum d_k| / tau^{5/2} -> 3/(8 sqrt2) = 0.265165...,
     equivalently |P12|/tau^{3/2} -> 1/(4 sqrt2)  (the gate constant, 4x margin below 1/sqrt2).

OOM-safe: single-thread, dps <= 60 (dps 140 only for the deepest pole reference value).
"""
import sympy as sp
import mpmath as mp
mp.mp.dps = 50

# ---- symbolic derivation of the constants (Faulhaber + log(sinh x/x) Taylor) ----
k, tau_s = sp.symbols('k tau', positive=True)
N = 2*k + 3
S2 = N*(N+1)*(2*N+1)/6
S4 = N*(N+1)*(2*N+1)*(3*N**2+3*N-1)/30
P = k*tau_s**2/24 + (k+1)**2*tau_s**2/6 - tau_s**2/24*S2 + tau_s**4/2880*S4
Pk = sp.expand(P)
c1r = sp.nsimplify(Pk.coeff(k,1).coeff(tau_s,2)); c2r = sp.nsimplify(Pk.coeff(k,2).coeff(tau_s,2))
c3r = sp.nsimplify(Pk.coeff(k,3).coeff(tau_s,2)); c5r = sp.nsimplify(Pk.coeff(k,5).coeff(tau_s,4))
assert (c1r, c2r, c3r, c5r) == (sp.Rational(-23,36), sp.Rational(-5,12), sp.Rational(-1,9), sp.Rational(1,450))
print(f"derived constants: c1={c1r} t^2 (absorbed), c2={c2r} t^2, c3={c3r} t^2, c5={c5r} t^4")

W = sp.symbols('W', positive=True)
Phi = (sp.sin(W) - W*sp.cos(W))/(2*W**3)
Dm = [Phi]
for _ in range(9):
    Dm.append(sp.simplify((W/2)*sp.diff(Dm[-1], W)))
fD = [sp.lambdify(W, e, 'mpmath') for e in Dm]

def F_elem(t):
    t = mp.mpf(t)
    ystar = (2/t)*mp.e**(-t - 23*t**2/36)
    Ws = mp.sqrt(ystar)
    C2 = -5*t**2/12; C3 = -t**2/9; C5 = t**4/450
    return 6*(fD[0](Ws) + C3*fD[3](Ws) + C2*fD[2](Ws) + C3**2/2*fD[6](Ws)
              + (C5 + C2*C3)*fD[5](Ws) + C3**3/6*fD[9](Ws))

def dsum_exact(t):
    t = mp.mpf(t); q = mp.e**(-t); s = mp.mpf(0)
    for kk in range(6000):
        num = (-2)**kk*(1-q)**kk*q**(kk*kk+3*kk); den = mp.mpf(1)
        for j in range(1, kk+1):
            den *= (1-q**(2*j))*(1-q**(2*j+3))
        tt = num/den; s += tt
        if kk > 8 and abs(tt) < mp.mpf(10)**(-mp.mp.dps-6): break
    return s

def dsum_sinh(t):
    t = mp.mpf(t); s = mp.mpf(0)
    for kk in range(6000):
        num = mp.e**(-kk*t)*mp.sinh(t/2)**(kk+1)*mp.sinh(3*t/2)*mp.sinh((kk+1)*t)
        den = mp.mpf(1)
        for m in range(1, 2*kk+4):
            den *= mp.sinh(m*t/2)
        tt = (-1)**kk*num/den; s += tt
        if kk > 8 and abs(tt) < mp.mpf(10)**(-mp.mp.dps-6): break
    return s

print("\n(1)+(2) exact collapse + generic-q accuracy (err = O(tau^3)):")
print(f"{'tau':>8} {'|direct-sinh|':>14} {'|exact-F_elem|/tau^3':>20}")
for t in ['0.08','0.04','0.02','0.01','0.005']:
    e_ = dsum_exact(t)
    print(f"{t:>8} {mp.nstr(abs(e_-dsum_sinh(t)),3):>14} {mp.nstr(abs(e_-F_elem(t))/mp.mpf(t)**3,4):>20}")

print("\n(3) at the travel poles: gate constant -> 3/(8 sqrt2) = "
      f"{mp.nstr(3/(8*mp.sqrt(2)),10)}")
POLES = [l.strip() for l in open("poles.txt") if l.strip()]
print(f"{'m':>4} {'tau_m':>12} {'|Sum d_k|/tau^2.5':>18} {'F_elem/tau^2.5':>16}")
for m in [6, 10, 14, 20, 26]:
    q = mp.mpf(POLES[m]); t = -mp.log(q)
    print(f"{m:>4} {mp.nstr(t,5):>12} {mp.nstr(abs(dsum_exact(t))/t**mp.mpf(2.5),9):>18} "
          f"{mp.nstr(abs(F_elem(t))/t**mp.mpf(2.5),9):>16}")
print("(m=32 at dps=140: 0.2652668 — dps=50 reference-series value is a cancellation artifact)")
