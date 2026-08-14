#!/usr/bin/env python3
"""
TASK E exploration: establish the quantitative facts needed for a van der Corput
bound |T2| <= C sqrt(tau).

We work with the EXACT, CONVERGENT identity
    T2 = sum_{i>=1} (-1)^i psi(i),   psi(i) = W^{2i} g_i / (2i)!,  g_i = 1 - e^{-B_i} in [0,1).
This is the meaningful object (the real-axis AP integral diverges with exact B).

Goal of this script: measure |T2|/sqrt(tau) uniformly in phase, and the ingredients
(saddle width, amplitude, phase second derivative) so we can derive an explicit C.
"""
import mpmath as mp
from abelplana_verify import S1_bulk
mp.mp.dps = 80

def Bint(n, tau):
    """B_n at integer n via the convergent form-factor route (fast, exact)."""
    # B_n = sum_{x=0}^{n-1} b(x),  b(x)=phi((2x+2)t)+phi((2x+1)t)-phi(t)
    def phi(y): return mp.log(mp.sinh(y/2)/(y/2))
    s = mp.mpf(0)
    pt = phi(tau)
    for x in range(n):
        s += phi((2*x+2)*tau) + phi((2*x+1)*tau) - pt
    return s

def T2_via_psi(tau, NMAX=400):
    """T2 = sum_{i>=1}(-1)^i psi(i), psi(i)=W^{2i} g_i/(2i)!. Converges (factorial)."""
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    tot = mp.mpf(0)
    for i in range(1, NMAX+1):
        g = 1 - mp.e**(-Bint(i, tau))
        term = (-1)**i * W**(2*i) * g / mp.factorial(2*i)
        tot += term
        if i > int(W) + 40 and abs(term) < mp.mpf(10)**(-(mp.mp.dps-5)):
            break
    return tot, w, W

print("="*92)
print("Establish |T2|/sqrt(tau) uniformly in phase, via the convergent psi-sum")
print("="*92)
print(f"{'tau':>12} {'w':>9} {'W':>9} {'T2':>20} {'|T2|/sqrtT':>12} {'run-max':>9}")
runmax = mp.mpf(0)
for tau in [mp.mpf(x) for x in ['0.3','0.2','0.1','0.05','0.02','0.01','0.005',
                                 '0.002','0.001','0.0005','0.0002','0.0001']]:
    T2, w, W = T2_via_psi(tau)
    # cross-check vs bulk for tau not too small
    r = abs(T2)/mp.sqrt(tau)
    runmax = max(runmax, r)
    print(f"{float(tau):>12} {float(w):>9.4f} {float(W):>9.4f} {mp.nstr(T2,12):>20} "
          f"{mp.nstr(r,7):>12} {mp.nstr(runmax,7):>9}")
print(f"\nrun-max |T2|/sqrt(tau) over this grid = {mp.nstr(runmax,8)}")
