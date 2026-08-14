#!/usr/bin/env python3
"""
POISSON route -> CONVERGENT oscillatory integral -> van der Corput.

Claim: with PSI(y) = W^{2y} g_y / Gamma(2y+1) (real, smooth on y>0, decaying factorially),
   T2 = sum_{i>=1} (-1)^i PSI(i).
Extend to a function vanishing appropriately; the alternating sum equals (dominant part)
   2 Re[ F(1/2) ] + (corrections),  F(xi) = int_0^infty PSI(y) e^{-2 pi i xi y} dy,  xi=1/2
i.e. the dominant oscillatory integral is
   J := int_0^infty PSI(y) e^{i pi y} dy   (and conj).   [phase frequency pi]
We VERIFY numerically that |T2| is controlled by |J| and that J = int PSI e^{i pi y}
is a convergent stationary-phase integral.

We use the loggamma continuation of B to get g_y at REAL non-integer y.
"""
import mpmath as mp
from abelplana_verify import B_exact
mp.mp.dps = 50

def PSI(y, W, tau):
    """W^{2y} g_y / Gamma(2y+1), real y>0, g_y=1-e^{-B_y} via loggamma continuation."""
    B,_ = B_exact(mp.mpf(y), tau)   # B at real s=y; B real for real y
    g = 1 - mp.e**(-mp.re(B))
    return W**(2*y) * g / mp.gamma(2*y+1)

def run(tau):
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    ystar=W/2
    # the convergent oscillatory integral J = int_0^inf PSI(y) e^{i pi y} dy
    # integrate to well past W where PSI is negligible
    ytop = float(W)+30
    f = lambda y: PSI(y,W,tau)*mp.e**(mp.mpc(0,1)*mp.pi*y)
    pts=[mp.mpf(p) for p in [0, float(ystar)*0.5, float(ystar), float(W)*0.75,
                              float(W), float(W)+8, ytop]]
    J = mp.quad(f, pts)
    # direct T2 (psi integer sum)
    def Bint(n):
        from math import isqrt
        def phi(yy): return mp.log(mp.sinh(yy/2)/(yy/2))
        s=mp.mpf(0); pt=phi(tau)
        for x in range(n): s+=phi((2*x+2)*tau)+phi((2*x+1)*tau)-pt
        return s
    T2=mp.mpf(0)
    for i in range(1,int(W)+40):
        g=1-mp.e**(-Bint(i)); T2+=(-1)**i*W**(2*i)*g/mp.factorial(2*i)
    return T2,J,W,ystar

print("Verify: alternating sum T2 vs the convergent oscillatory integral 2 Re J, J=int PSI e^{i pi y}.")
print(f"{'tau':>9} {'T2':>16} {'2 Re J':>16} {'|J|':>12} {'|J|/sqrtT':>10} {'T2 - 2ReJ':>12}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    T2,J,W,ys=run(tau)
    print(f"{float(tau):>9} {mp.nstr(T2,9):>16} {mp.nstr(2*mp.re(J),9):>16} "
          f"{mp.nstr(abs(J),6):>12} {mp.nstr(abs(J)/mp.sqrt(tau),6):>10} {mp.nstr(T2-2*mp.re(J),4):>12}")
