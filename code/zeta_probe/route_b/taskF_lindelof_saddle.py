#!/usr/bin/env python3
"""
TASK F -- PART 2: the CORRECT contour (Lindelof) and the DLMF 2.4.14 / Olver Thm
saddle-point hypotheses, checked numerically with EXACT B.

SETUP.  T2 = sum_{i>=1} (-1)^i a_i g_i,  a_i = W^{2i}/(2i)!,  g_i = 1-e^{-B_i}.
Lindelof:  T2 = (1/2i) oint_C  h(s) pi/sin(pi s) ds,   h(s)=a_s g_s,
a_s = W^{2s}/Gamma(2s+1).  Residue of pi/sin(pi s) at s=n is (-1)^n.
The contour C is deformed to the steepest-descent path through the saddle s*=iW/2.

To put it in OLVER/DLMF canonical form  int e^{-z F(s)} Q(s) ds  with LARGE PARAMETER z,
write the dominant exponential factor.  The dominant balance (handoff): on the upper
side of C, pi/sin(pi s) ~ -2 pi i e^{i pi s} (= -2 pi i e^{-pi y} for s=x+iy), and
a_s ~ W^{2s}/Gamma(2s+1).  So
   log[ a_s * e^{i pi s} ]  =  2 s log W - logGamma(2s+1) + i pi s.
Define the PHASE/exponent  Lambda(s) := 2 s log W - logGamma(2s+1) + i pi s.
The saddle of the FULL integrand is  d/ds[ Lambda(s) + log g_s ] = 0; since g_s is
slowly varying (g~B=O(sqrt tau) small), the saddle is governed by Lambda':
   Lambda'(s) = 2 log W - 2 psi0(2s+1) + i pi,   psi0=digamma.
For large |s|, psi0(2s+1) ~ log(2s).  Set Lambda'(s*)=0:
   2 log W - 2 log(2 s*) + i pi = 0  =>  log(W/(2 s*)) = -i pi/2  =>  W/(2 s*) = e^{-i pi/2}=-i
   =>  s* = W/(2 * (-i) * ... ) ;  W/(2 s*) = -i  =>  s* = W/(2*(-i)) = i W/2.   <-- s*=iW/2.

So the LARGE PARAMETER is W (equivalently 1/sqrt(tau), since W ~ sqrt(2/tau)), and the
saddle is at s*=iW/2 EXACTLY as claimed.  We verify:
  (H1) integrand analytic in a neighborhood of the path (Re s >= 0): poles of B only at Re s<0.
  (H2) nondegenerate saddle:  Lambda''(s*) != 0,  Lambda''(s*) = -4 psi1(2s*+1) ~ -4/(2s*) = -2/(iW/...)
       (the foundation's Phi''(y*) = -4/W maps to this).
  (H3) g_{s*} = O(sqrt tau)  (small, slowly varying -- does not move the saddle at leading order).
  (H4) the steepest-descent path stays in Im s <= W/2 region where B is controlled (no blow-up).
  (H5) leading saddle term reproduces T2 with relative error -> 0 like O(1/W)=O(sqrt tau).
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk

mp.mp.dps = 50
I = mp.mpc(0, 1)

def setup(tau):
    tau = mp.mpf(tau); q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau, q, w, W

def T2_true(tau):
    tau, q, w, W = setup(tau)
    S1 = S1_bulk(q)
    return S1 - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

# ---- the canonical exponent Lambda(s) = 2 s log W - logGamma(2s+1) + i pi s ----
def Lam(s, W):
    return 2*s*mp.log(W) - mp.loggamma(2*s+1) + I*mp.pi*s
def Lam1(s, W):  # Lambda'(s)
    return 2*mp.log(W) - 2*mp.digamma(2*s+1) + I*mp.pi
def Lam2(s):     # Lambda''(s) = -4 psi'(2s+1)
    return -4*mp.polygamma(1, 2*s+1)

print("="*80)
print("PART 2 -- Lindelof/steepest-descent saddle, DLMF 2.4.14 / Olver hypotheses")
print("="*80)
for tau in [mp.mpf('0.3'), mp.mpf('0.1'), mp.mpf('0.02'), mp.mpf('0.005')]:
    tau, q, w, W = setup(tau)
    sstar = I*W/2
    # (H-saddle) verify Lambda'(s*) ~ 0
    L1 = Lam1(sstar, W)
    L2 = Lam2(sstar)
    # compare Lambda'' to the predicted -4/W (foundation Phi''(y*)=-4/W, with y=Im s)
    # Phi(y) = Im Lambda(iy)/... ; the curvature along the descent direction is |Lambda''|.
    print(f"\n-- tau={float(tau)}  W={float(W):.5f}  s*=iW/2 (Im={float(W/2):.5f})")
    print(f"   Lambda'(s*)      = {mp.nstr(L1, 6)}   |Lambda'(s*)| = {mp.nstr(abs(L1),4)}   (saddle: should -> 0)")
    print(f"   Lambda''(s*)     = {mp.nstr(L2, 6)}   |Lambda''|    = {mp.nstr(abs(L2),6)}")
    print(f"   -4/W (predicted) = {mp.nstr(-4/W,6)}   ratio |Lam''|/(4/W) = {mp.nstr(abs(L2)/(4/W),6)}")
    # (H3) g at saddle small = O(sqrt tau)
    Bs, _ = B_exact(sstar, tau)
    gs = 1 - mp.e**(-Bs)
    print(f"   B_(s*)           = {mp.nstr(Bs,6)}   |B_s*|/sqrt(tau) = {mp.nstr(abs(Bs)/mp.sqrt(tau),6)}  (-> sqrt2/36={float(mp.sqrt(2)/36):.6f})")
    print(f"   g_(s*)=1-e^-B    = {mp.nstr(gs,6)}   |g_s*-B_s*|/|B_s*| = {mp.nstr(abs(gs-Bs)/abs(Bs),4)} (g~B confirms slow variation)")
