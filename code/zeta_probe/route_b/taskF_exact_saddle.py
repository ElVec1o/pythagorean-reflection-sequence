#!/usr/bin/env python3
"""
TASK F -- PART 3: locate the EXACT saddle of the full Lindelof integrand and confirm
it is a single, simple (nondegenerate) interior critical point, as DLMF 2.4.14 / Olver
Thm 4.7.1 require.  The crude s*=iW/2 has a residual Lambda'(s*)=O(1/W); the TRUE saddle
s_hat solves  d/ds[ Lambda(s) + log g_s ] = 0  exactly.  We:
  (1) solve for s_hat by Newton from iW/2,
  (2) confirm (s_hat - iW/2)/(i sqrt(tau)) -> 1/2   (matches foundation y*=W/2+(1/2)sqrt(tau)),
  (3) confirm the TOTAL second derivative Psi''(s_hat) != 0 (nondegenerate),
  (4) confirm Psi''(s_hat) ~ -4/W (the leading curvature),
  (5) confirm the integrand is analytic at s_hat (B has no pole: Im(s_hat) < pi/tau,
      and Re(s_hat)>=0), so the contour deformation is legitimate (H1, H4).
"""
import mpmath as mp
from abelplana_verify import B_exact

mp.mp.dps = 60
I = mp.mpc(0, 1)

def setup(tau):
    tau = mp.mpf(tau); q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau, q, w, W

def logg(s, tau):
    B, _ = B_exact(s, tau)
    return mp.log(1 - mp.e**(-B))

def Psi(s, W, tau):
    # full exponent: Lambda(s) + log g_s,  Lambda = 2 s log W - logGamma(2s+1) + i pi s
    return 2*s*mp.log(W) - mp.loggamma(2*s+1) + I*mp.pi*s + logg(s, tau)

def Psi1(s, W, tau, h=mp.mpf('1e-20')):
    return (Psi(s+h, W, tau) - Psi(s-h, W, tau))/(2*h)
def Psi2(s, W, tau, h=mp.mpf('1e-13')):
    return (Psi(s+h, W, tau) - 2*Psi(s, W, tau) + Psi(s-h, W, tau))/h**2

print("="*84)
print("PART 3 -- EXACT saddle s_hat of the full Lindelof exponent Psi=Lambda+log g")
print("="*84)
print(f"{'tau':>8} {'W':>10} {'Im s_hat':>12} {'(s_hat-iW/2)/(i sqrt tau)':>26} {'Psi2(s_hat)':>22} {'ratio to -4/W':>14}")
for tau in [mp.mpf('0.1'), mp.mpf('0.02'), mp.mpf('0.005'), mp.mpf('0.001')]:
    tau, q, w, W = setup(tau)
    s = I*W/2
    # Newton on Psi1 = 0
    for _ in range(40):
        f = Psi1(s, W, tau)
        # numerical derivative of Psi1 (= Psi2)
        d = Psi2(s, W, tau)
        step = f/d
        s = s - step
        if abs(step) < mp.mpf('1e-40'):
            break
    shat = s
    shift = (shat - I*W/2)/(I*mp.sqrt(tau))   # should -> 1/2
    p2 = Psi2(shat, W, tau)
    ratio = p2/(-4/W)
    # analyticity check: Im(s_hat) vs pole pi/tau, Re(s_hat) sign
    poledist = mp.pi/tau - abs(mp.im(shat))
    print(f"{float(tau):>8} {float(W):>10.4f} {mp.nstr(mp.im(shat),8):>12} {mp.nstr(shift,10):>26} {mp.nstr(p2,6):>22} {mp.nstr(ratio,7):>14}")
    print(f"         |Psi1(s_hat)|={mp.nstr(abs(Psi1(shat,W,tau)),3)} (->0 confirms saddle)   "
          f"Re(s_hat)={mp.nstr(mp.re(shat),4)} (>=0, in analytic region)   "
          f"dist to pole pi/tau={mp.nstr(poledist,4)} (>0: B analytic at s_hat)")
