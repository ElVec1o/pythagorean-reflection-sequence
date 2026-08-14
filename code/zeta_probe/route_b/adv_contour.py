#!/usr/bin/env python3
"""
Adversarial check of the SADDLE-ROUTE structural claims:

CLAIM (a): the summand a_s g_s is analytic in Re(s)>=0 (poles of B only at Re(s)<0).
CLAIM (b): on the steepest-descent path through s*=iW/2 that stays Im(s)<=W/2, g_s
           is CONTROLLED (does not blow up) -- the blowup Re(B_iy)->-inf is only for
           Im(s) >> W/2 (the imaginary-axis tail).
CLAIM (c): the Abel-Plana real-axis integral is genuinely DIVERGENT (author-admitted gap 1):
           Re(B_iy) -> -inf, A(y)=|g_iy| sqrt(coth/...) blows up.

We test (b) and (c) directly by evaluating B at s = sigma + i*eta on a grid, using the
colleague's analytic continuation B_exact (which we already cross-validated at integer s).
Independent sanity: also recompute B at a few complex points from the tau-SERIES where it
converges (|s| < pi/tau), to confirm B_exact is right OFF the real axis too.
"""
import mpmath as mp
from abelplana_verify import B_exact

def B_tau_series(s, tau, NMAX=40):
    """B_s = sum_{n>=1} f_n tau^{2n} Q_n(s-1), f_n=[y^{2n}]phi, Q_n Faulhaber.
    Valid for |s| < pi/tau. f_n from phi(y)=sum_{k} log(1+(y/2pik)^2):
      phi(y) = -sum_{n>=1} (-1)^n/n (y/2pi)^{2n} zeta(2n)
             => f_n = [y^{2n}]phi = -(-1)^n/n * zeta(2n)/(2pi)^{2n}.
    Q_n(m) = sum_{i=0}^m [(2i+2)^{2n}+(2i+1)^{2n}-1], here m=s-1 (analytic via Faulhaber).
    Easier: B_s = sum_{x=0}^{s-1} b(x); use the closed Faulhaber sum symbolically is heavy.
    Instead we just verify at INTEGER s via direct b-sum (already have) and at small complex
    s by analytic Faulhaber. To keep it light, validate B_exact via the integer route (done)
    and via B(-iy)=conj(B(iy)). Here we only PROBE magnitudes with B_exact.
    """
    raise NotImplementedError

if __name__ == "__main__":
    mp.mp.dps = 50
    tau = mp.mpf('0.1')
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    print(f"tau={float(tau)}, W={float(W):.4f}, W/2={float(W/2):.4f}, pi/tau={float(mp.pi/tau):.2f}")
    print("="*84)
    print("(c) ON THE IMAGINARY AXIS s=iy: Re(B_iy) and |g_iy|=|1-e^{-B}| -- does it blow up?")
    print("="*84)
    for y in [5, 10, 20, 30, 40, 50, 70]:
        s = mp.mpc(0, y)
        B,_ = B_exact(s, tau)
        g = 1 - mp.e**(-B)
        print(f"  y={y:3d}: Re(B)={mp.nstr(mp.re(B),6):>12}  |B|={mp.nstr(abs(B),5):>10}  "
              f"|g_iy|={mp.nstr(abs(g),5):>12}")

    print("\n" + "="*84)
    print("(b) ON A CURVED CONTOUR staying Im(s)<=W/2: s = sigma + i*W/2, sigma>=0 increasing.")
    print("    Does g stay controlled (NOT blow up)?  (the saddle is at sigma=0, Im=W/2.)")
    print("="*84)
    ystar = W/2
    for sigma in [mp.mpf(0), mp.mpf('1'), mp.mpf('2'), mp.mpf('4'), mp.mpf('8')]:
        s = mp.mpc(sigma, float(ystar))
        B,_ = B_exact(s, tau)
        g = 1 - mp.e**(-B)
        print(f"  s={mp.nstr(s,6)}: Re(B)={mp.nstr(mp.re(B),6):>12}  |g|={mp.nstr(abs(g),6):>12}")

    print("\n" + "="*84)
    print("(b') Steepest-descent direction from s* = iW/2: probe a few rays. The claim is the")
    print("     descent path turns AWAY from the imaginary axis (toward larger Re s, Im<=W/2).")
    print("="*84)
    # Sample the function magnitude |a_s g_s/sin(pi s)| around s* to see the descent geometry.
    def logmag(s):
        B,_ = B_exact(s, tau); g = 1-mp.e**(-B)
        # a_s = W^{2s}/Gamma(2s+1)
        la = 2*s*mp.log(W) - mp.loggamma(2*s+1)
        val = la + mp.log(g) - mp.log(mp.sin(mp.pi*s))
        return mp.re(val)
    s0 = mp.mpc(0, float(ystar))
    base = logmag(s0)
    print(f"  log|F| at s*=iW/2: {mp.nstr(base,8)}")
    import cmath
    for ang_deg in [0, 30, 45, 60, 90, 120, 135, 150, 180, -30, -45, -90]:
        d = 0.5*mp.e**(mp.mpc(0,1)*mp.radians(ang_deg))
        try:
            v = logmag(s0+d) - base
            print(f"    dir {ang_deg:4d} deg: Delta log|F| = {mp.nstr(v,6)}  "
                  f"{'(descent)' if mp.re(v)<0 else '(ASCENT)'}")
        except Exception as e:
            print(f"    dir {ang_deg:4d} deg: err {e}")
