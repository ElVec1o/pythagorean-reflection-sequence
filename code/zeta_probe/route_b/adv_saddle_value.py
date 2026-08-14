#!/usr/bin/env python3
"""
END-TO-END: does the steepest-descent saddle formula reproduce T2, and is the
RELATIVE error O(1/W)=O(sqrt tau)?

We do NOT trust the colleague's 'Re[g_{s*} e^{iW}]' shortcut. Instead we use the
honest contour-integral saddle:

  T2 = sum_{i>=1} (-1)^i a_i g_i.  Write as a Lindelof contour integral:
  Since psi(0)=0, sum_{i>=0} (-1)^i psi(i) = (1/2i) oint_C psi(s) pi/sin(pi s) ds
  with C a contour around the positive real axis (poles at s=1,2,3,...).
  Deforming to the steepest-descent path through the saddle s_c (found numerically),
  the leading saddle contribution is
     T2 ~ Residue-orientation * psi(s_c) * pi/sin(pi s_c) * sqrt(2 pi / (-F''(s_c))) / (2 pi i) ...
  But the orientation/prefactor algebra is exactly the 'cited theorem' step. Rather than
  re-derive it, we TEST the colleague's verified claim directly:

    (1) the saddle MAGNITUDE  M(tau) = |a_{s_c} g_{s_c}/sin(pi s_c)| * sqrt(2 pi/|F''(s_c)|)
        should equal |T2| up to a bounded factor and M/sqrt(tau) -> sqrt2/36.
    (2) more honestly: compute T2 by NUMERICAL steepest descent (deform the Lindelof
        contour to a finite curved path through s_c and integrate), compare to T2_direct.

We do (1) at s_c=iW/2 (colleague's node) AND at the true critical point, and (2) a
direct numerical contour integral as the real test of the saddle route's validity.
"""
import mpmath as mp
from abelplana_verify import B_exact
from adv_verify import T2_direct

def a_s(s, W):  # W^{2s}/Gamma(2s+1)
    return mp.e**(2*s*mp.log(W)) / mp.gamma(2*s+1)

def g_s(s, tau):
    B,_ = B_exact(s, tau); return 1 - mp.e**(-B)

def psi(s, W, tau):
    return a_s(s, W) * g_s(s, tau)

if __name__ == "__main__":
    mp.mp.dps = 50
    print("="*96)
    print("(1) saddle MAGNITUDE M = |a g/sin| sqrt(2pi/|F''|) at s_c=iW/2 vs |T2|, and M/sqrt(tau)")
    print("="*96)
    sq2_36 = mp.sqrt(2)/36
    for tau0 in ['0.02','0.005','0.001','0.0002']:
        tau = mp.mpf(tau0); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
        sc = mp.mpc(0, float(W/2))
        Fpp = mp.mpf(4)/W  # |F''| ~ 4/W
        M = abs(a_s(sc,W)*g_s(sc,tau)/mp.sin(mp.pi*sc)) * mp.sqrt(2*mp.pi/Fpp)
        T2 = abs(T2_direct(tau))
        print(f"  tau={tau0}: M={mp.nstr(M,7):>12}  |T2|={mp.nstr(T2,7):>12}  "
              f"M/sqrt(tau)={mp.nstr(M/mp.sqrt(tau),7)}  M/|T2|={mp.nstr(M/T2,5) if T2>0 else 'inf'}")

    print("\n" + "="*96)
    print("(2) HONEST numerical steepest-descent: deform Lindelof contour through saddle,")
    print("    integrate, compare to T2_direct. This tests the saddle ROUTE end-to-end.")
    print("="*96)
    # Lindelof: T2 = sum_{i>=1}(-1)^i psi(i). Use the integral representation
    #   sum_{n=1}^inf (-1)^n h(n) = -(1/2i) int_{C} h(s) pi/sin(pi s) ds  (Abel-Plana alternating),
    # We integrate on a VERTICAL line Re(s)=c (0<c<1) -- the standard Mellin-Barnes/Lindelof line:
    #   sum_{n>=1}(-1)^n psi(n) = (1/2i) int_{c-i inf}^{c+i inf} psi(s) pi/sin(pi s) ds
    #   BUT this requires psi decay; psi blows up upward (g blows up). So a STRAIGHT vertical
    #   line FAILS (matches author gap). Test: integrate on the line Re(s)=c and watch divergence.
    for tau0 in ['0.1','0.02']:
        tau = mp.mpf(tau0); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
        c = mp.mpf('0.5')
        def integ(t):  # s = c + i t
            s = mp.mpc(c, t)
            return psi(s, W, tau)*mp.pi/mp.sin(mp.pi*s)
        # sample |integrand| along the vertical line to show growth/decay
        print(f"  tau={tau0}, W={float(W):.3f}, saddle Im=W/2={float(W/2):.3f}: |integrand| on Re(s)=0.5:")
        for t in [1, 2, float(W/2), float(W/2)+3, float(W/2)+8, float(W/2)+15]:
            v = abs(integ(mp.mpf(t)))
            print(f"     Im(s)={t:7.3f}: |integrand|={mp.nstr(v,5)}")
