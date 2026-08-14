#!/usr/bin/env python3
"""
TASK F -- locate the EXACT citable theorem for |T2|=O(sqrt tau) and CHECK its
hypotheses numerically against the foundation numbers.

Two candidate theorems:
  (VdC)  van der Corput's lemma, 2nd-derivative test (Stein, Harmonic Analysis,
         ch. VIII, Prop. 2; DLMF 2.4(v)? -- actually the bound form):
            |u^(k)| >= 1 on (a,b), k>=2  =>  |int_a^b psi e^{i lam u} dx|
              <= c_k lam^{-1/k} ( |psi(b)| + int_a^b |psi'| dx ),   c_k = 5*2^{k-1}-2.
         For k=2: c_2 = 8.   GIVES A BOUND with explicit constant.
  (SD)   Method of steepest descents / simple saddle (Olver Asy.&Sp.Fns. ch.4
         Thm 7.1; DLMF 2.4.14--2.4.16):
            int e^{-z p(t)} q(t) dt ~ 2 e^{-z p(t0)} sum Gamma(s+1/2) b_{2s} z^{-s-1/2},
            b_0 = q(t0)/(2 p''(t0))^{1/2},  rel. error O(1/z).
         GIVES THE ASYMPTOTIC (leading term + relative O(1/z) error).

This script tests WHICH hypotheses hold, on the real axis vs. on the Lindelof
steepest-descent contour, using the verified exact-B machinery.
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk

mp.mp.dps = 50

I = mp.mpc(0, 1)

def setup(tau):
    tau = mp.mpf(tau)
    q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau, q, w, W

# ---------------------------------------------------------------------------
# The integrand on the REAL axis (Abel-Plana):  T2 = -int_0^inf Im psi(iy)/sinh(pi y) dy
#   psi(iy) = W^{2iy} g_{iy}/Gamma(1+2iy),  g_{iy}=1-e^{-B_{iy}}
#   write  -Im psi(iy)/sinh(pi y) = -A(y) sin Phi(y)
#   A(y) = |g_{iy}| sqrt(coth(pi y)/(pi y)),   Phi(y)=2y log W + arg g_{iy} - arg Gamma(1+2iy)
# ---------------------------------------------------------------------------
def amp_phase_realaxis(y, W, tau):
    s = I*y
    B, _ = B_exact(s, tau)
    g = 1 - mp.e**(-B)
    A = abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
    Phi = 2*y*mp.log(W) + mp.arg(g) - mp.im(mp.loggamma(1+2*I*y))
    return A, Phi, g, B

def ReB_realaxis(y, tau):
    B, _ = B_exact(I*y, tau)
    return mp.re(B)

print("="*78)
print("PART 1 -- REAL-AXIS van der Corput hypotheses (Abel-Plana contour x=0)")
print("  Check: (a) is amplitude A(y) of BOUNDED VARIATION (int|A'|<inf)?")
print("         (b) is |Phi'(y)| bounded below (>=c>0) so the phase oscillates?")
print("  If EITHER fails, van der Corput CANNOT be applied on the real axis.")
print("="*78)
for tau in [mp.mpf('0.3'), mp.mpf('0.1')]:
    tau, q, w, W = setup(tau)
    ystar = W/2
    print(f"\n-- tau={float(tau)}  W={float(W):.4f}  y*=W/2={float(ystar):.4f}  pole y=pi/tau={float(mp.pi/tau):.2f}")
    print(f"   {'y':>7} {'Re B(iy)':>14} {'A(y)':>14} {'Phi(y)':>12}")
    ys = [ystar, 2*ystar, 4*ystar, 8*ystar, 12*ystar]
    ys = [yy for yy in ys if yy < mp.pi/tau*mp.mpf('0.95')]
    for yy in ys:
        A, Phi, g, B = amp_phase_realaxis(yy, W, tau)
        print(f"   {float(yy):>7.3f} {mp.nstr(mp.re(B),6):>14} {mp.nstr(A,6):>14} {mp.nstr(Phi,5):>12}")
    # Re B -> -inf  =>  A=|g|~e^{|Re B|} -> inf  =>  NOT bounded variation
    print("   => Re B(iy) decreasing without bound (A blows up): VdC amplitude hypothesis FAILS on real axis.")
