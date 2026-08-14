#!/usr/bin/env python3
"""
RIGOROUS closed-contour residue test.

Claim: (1/(2 pi i)) oint_C psi(s) [pi/sin(pi s)] ds = sum_{n in C} (-1)^n psi(n),
psi(s)=W^{2s} g_s/Gamma(2s+1), poles of pi/sin(pi s) at integers with residue (-1)^n.

We pick a closed rectangle that encloses n=1,2,...,M, lying ENTIRELY in the region where
psi is analytic and computable. To AVOID the upward blowup of g, we keep the rectangle's
top edge at a modest height H_top and its right edge at Re=R=M+0.5. Because psi has NO
poles, the contour integral must equal the enclosed residue sum EXACTLY -- regardless of
the height; the integral over the (non-negligible) top/sides simply accounts for the
remaining tail of the alternating series. So this is a clean consistency check of:
  (i) psi analytic in the rectangle (no spurious poles), and
  (ii) the B_exact continuation is correct off the real axis.

If it matches the residue sum to high precision, the contour REPRESENTATION is validated.
(The asymptotic O(sqrt tau) bound is a SEPARATE, harder claim about the SIZE.)
"""
import mpmath as mp
from abelplana_verify import B_exact
from adv_verify import B_int

def h(s, W, tau):
    B,_ = B_exact(s, tau); g = 1 - mp.e**(-B)
    a = mp.e**(2*s*mp.log(W))/mp.gamma(2*s+1)
    return a*g*mp.pi/mp.sin(mp.pi*s)

def closed_integral(tau0, M, Htop, dps=50):
    mp.mp.dps=dps
    tau=mp.mpf(tau0); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    c0=mp.mpf('0.5'); R=mp.mpf(M)+mp.mpf('0.5'); H=mp.mpf(Htop)
    f=lambda s: h(s,W,tau)
    # Rectangle corners CCW: (c0,-H)->(R,-H)->(R,H)->(c0,H)->(c0,-H)
    def seg(p0, p1, n=None):
        # integrate f along straight segment p0->p1
        L=p1-p0
        g=lambda t: f(p0+t*L)*L
        return mp.quad(g, [0,0.25,0.5,0.75,1])
    A=mp.mpc(c0,-H); Bc=mp.mpc(R,-H); C=mp.mpc(R,H); D=mp.mpc(c0,H)
    I = seg(A,Bc)+seg(Bc,C)+seg(C,D)+seg(D,A)
    val = I/(2*mp.pi*mp.mpc(0,1))
    # residue sum enclosed: n=1..M
    resn = mp.mpf(0)
    for n in range(1,M+1):
        Bi=B_int(n,tau); g=1-mp.e**(-Bi); a=W**(2*n)/mp.factorial(2*n)
        resn += (-1)**n * a*g
    return val, resn

if __name__ == "__main__":
    print("="*90)
    print("Closed-contour integral / (2 pi i) vs enclosed residue sum  (validates representation)")
    print("="*90)
    for t0, M, H in [('0.1', 8, 6), ('0.1', 12, 8), ('0.02', 14, 10)]:
        val, resn = closed_integral(t0, M, H)
        print(f"  tau={t0}, M={M}, Htop={H}:")
        print(f"     contour/(2pi i) = {mp.nstr(val,14)}")
        print(f"     residue sum n=1..M = {mp.nstr(resn,14)}")
        print(f"     |diff| = {mp.nstr(abs(val-resn),4)}")
