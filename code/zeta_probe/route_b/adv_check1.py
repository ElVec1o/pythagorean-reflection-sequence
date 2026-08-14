#!/usr/bin/env python3
"""
ADVERSARIAL CHECK 1 (independent).
Goal: test the THREE load-bearing claims independently of the colleague's framing.

(A) Does the Abel-Plana real-axis integral actually reproduce T2_direct?
    (validate the representation before bounding it)
(B) Tail behaviour: is the real-axis integrand integrable up to the pole y=pi/tau?
    Does the integral T2 = -int_0^Y Im psi(iy)/sinh(pi y) dy converge as Y -> pi/tau ?
    The colleague says it DIVERGES (Re B -> -inf). Verify which side of the truth that is:
    we need the *integrand* (which carries 1/sinh(pi y) ~ 2 e^{-pi y}) not just A(y).
(C) Compare T2_direct against the *truncated* integral at window edge Y0 = y*+K sqrt(W).
    If truncation already reproduces T2 to O(tau), the tail repair is at least empirically OK.
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk

mp.mp.dps = 50
I = mp.mpc(0, 1)

def setup(tau):
    tau = mp.mpf(tau); q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau, q, w, W

def T2_direct(tau):
    tau, q, w, W = setup(tau)
    S1 = S1_bulk(q)
    return S1 - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

def psi_iy(y, W, tau):
    s = I*y
    B, _ = B_exact(s, tau)
    g = 1 - mp.e**(-B)
    Wp = mp.e**(2*s*mp.log(W))
    return Wp * g / mp.gamma(2*s+1)

def integrand(y, W, tau):
    if y == 0: return mp.mpf(0)
    return -mp.im(psi_iy(y, W, tau))/mp.sinh(mp.pi*y)

# magnitude of the integrand (to see tail growth/decay)
def integrand_mag(y, W, tau):
    s = I*y
    B,_ = B_exact(s, tau)
    g = 1-mp.e**(-B)
    # |psi(iy)/sinh(pi y)| = |g| sqrt(coth(pi y)/(pi y))  (derived in context)
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))

print("="*90)
print("(A) Abel-Plana representation vs T2_direct, AND (C) truncated-integral comparison")
print("="*90)
for tau in [mp.mpf('0.3'), mp.mpf('0.1'), mp.mpf('0.05')]:
    tau, q, w, W = setup(tau)
    ystar = W/2
    pole = mp.pi/tau
    T2d = T2_direct(tau)
    # full integral up to just below the pole
    Yfull = min(float(ystar)*3+30, float(pole)*0.97)
    f = lambda y: integrand(y, W, tau)
    pts = [mp.mpf(0), ystar/2, ystar, ystar*mp.mpf('1.5'), 2*ystar, mp.mpf(Yfull)]
    pts = sorted(set(pts))
    Ifull = mp.quad(f, pts)
    # truncated at window edge K sqrt(W)
    K = mp.mpf(4); Y0 = ystar + K*mp.sqrt(W)
    pts2 = [p for p in pts if p < Y0] + [Y0]
    Itrunc = mp.quad(f, sorted(set(pts2)))
    print(f"\n-- tau={float(tau)}  ystar={float(ystar):.4f}  pole pi/tau={float(pole):.3f}  Yfull={Yfull:.3f}")
    print(f"   T2_direct          = {mp.nstr(T2d,12)}")
    print(f"   integral_full      = {mp.nstr(Ifull,12)}   |diff|={mp.nstr(abs(Ifull-T2d),4)}")
    print(f"   integral_trunc(Y0={float(Y0):.2f}) = {mp.nstr(Itrunc,12)}   |diff vs direct|={mp.nstr(abs(Itrunc-T2d),4)}")
    print(f"   |trunc - full|     = {mp.nstr(abs(Itrunc-Ifull),4)}  (tail beyond window contribution)")

print("\n" + "="*90)
print("(B) integrand MAGNITUDE A(y)= |g| sqrt(coth/(pi y)) vs the y -> pole=pi/tau")
print("    Does A(y) -> inf as y -> pi/tau ?  (the pole in B is at |y|=pi/tau via phi(tau) terms)")
print("="*90)
for tau in [mp.mpf('0.1')]:
    tau, q, w, W = setup(tau)
    pole = mp.pi/tau
    print(f"\n-- tau={float(tau)}  pole pi/tau={float(pole):.4f}")
    print(f"   {'y':>10} {'Re B(iy)':>16} {'A(y)=|g|sqrt(coth/piy)':>24} {'|integrand|=A/?':>18}")
    for frac in [mp.mpf('0.5'), mp.mpf('0.8'), mp.mpf('0.9'), mp.mpf('0.95'), mp.mpf('0.99'), mp.mpf('0.999')]:
        y = pole*frac
        s = I*y
        B,_ = B_exact(s, tau)
        g = 1-mp.e**(-B)
        A = abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
        print(f"   {float(y):>10.4f} {mp.nstr(mp.re(B),8):>16} {mp.nstr(A,8):>24}")
