#!/usr/bin/env python3
"""
ADVERSARIAL CHECK 3: where does the Abel-Plana integral actually represent T2,
and how does the integrand behave across (0, pole)?  Unbuffered, faster KMAX.

We integrate the real-axis integrand over (0, Y) for a SEQUENCE of upper limits Y,
to see whether the integral STABILIZES at T2 (genuine convergence) or whether
pushing Y toward the pole pi/tau destroys it.  This tells us what "the integral the
theorem acts on" really is.
"""
import sys
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk

mp.mp.dps = 40
I = mp.mpc(0, 1)

def setup(tau):
    tau = mp.mpf(tau); q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau, q, w, W

def T2_direct(tau):
    tau,q,w,W = setup(tau)
    return S1_bulk(q) - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

def integrand(y, W, tau):
    if y == 0: return mp.mpf(0)
    s = I*y
    B,_ = B_exact(s, tau)
    g = 1-mp.e**(-B)
    psi = mp.e**(2*s*mp.log(W)) * g / mp.gamma(2*s+1)
    return -mp.im(psi)/mp.sinh(mp.pi*y)

for tau in [mp.mpf('0.1'), mp.mpf('0.05')]:
    tau,q,w,W = setup(tau)
    ystar = W/2; pole = mp.pi/tau
    T2d = T2_direct(tau)
    print(f"\n{'='*70}\ntau={float(tau)}  ystar={float(ystar):.4f}  pole={float(pole):.4f}  T2_direct={mp.nstr(T2d,10)}")
    sys.stdout.flush()
    f = lambda y: integrand(y, W, tau)
    # cumulative integral to increasing Y, as multiples of ystar (and toward pole)
    Ys = [ystar*mp.mpf(m) for m in ['1','2','3','4','6']]
    Ys += [pole*mp.mpf(fr) for fr in ['0.5','0.8','0.95','0.99']]
    Ys = sorted(set([y for y in Ys if y < pole]))
    prev = mp.mpf(0); acc = mp.mpf(0); a = mp.mpf(0)
    print(f"   {'Y':>10} {'Y/ystar':>8} {'int_0^Y':>16} {'int-T2direct':>14}")
    nodes = [mp.mpf(0)] + Ys
    for j in range(1, len(nodes)):
        lo, hi = nodes[j-1], nodes[j]
        # subdivide near saddle
        mid = (lo+hi)/2
        seg = mp.quad(f, [lo, mid, hi])
        acc += seg
        print(f"   {float(hi):>10.3f} {float(hi/ystar):>8.2f} {mp.nstr(acc,10):>16} {mp.nstr(acc-T2d,4):>14}")
        sys.stdout.flush()
print("\nDONE")
