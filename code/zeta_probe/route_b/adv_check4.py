#!/usr/bin/env python3
"""
ADVERSARIAL CHECK 4: is the growing partial integral a QUADRATURE ARTIFACT or REAL?
Use high-accuracy oscillatory quadrature (mp.quadosc-style: integrate between the
phase nodes where sin Phi = 0).  Compare against the original module's T2_abelplana
choice (ymax ~ y*+25).  Also directly tabulate the integrand to confirm |A(y)| growth
vs 1/Phi' so we can judge conditional convergence honestly.
"""
import sys
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk, T2_abelplana

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

tau = mp.mpf('0.1')
tau,q,w,W = setup(tau)
ystar = W/2; pole = mp.pi/tau
T2d = T2_direct(tau)
print(f"tau={float(tau)}  ystar={float(ystar):.4f}  pole={float(pole):.4f}")
print(f"T2_direct = {mp.nstr(T2d,12)}")
sys.stdout.flush()

# (1) original module's representation value (its chosen ymax ~ y*+25, NOT to pole)
val, ys, ym = T2_abelplana(tau)
print(f"\nT2_abelplana (module, ymax={float(ym):.2f}) = {mp.nstr(val,12)}  |vs direct|={mp.nstr(abs(val-T2d),4)}")
sys.stdout.flush()

# (2) integrate to a sequence of upper limits with FINE adaptive nodes (subdivide each unit)
f = lambda y: integrand(y, W, tau)
def fine_integral(Y, step=mp.mpf('0.5')):
    nodes = []
    yv = mp.mpf(0)
    while yv < Y:
        nodes.append(yv); yv += step
    nodes.append(Y)
    return mp.quad(f, nodes)

print(f"\nFINE cumulative integral (0.5-wide panels):")
print(f"   {'Y':>8} {'int_0^Y':>16} {'int-T2direct':>14}")
for Yf in ['5','10','15','20','25','30']:
    Y = mp.mpf(Yf)
    if Y >= pole: continue
    v = fine_integral(Y)
    print(f"   {float(Y):>8.2f} {mp.nstr(v,10):>16} {mp.nstr(v-T2d,4):>14}")
    sys.stdout.flush()

# (3) integrand magnitude & local oscillation across the range
print(f"\n   y, |integrand|, 1/sinh(pi y) factor implicit:")
for y in [mp.mpf(v) for v in ['2','5','10','15','20','25','29','30','31']]:
    if y >= pole: continue
    ig = integrand(y, W, tau)
    s=I*y; B,_=B_exact(s,tau); g=1-mp.e**(-B)
    A = abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
    print(f"   y={float(y):>6.2f}  integrand={mp.nstr(ig,6):>14}  A(y)={mp.nstr(A,6):>12}  ReB={mp.nstr(mp.re(B),5)}")
    sys.stdout.flush()
print("DONE")
