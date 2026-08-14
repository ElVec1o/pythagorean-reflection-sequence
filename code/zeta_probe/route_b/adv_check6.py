#!/usr/bin/env python3
"""
ADVERSARIAL CHECK 6: properly-resolved sup over a FULL phase cycle at each tau scale.
At small tau, w=sqrt(2/tau) is huge; to sweep one full 2pi of phase we vary tau in a band
[tau0, tau1] chosen so w(tau0)-w(tau1)=2.2pi, and sample densely (>2000 pts).
Goal: get the TRUE sup_w |T2|/sqrt(tau) at each scale and confirm
  (i) it is BOUNDED (the O(sqrt tau) ORDER claim), and
  (ii) it sits slightly ABOVE sqrt2/36 (so the 'sharp bound' is exceeded), settling
       to a limit ~ sqrt2/36 from above.
Fast: T2_direct only.
"""
import mpmath as mp
mp.mp.dps = 90

def setup(tau):
    tau = mp.mpf(tau); q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau,q,w,W
def alpha_q(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_q(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def S1_bulk(q,J=80000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot += alpha_q(1+2*j,q)*prod
        prod *= gamma_q(1+2*j,q)
        if abs(prod)<mp.mpf(10)**(-(mp.mp.dps+10)) and j>50: break
    return tot
def T2_direct(tau):
    tau,q,w,W = setup(tau)
    return S1_bulk(q) - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

C = mp.sqrt(2)/36
print(f"sharp const sqrt2/36 = {mp.nstr(C,12)}")
print(f"{'tau_scale':>12} {'sup|T2|/sqrt(tau)':>20} {'sup/(sqrt2/36)':>16}")
for ts in ['0.02','0.01','0.005','0.002','0.001','0.0005','0.0002']:
    ts = mp.mpf(ts)
    w0 = mp.sqrt(2/ts)
    # choose tau1 so that w(tau1) = w0 - 2.2*pi
    w1 = w0 - mp.mpf('2.3')*mp.pi
    tau1 = 2/w1**2
    N = 3000
    sup=mp.mpf(0)
    for j in range(N+1):
        tau = ts + (tau1-ts)*mp.mpf(j)/N
        r = abs(T2_direct(tau))/mp.sqrt(tau)
        if r>sup: sup=r
    print(f"{float(ts):>12} {mp.nstr(sup,10):>20} {mp.nstr(sup/C,9):>16}")
print("\n(sup BOUNDED across scales => O(sqrt tau) ORDER holds empirically;")
print(" sup/(sqrt2/36) slightly >1 and -> 1 from above => sqrt2/36 = leading coeff, not bound.)")
