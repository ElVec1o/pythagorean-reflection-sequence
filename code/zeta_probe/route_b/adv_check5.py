#!/usr/bin/env python3
"""
ADVERSARIAL CHECK 5: does the SHARP constant sqrt2/36 actually BOUND |T2|/sqrt(tau)?
Sweep the phase w over a full cycle at several tau scales using ONLY T2_direct
(fast: S1_bulk + cos terms, no B_exact, no integral).  Report sup_w |T2|/sqrt(tau).
The claim: sup -> sqrt2/36 = 0.0392837 and |T2| <= C sqrt(tau).
If the realized sup EXCEEDS sqrt2/36, then sqrt2/36 is NOT an upper bound (only the
leading asymptotic coefficient), and the o(1) correction is POSITIVE -> the stated
'|T2| <= (sqrt2/36) sqrt(tau)(1+o(1))' is only an asymptotic equality, not a finite bound.
"""
import mpmath as mp
mp.mp.dps = 80

def setup(tau):
    tau = mp.mpf(tau); q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau,q,w,W

def alpha_q(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_q(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def S1_bulk(q,J=60000):
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
print(f"sharp constant sqrt2/36 = {mp.nstr(C,12)}")
print(f"{'tau_center':>12} {'sup|T2|/sqrt(tau)':>20} {'sup/(sqrt2/36)':>16} {'argmax tau':>14}")
for tc in ['0.01','0.002','0.001','0.0005','0.0002']:
    tc = mp.mpf(tc)
    # sweep tau over a band so w=sqrt(2/tau) covers > 2pi of phase
    # dw/dtau = -sqrt(2)/(2) tau^{-3/2}; to cover 2pi need Delta tau ~ 2pi * 2/sqrt2 * tau^{3/2}/...
    # just sweep +-4% with many points; for small tau this covers many cycles
    sup=mp.mpf(0); arg=None
    N=400
    lo=tc*mp.mpf('0.97'); hi=tc*mp.mpf('1.03')
    for j in range(N+1):
        tau = lo+(hi-lo)*mp.mpf(j)/N
        r = abs(T2_direct(tau))/mp.sqrt(tau)
        if r>sup: sup=r; arg=float(tau)
    print(f"{float(tc):>12} {mp.nstr(sup,10):>20} {mp.nstr(sup/C,8):>16} {arg:>14.6g}")
print("\nIf sup/(sqrt2/36) > 1, the realized peak EXCEEDS the claimed sharp constant")
print("=> sqrt2/36 is the leading coeff, NOT a finite-tau upper bound (o(1) is +).")
