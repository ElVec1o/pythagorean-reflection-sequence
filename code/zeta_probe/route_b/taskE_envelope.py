#!/usr/bin/env python3
"""
Dense phase scan: confirm |T2| <= C sqrt(tau) and find the empirical sup of |T2|/sqrt(tau).
Also confirm the leading-order envelope T2 ~ (sqrt2/36) sqrt(tau) sin W (travel-block constant
from MEMORY: c1_trav = sqrt2/36 = 0.0392837). We use the BULK constant 17 sqrt2/36 too since
the task's T2 may be the bulk one; report both and the actual data-driven sup.
"""
import mpmath as mp
mp.mp.dps = 60

def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb1(q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(1+2*j,q)*prod; prod*=gamma(1+2*j,q)
        if abs(prod)<mp.mpf(10)**(-110) and j>50: break
    return tot

c1 = mp.sqrt(2)/36          # leading T2 amplitude coefficient (per saddle: tau^2 W^3/72 = sqrt2/36 sqrt tau)
print("Dense phase scan of |T2|/sqrt(tau).  T2 = S1 - (1-cos w) - (cos w - cos W).")
print(f"leading coeff c1 = sqrt2/36 = {mp.nstr(c1,10)}")
print(f"{'w-range':>16} {'sup|T2|/sqrtT':>14} {'argmax w':>10} {'sup |sinW| pred':>16}")
# scan in bands of w; within each band sample many phases
bands = [(3,10),(10,20),(20,40),(40,70),(70,110),(110,160)]
gsup = mp.mpf(0)
for lo,hi in bands:
    wv = mp.mpf(lo); sup=mp.mpf(0); argw=wv
    step = mp.mpf(hi-lo)/400
    while wv<=hi:
        tau=2/wv**2; q=mp.e**(-tau); st=mp.sqrt(tau)
        W = wv*mp.e**(-tau/2)
        T2 = Sb1(q)-(1-mp.cos(wv))-(mp.cos(wv)-mp.cos(W))
        r = abs(T2)/st
        if r>sup: sup=r; argw=wv
        wv+=step
    gsup=max(gsup,sup)
    print(f"{('['+str(lo)+','+str(hi)+']'):>16} {mp.nstr(sup,8):>14} {mp.nstr(argw,6):>10} {mp.nstr(c1,6):>16}")
print(f"\nGLOBAL sup_w |T2|/sqrt(tau) over [3,160] = {mp.nstr(gsup,8)}")
print(f"Compare leading c1 = sqrt2/36 = {mp.nstr(c1,8)}  (sup should approach c1 from above as w grows)")
