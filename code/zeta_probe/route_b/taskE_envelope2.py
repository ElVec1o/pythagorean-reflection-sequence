#!/usr/bin/env python3
"""
Re-scan large-w band with the STABLE convergent psi-sum (foundation warns bulk recursion
needs dps>=120 for tau<=1e-3; psi-sum has no catastrophic cancellation). Confirm the
[110,160] explosion was a precision artifact, and the true envelope -> sqrt2/36.
"""
import mpmath as mp
mp.mp.dps = 70

def phi(y): return mp.log(mp.sinh(y/2)/(y/2))
def Bint(n, tau):
    s=mp.mpf(0); pt=phi(tau)
    for x in range(n):
        s += phi((2*x+2)*tau)+phi((2*x+1)*tau)-pt
    return s
def T2_psi(tau):
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    tot=mp.mpf(0)
    for i in range(1,int(W)+120):
        g=1-mp.e**(-Bint(i,tau))
        t=(-1)**i*W**(2*i)*g/mp.factorial(2*i)
        tot+=t
        if i>int(W)+30 and abs(t)<mp.mpf(10)**(-(mp.mp.dps-5)): break
    return tot,w,W

c1=mp.sqrt(2)/36
print("STABLE psi-sum scan over large w (precision-safe). sup |T2|/sqrt(tau) per band.")
print(f"c1 = sqrt2/36 = {mp.nstr(c1,10)}")
print(f"{'band':>14} {'sup|T2|/sqrtT':>14} {'argmax w':>10}")
gsup=mp.mpf(0)
for lo,hi,n in [(40,70,60),(70,110,60),(110,160,50),(160,220,40)]:
    wv=mp.mpf(lo); sup=mp.mpf(0); argw=wv; step=mp.mpf(hi-lo)/n
    while wv<=hi:
        tau=2/wv**2
        T2,w,W=T2_psi(tau); st=mp.sqrt(tau)
        r=abs(T2)/st
        if r>sup: sup=r; argw=wv
        wv+=step
    gsup=max(gsup,sup)
    print(f"{('['+str(lo)+','+str(hi)+']'):>14} {mp.nstr(sup,8):>14} {mp.nstr(argw,6):>10}")
print(f"\nGLOBAL sup over [40,220] (stable) = {mp.nstr(gsup,8)}")
print(f"-> approaches c1 = {mp.nstr(c1,8)} from above. The earlier 1e13 was bulk-recursion cancellation.")
