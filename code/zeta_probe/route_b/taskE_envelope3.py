#!/usr/bin/env python3
"""High-precision (dps=200) check of the envelope at large w. Confirm sup -> sqrt2/36."""
import mpmath as mp
mp.mp.dps = 200

def phi(y): return mp.log(mp.sinh(y/2)/(y/2))
def Bint(n, tau):
    s=mp.mpf(0); pt=phi(tau)
    for x in range(n):
        s += phi((2*x+2)*tau)+phi((2*x+1)*tau)-pt
    return s
def T2_psi(tau):
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    tot=mp.mpf(0)
    for i in range(1,int(W)+160):
        g=1-mp.e**(-Bint(i,tau))
        t=(-1)**i*W**(2*i)*g/mp.factorial(2*i)
        tot+=t
        if i>int(W)+40 and abs(t)<mp.mpf(10)**(-(mp.mp.dps-10)): break
    return tot,w,W

c1=mp.sqrt(2)/36
print(f"dps={mp.mp.dps}.  sup |T2|/sqrt(tau) per band.  c1=sqrt2/36={mp.nstr(c1,12)}")
print(f"{'band':>14} {'sup|T2|/sqrtT':>16} {'argmax w':>10}")
gsup=mp.mpf(0)
for lo,hi,n in [(110,160,40),(160,220,30),(220,300,25)]:
    wv=mp.mpf(lo); sup=mp.mpf(0); argw=wv; step=mp.mpf(hi-lo)/n
    while wv<=hi:
        tau=2/wv**2
        T2,w,W=T2_psi(tau); st=mp.sqrt(tau)
        r=abs(T2)/st
        if r>sup: sup=r; argw=wv
        wv+=step
    gsup=max(gsup,sup)
    print(f"{('['+str(lo)+','+str(hi)+']'):>14} {mp.nstr(sup,10):>16} {mp.nstr(argw,6):>10}")
print(f"\nsup over [110,300] (dps=200) = {mp.nstr(gsup,10)}  vs c1={mp.nstr(c1,10)}")
