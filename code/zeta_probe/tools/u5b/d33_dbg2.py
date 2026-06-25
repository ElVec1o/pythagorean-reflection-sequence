#!/usr/bin/env python3
import mpmath as mp
mp.mp.dps=30
def qpoch_inf(a,p,tol=mp.mpf(10)**(-32),NM=5000):
    r=mp.mpc(1);ai=a
    for i in range(NM):
        r*=(1-ai);ai*=p
        if abs(ai)<tol:break
    return r
def S_in_closed(x,c,p,N=300):
    e=mp.e**(1j*x);poch=(1-p);t=mp.mpc(1)/poch;s=t
    for n in range(1,N):
        t=t*(-c*e)*(1-p**n)/(1-p**(n+1));s+=t
        if abs(t)<mp.mpf(10)**(-32) and n>10:break
    return s
def S_in_brute(x,c,p,J=2000):
    e=mp.e**(1j*x);s=mp.mpc(0)
    for j in range(J):
        pj=p**j
        if pj<mp.mpf(10)**(-32):break
        s+=pj/qpoch_inf(-c*pj*e,p)
    return s
tau=mp.mpf("0.2");q=mp.e**(-tau);p=q*q;c=2*q**2*(1-q)
for x in [mp.mpf("0.0"),mp.mpf("0.5")]:
    a=S_in_closed(x,c,p);b=S_in_brute(x,c,p)
    print("x=",mp.nstr(x,3)," closed=",mp.nstr(a,12)," brute=",mp.nstr(b,12)," diff=",mp.nstr(a-b,4),flush=True)
