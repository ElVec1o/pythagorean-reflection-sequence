#!/usr/bin/env python3
# ROUTE D3.2 -- pin the phase offset  C(tau) := sum_{n>=0} k_n - w  ->  C0 ?
# and decide whether C(tau) has an asymptotic expansion in sqrt(tau) (Poincare).
#
# Euler-Maclaurin:  sum_{n=0}^{inf} f(n) = INT_0^inf f dn + (1/2) f(0) - (1/12) f'(0) + ...
# with f(n)=k_n. INT_0^inf k_n dn: with k_n ~ sqrt(2tau) q^n (+corrections), and exact
# k_n = arccos(cosh(1.5tau) - (1-q)q^{1/2} q^{2n}). Substitute x=q^n, dn=dx/(x ln q):
#   INT_0^1 arccos(cosh(1.5tau)-(1-q)q^{1/2}x^2) dx/(x*(-ln q))  ... = w + corrections.
# The LEADING INT gives w; the +1/2 f(0) = (1/2) k_0 -> (1/2) sqrt(2tau)*... ->0.
# So C0 must come from the INTEGRAL's subleading (the gap between continuum phase and w),
# NOT from EM endpoint (which ->0). Let's just measure C(tau) precisely and Richardson it,
# then test if C(tau)-C0 ~ a sqrt(tau).

import mpmath as mp
mp.mp.dps = 50

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))
def kfun(n, q):
    bn = bcoef(n, q)
    if abs(bn) >= 2: return None
    return mp.acos(bn/2)

def C(tau):
    q = mp.e**(-tau)
    S=mp.mpf(0); n=0
    while True:
        kn=kfun(n,q)
        if kn is None: break
        S+=kn; n+=1
        if n>500000: break
    return S - mp.sqrt(2/tau)

taus=[mp.mpf("0.02")/2**i for i in range(8)]
Cs=[C(t) for t in taus]
print("tau           C=sumk-w            C/?(check const)")
for t,c in zip(taus,Cs):
    print(f"  {mp.nstr(t,5):>10}   {mp.nstr(c,12)}")
print()
# Richardson extrapolate assuming C(tau)=C0 + a*tau^p. First find p from triples.
def expo(i):
    t1,t2,t3=taus[i],taus[i+1],taus[i+2]
    f1,f2,f3=Cs[i],Cs[i+1],Cs[i+2]
    # ratio (f2-f1)/(f3-f2) = (t2^p-t1^p)/(t3^p-t2^p); with t halving, = (1-2^p)/(2^-p? )
    # simpler: assume geometric: (f3-f2)/(f2-f1) = (t3/t2)^p? only if C0 cancels: it does in differences
    r=(f3-f2)/(f2-f1)
    # t halves each step so t3/t2=1/2 => r=(1/2)^p => p=log(r)/log(1/2)
    return mp.log(r)/mp.log(mp.mpf("0.5")), r
print("local exponent p of (C - C0) from successive differences (C(tau)=C0+a tau^p):")
for i in range(len(taus)-2):
    p,r=expo(i)
    print(f"  tau~{mp.nstr(taus[i],4)}: p={mp.nstr(p,6)}  (diff ratio {mp.nstr(r,5)})")
print()
# extrapolate C0 with p found (~0.5?). Use pairwise C0=(f1 t2^p - f2 t1^p)/(t2^p-t1^p)
def extrap(p):
    out=[]
    for i in range(len(taus)-1):
        t1,t2=taus[i],taus[i+1]; f1,f2=Cs[i],Cs[i+1]
        C0=(f1*t2**p - f2*t1**p)/(t2**p - t1**p)
        out.append(C0)
    return out
for p in [mp.mpf("0.5"), mp.mpf("1.0")]:
    ext=extrap(p)
    print(f"C0 extrap (assume p={float(p)}):", [mp.nstr(x,10) for x in ext[-4:]])
print()
print("candidate closed forms for C0:")
for name,val in [("-3pi/4",-3*mp.pi/4),("-pi",-mp.pi),("-3pi/4+? ",-3*mp.pi/4),
                 ("-2.356(=-3pi/4)",-3*mp.pi/4),("-(pi - 1)? ",-(mp.pi-1)),
                 ("-3pi/4 - small","")]:
    if val!="":
        print(f"   {name} = {mp.nstr(val,10)}")
# Richardson (2-pt) on p=0.5 series for a cleaner C0
print()
ext=extrap(mp.mpf("0.5"))
# second Richardson: these still have residual; do Aitken
def aitken(seq):
    out=[]
    for i in range(len(seq)-2):
        d1=seq[i+1]-seq[i]; d2=seq[i+2]-seq[i+1]
        if d2-d1!=0:
            out.append(seq[i]-d1*d1/(d2-d1))
    return out
ait=aitken(ext)
print("Aitken on p=0.5 extrap:", [mp.nstr(x,12) for x in ait])
