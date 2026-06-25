#!/usr/bin/env python3
# ROUTE D3.2 -- CORRECTED subleading coefficient.
# Established:  sum_n k_n = w - 3pi/4 + a1 sqrt(tau) + a3 tau^{3/2} + ...
# So the residual after the constant is  res(tau) := sum k - w + 3pi/4  -> 0 like sqrt(tau).
# a1 = lim res/sqrt(tau). Then res - a1 sqrt(tau) ~ a3 tau^{3/2} (next half power) => Poincare.

import mpmath as mp
mp.mp.dps = 50

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))
def kfun(n, q):
    bn = bcoef(n, q)
    if abs(bn) >= 2: return None
    return mp.acos(bn/2)
def S1(tau):
    q=mp.e**(-tau); s=mp.mpf(0); n=0
    while True:
        kn=kfun(n,q)
        if kn is None: break
        s+=kn; n+=1
        if n>1500000: break
    return s

m3pi4=3*mp.pi/4
def res(tau):
    return S1(tau) - mp.sqrt(2/tau) + m3pi4   # -> 0 ~ a1 sqrt(tau)

taus=[mp.mpf("0.008")/2**i for i in range(8)]
rs=[res(t) for t in taus]
print("=== res = sum k - w + 3pi/4  (-> 0); a1 = res/sqrt(tau) ===")
for t,r in zip(taus,rs):
    print(f"  tau={mp.nstr(t,6):>12}  res={mp.nstr(r,11)}  res/sqrt(tau)={mp.nstr(r/mp.sqrt(t),9)}  res/tau={mp.nstr(r/t,8)}")
print()
# exponent of res
print("local exponent p of res (res = a*tau^p), from difference ratios (tau halving):")
for i in range(len(taus)-2):
    r1,r2,r3=rs[i],rs[i+1],rs[i+2]
    rr=(r3-r2)/(r2-r1)
    p=mp.log(rr)/mp.log(mp.mpf("0.5"))
    print(f"   tau~{mp.nstr(taus[i],4)}: p={mp.nstr(p,7)}")
print()
ratios=[r/mp.sqrt(t) for t,r in zip(taus,rs)]
print("res/sqrt(tau) (-> a1):", [mp.nstr(x,9) for x in ratios])
def rich(rs,ts):
    out=[]
    for i in range(len(rs)-1):
        out.append((rs[i]*ts[i+1]-rs[i+1]*ts[i])/(ts[i+1]-ts[i]))
    return out
a1=rich(ratios,taus)
print("a1 Richardson (linear-in-tau):", [mp.nstr(x,11) for x in a1])
a1b=rich(a1,taus[:-1])
print("a1 second Richardson:", [mp.nstr(x,11) for x in a1b])
print()
print("candidate a1 closed forms:")
for nm,v in [("sqrt2/36",mp.sqrt(2)/36),("sqrt2/18",mp.sqrt(2)/18),("1/(3sqrt2)",1/(3*mp.sqrt(2))),
             ("sqrt2/12",mp.sqrt(2)/12),("1/(6sqrt2)",1/(6*mp.sqrt(2))),("7/(36)*sqrt2",mp.mpf(7)/36*mp.sqrt(2)),
             ("5sqrt2/36",5*mp.sqrt(2)/36),("sqrt2/9",mp.sqrt(2)/9),("11sqrt2/72",11*mp.sqrt(2)/72),
             ("1/3",mp.mpf(1)/3),("0.137...?","")]:
    if v!="":
        print(f"   {nm} = {mp.nstr(v,11)}")
print()
# DECISIVE: the residual after subtracting a1 sqrt(tau): is the NEXT power tau^{3/2}? (Poincare)
# Use the best a1 estimate (second Richardson last) and form res - a1 sqrt(tau), check exponent.
a1best=a1b[-1]
print(f"using a1 ~ {mp.nstr(a1best,12)}; residual r2 = res - a1*sqrt(tau), exponent:")
r2=[res(t)-a1best*mp.sqrt(t) for t in taus]
for i in range(len(taus)-2):
    x1,x2,x3=r2[i],r2[i+1],r2[i+2]
    if (x2-x1)!=0:
        rr=(x3-x2)/(x2-x1)
        if rr>0:
            p=mp.log(rr)/mp.log(mp.mpf("0.5"))
            print(f"   tau~{mp.nstr(taus[i],4)}: r2={mp.nstr(x2,6)}  next-power p={mp.nstr(p,6)}")
        else:
            print(f"   tau~{mp.nstr(taus[i],4)}: r2={mp.nstr(x2,6)}  ratio<0 (a1 not converged enough)")
