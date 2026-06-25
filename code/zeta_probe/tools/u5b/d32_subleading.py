#!/usr/bin/env python3
# ROUTE D3.2 -- does the discrete-LG phase reproduce the SUBLEADING (Poincare) terms,
# i.e. the c_k pole law, not just the leading w - 3pi/4?
#
# The pole quantization (standing wave / Sigma=1) is  Phi_total(tau_m) = (m+1/2)pi where
#   Phi_total = [discrete LG phase] = sum_{n} k_n  +  [turning connection already in -3pi/4]
# Wait: we found sum k_n = w - 3pi/4 + a1 sqrt(tau)+...  The pole law from MEMORY/confluence
# is w_m = (m+1/2)pi - sqrt2/36 sqrt(tau) - ... i.e.  (m+1/2)pi - w_m = sqrt2/36 sqrt(tau)+...
# and the EM cube identity says (m+1/2)pi - w_m = (1/24) sum k^3.
#
# The discrete-LG PHASE that must equal (m+1/2)pi at a pole is the FULL accumulated phase
# INCLUDING the curvature (cube) correction:
#     Theta(tau) := sum_n k_n  - (1/24) sum_n k_n^3 + (3pi/4)   [+ const to fix branch]
# should equal w + (pole corrections). Let's instead directly TEST the known pole law via
# the discrete objects:  define
#     PoleDev(tau) := w + 3pi/4 - sum_n k_n        [ = -(sum k - w) - 3pi/4, ->0 ]
# and check PoleDev/sqrt(tau) -> a fixed constant a1, then PoleDev - a1 sqrt(tau) ~ tau^{3/2}.
#
# If a1 is a STABLE constant and the residual is the next half-power, the phase is a
# genuine asymptotic (Poincare) series => the c_k (which are algebraic combinations of
# these phase coefficients via the standing-wave condition) are the one-sided Taylor data.

import mpmath as mp
mp.mp.dps = 50

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))
def kfun(n, q):
    bn = bcoef(n, q)
    if abs(bn) >= 2: return None
    return mp.acos(bn/2)

def sums(tau):
    q=mp.e**(-tau)
    S1=mp.mpf(0); S3=mp.mpf(0); S5=mp.mpf(0); n=0
    while True:
        kn=kfun(n,q)
        if kn is None: break
        S1+=kn; S3+=kn**3; S5+=kn**5; n+=1
        if n>800000: break
    return q,S1,S3,S5

m3pi4=3*mp.pi/4
def poledev(tau):
    q,S1,S3,S5=sums(tau)
    w=mp.sqrt(2/tau)
    return w + m3pi4 - S1    # ->0 like sqrt(tau)

print("=== subleading phase coefficient a1 of (w+3pi/4 - sum k) ===")
taus=[mp.mpf("0.01")/2**i for i in range(7)]
pd=[poledev(t) for t in taus]
for t,p in zip(taus,pd):
    print(f"  tau={mp.nstr(t,5):>11}  PoleDev={mp.nstr(p,10)}  /sqrt(tau)={mp.nstr(p/mp.sqrt(t),8)}  /tau={mp.nstr(p/t,7)}")
print()
# extrapolate a1 = lim PoleDev/sqrt(tau). Then residual r=PoleDev - a1 sqrt(tau); exponent?
# fit PoleDev = a1 sqrt(tau) + a3 tau^{3/2}+...  => PoleDev/sqrt(tau) = a1 + a3 tau + ...
ratios=[p/mp.sqrt(t) for t,p in zip(taus,pd)]
print("PoleDev/sqrt(tau) (->a1):", [mp.nstr(r,9) for r in ratios])
# Richardson (linear in tau): a1 = (r_i * t_{i+1} - r_{i+1} t_i)/(t_{i+1}-t_i) with halving
def rich(rs,ts):
    out=[]
    for i in range(len(rs)-1):
        out.append((rs[i]*ts[i+1]-rs[i+1]*ts[i])/(ts[i+1]-ts[i]))
    return out
a1ext=rich(ratios,taus)
print("a1 (Richardson, linear-in-tau):", [mp.nstr(x,10) for x in a1ext])
print()
# compare with cube-sum prediction: (m+1/2)pi - w_m = (1/24) sum k^3 -> sqrt2/36 sqrt(tau).
# Note PoleDev here = w+3pi/4-sum k. The cube term enters the FULL phase as -(1/24)sum k^3.
# So the *consistent* quantization deviation is PoleDev_full = w+3pi/4 - (sum k - (1/24)sum k^3)
def poledev_full(tau):
    q,S1,S3,S5=sums(tau)
    w=mp.sqrt(2/tau)
    return w + m3pi4 - (S1 - S3/24)
print("=== with cube correction included: w+3pi/4 - (sum k - (1/24)sum k^3) ===")
pdf=[poledev_full(t) for t in taus]
for t,p in zip(taus,pd):
    pf=poledev_full(t)
    print(f"  tau={mp.nstr(t,5):>11}  full PoleDev={mp.nstr(pf,9)}  /sqrt(tau)={mp.nstr(pf/mp.sqrt(t),8)}")
ratios_f=[p/mp.sqrt(t) for t,p in zip(taus,pdf)]
print("full a1 (Richardson):", [mp.nstr(x,10) for x in rich(ratios_f,taus)])
print()
# candidate closed forms for a1
print("candidate constants:")
for nm,v in [("sqrt2/36",mp.sqrt(2)/36),("1/sqrt2",1/mp.sqrt(2)),("sqrt2/18",mp.sqrt(2)/18),
             ("1/(3sqrt2)",1/(3*mp.sqrt(2))),("11/4*(1/2)^{3/2}",mp.mpf(11)/4*(mp.mpf(1)/2)**mp.mpf("1.5")),
             ("-sqrt2/36",-mp.sqrt(2)/36),("2sqrt2/3",2*mp.sqrt(2)/3),("1/sqrt2 - small","")]:
    if v!="":
        print(f"   {nm} = {mp.nstr(v,10)}")
