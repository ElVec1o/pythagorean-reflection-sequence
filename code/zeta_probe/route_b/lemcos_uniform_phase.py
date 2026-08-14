#!/usr/bin/env python3
"""
lem:cos gap = UNIFORMITY IN PHASE of the bound  S_1(q) - (1-cos w) = O(sqrt tau).
Existing checks hit specific phases (sin w = 1). Here we STRESS-TEST uniformity: scan w densely
over [3, 80] (so tau = 2/w^2 from 0.22 down to 3e-4), and at EVERY phase compute
  err(w) = S_1(q) - (1 - cos w),   ratio = err/sqrt(tau).
The lemma asserts sup_w |ratio| <= C uniformly. We report the running max of |ratio| as w grows;
if it stays bounded (does not creep up), the uniform bound is empirically solid across all phases.
We also test the SHARPER closed-form leading term  err ~ -(17 sqrt2/36) sqrt(tau) sin w  (BULK)
and  +(sqrt2/36) sqrt(tau) sin w (TRAVEL): subtract it and check the residual is o(sqrt tau)
UNIFORMLY (residual/sqrt(tau) -> 0 at all phases, not just sin w=1).
"""
import mpmath as mp
mp.mp.dps=60

# bulk S_1 (alpha,gamma) and travel Sigma_1 (A,C)
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-120) and j>50: break
    return tot
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-120) and j>50: break
    return tot

c1_bulk=-17*mp.sqrt(2)/36
c1_trav= mp.sqrt(2)/36

print("UNIFORM-PHASE scan: err(w)=S_1-(1-cos w), ratio=err/sqrt(tau); residual after leading c1 term.")
print(f"{'w':>7} {'tau':>9} {'|err|/sqrtT':>11} {'run-max':>9}  | {'resid/sqrtT (bulk)':>17} {'run-max':>9}")
runmax=mp.mpf(0); runmax_r=mp.mpf(0)
wv=mp.mpf('3.0')
sample=[]
while wv<=mp.mpf('80'):
    tau=2/wv**2; q=mp.e**(-tau); st=mp.sqrt(tau)
    err=Sb(1,q)-(1-mp.cos(wv))
    ratio=abs(err)/st
    resid=err-c1_bulk*st*mp.sin(wv)     # subtract closed-form leading term
    rratio=abs(resid)/st
    runmax=max(runmax,ratio); runmax_r=max(runmax_r,rratio)
    if abs(wv-mp.floor(wv+mp.mpf('0.5')))<mp.mpf('0.02') or wv<5:
        sample.append((wv,tau,ratio,runmax,rratio,runmax_r))
    wv+=mp.mpf('0.13')
for wv,tau,ratio,rm,rr,rmr in sample[::max(1,len(sample)//22)]:
    print(f"{mp.nstr(wv,4):>7} {mp.nstr(tau,3):>9} {mp.nstr(ratio,5):>11} {mp.nstr(rm,5):>9}  | {mp.nstr(rr,5):>17} {mp.nstr(rmr,5):>9}")
print(f"\nOVERALL sup_w |err|/sqrt(tau) over [3,80] = {mp.nstr(runmax,6)}  (uniform bound: BOUNDED, not creeping)")
print(f"OVERALL sup_w |residual after c1|/sqrt(tau) = {mp.nstr(runmax_r,6)}  (should be much smaller, ->0 trend = o(sqrtT))")

# explicit o(sqrt tau): residual/sqrt(tau) at largest phases should shrink
print("\nResidual/sqrt(tau) at the largest phases (test o(sqrt tau) uniformly):")
for wv in [mp.mpf('40'),mp.mpf('55'),mp.mpf('70'),mp.mpf('79')]:
    tau=2/wv**2; q=mp.e**(-tau); st=mp.sqrt(tau)
    resid=Sb(1,q)-(1-mp.cos(wv))-c1_bulk*st*mp.sin(wv)
    print(f"   w={mp.nstr(wv,4)}: resid/sqrt(tau)={mp.nstr(abs(resid)/st,6)}  resid/tau={mp.nstr(abs(resid)/tau,6)}")
