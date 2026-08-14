#!/usr/bin/env python3
"""
SEAM: prove the numerator NON-VANISHING by ASYMPTOTIC ALTERNATION instead of 58 spot checks.
At travel poles q_m (Sigma_1=1, w_m=sqrt(2/tau_m) ~ (m+1/2)pi), the V-numerator Sigma_0(q_m)
empirically STRICTLY ALTERNATES with |Sigma_0| growing ~ pi*m.  A strictly sign-alternating
sequence with |.|->inf has NO zeros => Sigma_0(q_m)!=0 for all large m => V transcendental
(given lem:cos supplies infinitely many poles), NO numerical certification needed.

This script: compute ~40 travel poles, w_m, Sigma_0(q_m); test
  (1) strict sign alternation,
  (2) |Sigma_0(q_m)| / m -> const ( ~ pi ?),  and other fits (w_m, 1/sqrt(tau)),
to pin the clean leading asymptotic to then DERIVE.
"""
import mpmath as mp
mp.mp.dps=50

def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=4000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>40: break
    return tot

def bisect(f,a,b,it=400):
    fa=f(a); fb=f(b)
    if mp.sign(fa)==mp.sign(fb): return None
    for _ in range(it):
        m=(a+b)/2; fm=f(m)
        if mp.sign(fm)==mp.sign(fa): a,fa=m,fm
        else: b,fb=m,fm
    return (a+b)/2

def travel_poles(nmax):
    roots=[]; w=mp.mpf('1.5'); prev=None; prevq=None; g=lambda qq: Sig(1,qq)-1
    while len(roots)<nmax and w<400:
        q=mp.e**(-2/w**2); val=g(q)
        if prev is not None and mp.sign(val)!=mp.sign(prev):
            r=bisect(g,prevq,q)
            if r and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-16)): roots.append(r)
        prev=val; prevq=q; w+=mp.mpf('0.03')
    return roots

if __name__=="__main__":
    P=travel_poles(40)
    print(f"{len(P)} travel poles.  m: index from 1.")
    print(f"{'m':>3} {'q_m':>16} {'w_m':>12} {'w_m/pi-1/2':>11} {'Sigma0':>14} {'|S0|/m':>9} {'|S0|/w':>9}")
    s0v=[]
    for i,r in enumerate(P,1):
        tau=-mp.log(r); w=mp.sqrt(2/tau)
        s0=Sig(0,r); s0v.append(s0)
        print(f"{i:>3} {mp.nstr(r,12):>16} {mp.nstr(w,8):>12} {mp.nstr(w/mp.pi-0.5,6):>11} {mp.nstr(s0,9):>14} {mp.nstr(abs(s0)/i,6):>9} {mp.nstr(abs(s0)/w,6):>9}")
    # alternation test
    alt=all(s0v[i]*s0v[i+1]<0 for i in range(len(s0v)-1))
    print(f"\nstrict sign alternation over {len(s0v)} poles: {alt}")
    # asymptotic fits on tail
    tail=s0v[-12:]; idx=list(range(len(s0v)-11,len(s0v)+1))
    print("tail |Sigma0|/m :", [mp.nstr(abs(v)/k,7) for v,k in zip(tail,idx)])
    # increments of |Sigma0|
    a=[abs(v) for v in s0v]
    inc=[a[i+1]-a[i] for i in range(len(a)-1)]
    print("increments |S0|(m+1)-|S0|(m) (tail):", [mp.nstr(x,7) for x in inc[-10:]])
    print("pi =", mp.nstr(mp.pi,8))
    # is increment -> pi ?  and |S0| ~ pi*m + b ?  fit b on tail
    bvals=[a[k-1]-mp.pi*k for k in idx]
    print("tail (|S0| - pi*m):", [mp.nstr(x,7) for x in bvals])
