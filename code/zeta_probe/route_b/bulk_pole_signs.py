#!/usr/bin/env python3
"""
PROBE the BULK pole family {S_1(q)=1} = {0.6096, 0.9202, 0.9690, ...} -> 1.
At the TRAVEL poles, the travel numerator Sigma_0 SIGN-ALTERNATES (-,+,-,+,...), which kills
positivity for U.  The paper flags the bulk family as the unexploited lever "where the numerator
structure differs."  Decisive test: at the BULK poles, are the numerator factors SIGN-DEFINITE
(=> positivity lever, possibly a clean route) or sign-alternating (=> same refractory wall)?

Telescoped defs (validated):
  travel: A(k)=2q/(1-q^{k+1}), C(k)=2q^{k+3}/(1-q^{k+2})-2q^{k+2}/(1-q^{k+1}); Sigma_k.
  bulk:   alpha(k)=2q^{k+1}/(1-q^{k+1}), gamma(k)=2q^{k+2}/(1-q^{k+2})-2q^{k+1}/(1-q^{k+1}); S_k.
At a bulk pole q_b: bulk-block residue numerator = S_0(q_b); travel resolvent 1/(1-Sigma_1(q_b))
is FINITE (bulk pole != travel pole).  We report signs of S_0, 1-Sigma_1, Sigma_0, and the
residue sign of the bulk block, across many bulk poles.
"""
import mpmath as mp
mp.mp.dps=40

def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=2000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-80) and j>30: break
    return tot
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=2000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-80) and j>30: break
    return tot

def bisect(f,a,b,it=300):
    fa=f(a); fb=f(b)
    if mp.sign(fa)==mp.sign(fb): return None
    for _ in range(it):
        m=(a+b)/2; fm=f(m)
        if fm==0: return m
        if mp.sign(fm)==mp.sign(fa): a,fa=m,fm
        else: b,fb=m,fm
    return (a+b)/2

def poles(gfun, nmax, w0=2.0, wstep=0.05):
    """zeros of gfun(q)=0 for q=e^{-2/w^2} in (0,1), scanning w upward (q->1)."""
    roots=[]; w=mp.mpf(w0); prev=None; prevq=None
    while len(roots)<nmax and w<400:
        q=mp.e**(-2/w**2)
        try: val=gfun(q)
        except: val=None
        if val is not None and prev is not None and mp.sign(val)!=mp.sign(prev):
            r=bisect(gfun, prevq, q)
            if r is not None and 0<r<1 and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-15)):
                roots.append(r)
        if val is not None: prev=val; prevq=q
        w+=wstep
    return roots

if __name__=="__main__":
    print("=== BULK pole family {S_1(q)=1} ===")
    bp=poles(lambda q: Sb(1,q)-1, 22)
    print(f"found {len(bp)} bulk poles\n")
    hdr=f"{'q_b':>15} {'S0(num)':>13} {'1-Sig1(trav)':>14} {'Sig0':>13} {'S1p':>11} {'res.sign':>9}"
    print(hdr)
    s0signs=[]; ressigns=[]; trsigns=[]
    for r in bp:
        s0=Sb(0,r)                       # bulk numerator (residue numerator of bulk block)
        sig1=Sig(1,r); sig0=Sig(0,r)
        tr=1-sig1                        # travel resolvent denominator at bulk pole (finite)
        h=mp.mpf(10)**(-15)
        s1p=(Sb(1,r+h)-Sb(1,r-h))/(2*h)  # S_1'(q_b) for residue
        res_sign=int(mp.sign(s0)*mp.sign(-s1p))   # sign of bulk-block residue S0/(-S1')
        s0signs.append(int(mp.sign(s0)))
        trsigns.append(int(mp.sign(tr)))
        ressigns.append(res_sign)
        print(f"{mp.nstr(r,11):>15} {mp.nstr(s0,7):>13} {mp.nstr(tr,7):>14} {mp.nstr(sig0,7):>13} {mp.nstr(s1p,5):>11} {res_sign:>9}")
    print()
    def patt(s): return "".join('+' if x>0 else ('-' if x<0 else '0') for x in s)
    print("sign(S0   bulk numerator) :", patt(s0signs))
    print("sign(1-Sig1 travel resolv):", patt(trsigns))
    print("sign(bulk-block residue)  :", patt(ressigns))
    print()
    print("VERDICT:")
    print("  bulk numerator S0 sign-definite? ", len(set(s0signs))==1, "(all", patt(s0signs)[0] if s0signs else '?',")" if len(set(s0signs))==1 else "(ALTERNATES)")
    print("  bulk-block RESIDUE sign-definite?", len(set(ressigns))==1, "" if len(set(ressigns))==1 else "(ALTERNATES)")
    print("  travel resolvent sign at bulk poles:", patt(trsigns))
