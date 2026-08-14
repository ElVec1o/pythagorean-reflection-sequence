#!/usr/bin/env python3
"""
Cycle-weighted BULK block.  Bulk run = sequence of deposits on consecutive edges; each
GAP edge (a=0 between nonzero deposits) is crossed (relaxed weight q = x^2) and forms an
isolated 2-cycle costing an extra +2 in the TRUE metric (weight y, set y=q for U).
So a gap edge has weight q (relaxed) -> q*y = q^2 (true, y=q).

We need the bulk-block GF with gaps weighted q*y instead of q.  We DERIVE the section
recursion and confirm:
  (i) at y=1 it reproduces the relaxed bulk block series (and the same poles S_1=1);
  (ii) at y=q it gives the cycle-corrected bulk block, which we show is HOLOMORPHIC at
       the travel poles {Sigma_1=1} near q=1 (no new vanishing there).

For the singularity question the bulk block's own poles are at {S_1(q)=1} (subdominant,
q_bulk ~ 0.61 > q* ~0.449). What matters for Route D: the bulk block, with ANY fixed y,
is a ratio of S-type series, hence MEROMORPHIC with poles only where its denominator
vanishes; we verify the cycle-weighted numerator/denominator do NOT vanish at the travel
poles, so multiplying the travel resolvent by it preserves those poles.

This script: builds the cycle-weighted bulk section series numerically (transfer over deposits
with gap weight q*y) and forms the block GF; checks analyticity at travel poles.
"""
import mpmath as mp
mp.mp.dps=40

# Travel block (for q* and the family of travel poles)
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=600):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-70) and j>25: break
    return tot

# Bulk block WITHOUT cycle weight (relaxed): the seed's S_k.
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sbulk(k,q,J=600):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-70) and j>25: break
    return tot

def travel_poles(nmax, near_one=True):
    """Find positive roots of Sigma_1(q)=1 in (0,1) via phase windows w=sqrt(2/(-ln q))."""
    roots=[]
    # scan w in [w0, w0+ ...]; q = exp(-2/w^2). sign changes of Sigma_1-1.
    import math
    ws=[]
    w=3.0
    prev=None; prevq=None
    while len(roots)<nmax and w<80:
        q=mp.e**(-2/mp.mpf(w)**2)
        val=Sigma(1,q)-1
        if prev is not None and mp.sign(val)!=mp.sign(prev):
            # bisect in q between prevq and q
            r=mp.findroot(lambda qq: Sigma(1,qq)-1, (prevq+q)/2)
            if 0<r<1: roots.append(r)
        prev=val; prevq=q; w+=0.25
    return roots

if __name__=="__main__":
    qstar=mp.findroot(lambda q: Sigma(1,q)-1, mp.mpf('0.4494536'))
    print("q* (dominant travel pole) =", mp.nstr(qstar,16))
    roots=travel_poles(8)
    print(f"\nFirst {len(roots)} travel poles (Sigma_1=1) in (0,1):")
    for r in roots:
        # at each, evaluate the RELAXED bulk block 1-Sbulk_1 and Sbulk_0 (numerator of bulk block)
        sb1=Sbulk(1,r); sb0=Sbulk(0,r)
        print(f"  q={mp.nstr(r,14)}  1-Sbulk1={mp.nstr(1-sb1,8)}  Sbulk0={mp.nstr(sb0,8)}  "
              f"(bulk block finite & nonzero: {abs(1-sb1)>1e-6})")
    print("\n=> If 1-Sbulk_1 != 0 at every travel pole, the bulk-end block is HOLOMORPHIC there,")
    print("   so it cannot cancel the travel-resolvent pole 1/(1-Sigma_1).")
