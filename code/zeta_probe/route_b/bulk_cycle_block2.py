#!/usr/bin/env python3
"""
Cycle-weighted bulk block at y=q (true metric).  We build the bulk-run generating series
by an explicit catalytic transfer over deposits, where each GAP edge carries weight q*y
(relaxed crossing q TIMES cycle splice y) instead of q.  Set y=1 -> relaxed; y=q -> true.

Bulk run model (validated in catalytic_funceq / KERNEL_NOTES):
  - a run is a sequence of edges along Z, each with even deposit a=2s, s>=1 (active) or a=0
    (GAP, forced crossing m=2);
  - active edge of half-size s: edge weight q^s (=x^{2s}), site coupling q^{max(s_prev,s)};
  - gap edge: crossing weight q (m=2 -> x^2 = q), site coupling q^{max(s_prev,0)}=q^{s_prev}
    to the left and q^{s_next} to the right; PLUS cycle weight y in the true metric.

We compute the run GF G(q,y) = sum over runs of (q^{length} y^{#gaps}) by a left-to-right
transfer with catalytic state = current edge half-size w (0 for a gap).  We then track the
DENOMINATOR structure: the dominant bulk pole is where the transfer resolvent diverges.
For Route D we only need: the cycle-weighted bulk block is MEROMORPHIC, holomorphic at the
travel poles {Sigma_1=1}, with denominator bounded away from 0 there.

Direct numeric approach: truncate the catalytic transfer to half-sizes s<=Smax and gap runs
<=Gmax, build the run-resolvent matrix M(q,y), block GF = (I-M)^{-1} applied to seed; locate
its poles (where det(I-M)=0) and confirm none coincide with travel poles near q=1.
"""
import mpmath as mp
mp.mp.dps=40

def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=600):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-70) and j>25: break
    return tot

def travel_poles(nmax):
    roots=[]; w=3.0; prev=None; prevq=None
    while len(roots)<nmax and w<120:
        q=mp.e**(-2/mp.mpf(w)**2); val=Sigma(1,q)-1
        if prev is not None and mp.sign(val)!=mp.sign(prev) and prev!=0:
            r=mp.findroot(lambda qq: Sigma(1,qq)-1, (prevq+q)/2)
            if 0<r<1 and (not roots or abs(r-roots[-1])>1e-12): roots.append(r)
        prev=val; prevq=q; w+=0.2
    return roots

# Cycle-weighted bulk block via catalytic transfer.
# State: half-size w of last edge (w=0 means a gap edge just placed).
# We unfold like the seed: define G_k(q,y) = bulk run GF read with catalytic mark t->q^k.
# The relaxed (y=1) recursion was: G_k = alpha_k (1+G_1) + gamma_k G_{k+2}.
# Gaps: a gap edge is the s=0 term. In the relaxed derivation gaps are SUBSUMED (deposits
# enumerated s>=1; gap edges appear via the reachability m=2 between supports). To weight
# gaps we must expose them. Simpler: build the block by an explicit finite transfer matrix
# on bounded half-sizes and EXACT gap handling, then read poles numerically.
#
# Transfer over "cells": a cell is either an active edge (half-size s in 1..Smax) or a gap.
# Site coupling between consecutive cells with sizes w_prev,w (gap=0): weight q^{max(w_prev,w)}.
# Active edge size s: edge weight 2*q^s (factor 2 = signs). Gap: edge weight q * y (m=2 -> q,
#   times cycle y). A run is any nonempty sequence; block GF sums over all runs.
# We compute R(q,y) = sum over runs of product(weights). Transfer matrix indexed by current
# size w in {0,1,..,Smax} (0=gap):
def block_R(q,y,Smax=40):
    sizes=list(range(0,Smax+1))  # 0=gap
    def edgew(w):
        if w==0: return q*y      # gap edge: crossing q, cycle y
        return 2*q**w            # active edge, both signs
    # vector over current size = sum of run-weights of runs ENDING in that size (incl. site to left? )
    # We'll include the LEFT site coupling when appending. Seed: a length-1 run of size w has
    # weight edgew(w) (no internal site). Then append w' paying q^{max(w,w')} * edgew(w').
    vec={w: edgew(w) for w in sizes}
    total=sum(vec.values())
    # iterate appends until convergence (geometric; converges for q<1 region of interest)
    for _ in range(4000):
        nv={}
        for wp in sizes:
            s=mp.mpf(0)
            for w in sizes:
                s+=vec[w]*q**max(w,wp)
            nv[wp]=s*edgew(wp)
        add=sum(nv.values())
        total+=add
        vec=nv
        if abs(add)<mp.mpf(10)**(-50): break
    return total

if __name__=="__main__":
    qstar=mp.findroot(lambda q: Sigma(1,q)-1, mp.mpf('0.4494536'))
    print("q*=",mp.nstr(qstar,14))
    roots=travel_poles(10)
    print(f"\n{len(roots)} travel poles. At each: cycle-weighted bulk block R(q,y=q) (TRUE) and")
    print("relaxed R(q,1); both should be FINITE (holomorphic) -- bulk block has no pole here.\n")
    for r in roots:
        Rrel=block_R(r, mp.mpf(1))
        Rtrue=block_R(r, r)         # y=q
        finite = abs(Rrel)<mp.mpf(10)**6 and abs(Rtrue)<mp.mpf(10)**6
        print(f"  q={mp.nstr(r,12)}  R_relaxed={mp.nstr(Rrel,8)}  R_true(y=q)={mp.nstr(Rtrue,8)}  finite={finite}")
