#!/usr/bin/env python3
"""
Validate the cycle-weighted bulk kernel  K(a,b) = q^{max(a,b)} + q^{a+b} * (q y)/(1-q y)
by building the bulk-block GENERATING SERIES in q and matching the seed's 0,2,2,6,2,18,...
at y=1, then reading the y-dependence (the DEFECT) at y=q.

Bulk block (one-sided run attached to a marker on the LEFT at site 0):
  G(q,y) = sum over runs (>=1 active edges, gaps allowed between them) attached to marker.
  We build it as a power series in q by a transfer over half-sizes with the kernel K.
  P_w(q,y) = generating series of runs ending in active half-size w.
  Boundary (attach to marker): first active edge w pays edge weight 2 q^w and a marker-join
  site cost q^{w} (the seed's S0 uses site q^{k+1}->the marker boundary).  Subsequent edges
  use K(prev,w).  Block = sum_w P_w.
Match target: seed G0_bulk = 0,2,2,6,2,18,6,42,18 (coeff of q^n).
"""
import mpmath as mp
mp.mp.dps=30
from functools import lru_cache

# Work with truncated power series in q as coefficient lists (length NT).
NT=14
def smul(a,b):
    r=[mp.mpf(0)]*NT
    for i,ai in enumerate(a):
        if ai==0: continue
        for j,bj in enumerate(b):
            if i+j<NT: r[i+j]+=ai*bj
    return r
def sadd(a,b): return [a[i]+b[i] for i in range(NT)]
def qpow(n):  # series for q^n
    r=[mp.mpf(0)]*NT
    if n<NT: r[n]=mp.mpf(1)
    return r
def geom(c,n):  # series for c*(q^n)/(1-q^n)... but we need (qy)/(1-qy) with y a number set later
    pass

def block_series(yval, Smax=13):
    # y is a numeric value (1 -> relaxed, or we substitute y=q LATER by shifting). Here we
    # treat y as a fixed scalar; for y=q we will instead build the kernel with the q-series of y.
    # gap-bridge series g = (q*y)/(1-q*y). With y scalar:
    g=[mp.mpf(0)]*NT
    # (q*y)/(1-q*y) = sum_{m>=1} (y)^m q^m
    for m in range(1,NT):
        g[m]=yval**m
    sizes=list(range(1,Smax+1))
    # P_w series; iterate transfer to convergence in q-order (NT terms => Smax>=NT enough)
    P={w:[mp.mpf(0)]*NT for w in sizes}
    # seed: first edge w attached to marker: weight 2 q^w * (marker join q^w) = 2 q^{2w}?
    # The seed S_0 = sum_j alpha_{2j} prod gamma; alpha_0=2q/(1-q): first coeff q^1 -> matches
    # block starting 0,2,.. (coeff q^1=2). So a single active edge w contributes 2 q^{w} * 1
    # (marker join cost folds into the S structure). Let's set seed_w = 2 q^w (marker-attached,
    # the marker join is q^0=1 since marker is the left end at "size 0", max(0,w)=w already in edge).
    # Hmm edge weight is 2q^w; site to marker = q^{max(0,w)}=q^w. So seed_w = 2 q^w * q^w? gives
    # coeff at q^2. But block starts at q^1. So marker join must be q^0. Use seed_w=2 q^w.
    seed={w: [mp.mpf(0)]*NT for w in sizes}
    for w in sizes:
        s=[mp.mpf(0)]*NT
        if w<NT: s[w]=mp.mpf(2)
        seed[w]=s
    # transfer: P_w = seed_w + e(w) * sum_{a} P_a * K(a,w),  but e(w) already in seed scale...
    # Define P_w = seed_w + sum_a P_a * [2 q^w * K(a,w)] with K(a,w)=q^{max(a,w)}+q^{a+w} g.
    for _ in range(NT+2):
        newP={}
        for w in sizes:
            acc=list(seed[w])
            for a in sizes:
                K=sadd(qpow(max(a,w)), smul(qpow(a+w),g))
                term=smul(P[a], smul(qpow(w),[mp.mpf(2) if i==0 else mp.mpf(0) for i in range(NT)]))
                term=smul(term,K)
                acc=sadd(acc,term)
            newP[w]=acc
        P=newP
    B=[mp.mpf(0)]*NT
    for w in sizes: B=sadd(B,P[w])
    return B

if __name__=="__main__":
    Brel=block_series(mp.mpf(1))
    print("kernel block y=1:", [int(mp.nint(c)) for c in Brel])
    print("seed target:      [0, 2, 2, 6, 2, 18, 6, 42, 18, ...]")
