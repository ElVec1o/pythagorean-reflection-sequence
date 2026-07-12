#!/usr/bin/env python3
"""Seat-independence of the catalytic locus (paper2 rem:truncroot addendum).

The 1phi1 parameter-argument swap 1phi1(0;b;Q,x) = ((x;Q)inf/(b;Q)inf) 1phi1(0;x;Q,b)
turns S(q) = 1phi1(0; q; q^2, 2q(1-q)) into the equivalent zero condition
    T(q) = 1phi1(0; 2q(1-q); q^2, q)
         = sum_k (-1)^k q^{k^2} / ((q^2;q^2)_k (2q(1-q); q^2)_k)  =  0  at q*,
(prefactor nonvanishing since z* < 1; verified 51 digits; T(q*) ~ 1e-32 = input precision).
Argument becomes the q-power q; the catalytic value moves to the PARAMETER seat --
equivalently the Hahn-Exton q-Bessel of q-dependent order nu(q) = log_{q^2}(2q(1-q)) - 1
vanishing at fixed argument q^{-1/2}. Clearing degree of truncations again ~2N^2: the
double-Pochhammer deficit is INVARIANT under the swap. In either seat, the non-special
value 2q(1-q) lies outside every Rogers-Ramanujan/Bailey lattice: the wall is seat-independent.
"""
import mpmath as mp
mp.mp.dps=50
def onephione(b,Q,x,K=200):
    """1phi1(0;b;Q,x) = sum (-1)^k Q^{k(k-1)/2} x^k / ((Q;Q)_k (b;Q)_k)"""
    s=mp.mpf(0); qq=mp.mpf(1); bb=mp.mpf(1)
    for k in range(K):
        if k>0:
            qq*=(1-Q**k); bb*=(1-b*Q**(k-1))
        t=mp.mpf((-1)**k)*Q**(mp.mpf(k)*(k-1)/2)*x**k/(qq*bb)
        s+=t
        if k>10 and abs(t)<mp.mpf(10)**-55: break
    return s
def pochinf(a,Q):
    r=mp.mpf(1); x=mp.mpf(a)
    for i in range(400):
        r*=(1-x); x*=Q
        if abs(x)<mp.mpf(10)**-52: break
    return r
for qs in ['0.3','0.449453630558948046125545825395696389319555316196']:
    q=mp.mpf(qs); Q=q*q; zs=2*q*(1-q)
    S=onephione(q,Q,zs)                       # original S(q)
    T=onephione(zs,Q,q)                       # swapped
    pref=pochinf(zs,Q)/pochinf(q,Q)
    print(f"q={qs[:8]}: S = {mp.nstr(S,12)}  pref*T = {mp.nstr(pref*T,12)}  rel diff {mp.nstr(abs(S-pref*T)/max(abs(S),mp.mpf(10)**-40),3)}")
    print(f"          T(q) alone = {mp.nstr(T,12)}   (at q*: should be 0)")
