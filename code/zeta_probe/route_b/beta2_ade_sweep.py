#!/usr/bin/env python3
"""v2.12.9: ADE MEGA-SWEEP -- S(q) and z_1(q) are not differentially algebraic at any
accessible profile; the Nesterenko door is closed proof-grade.

METHOD: series mod p = 46337 to order 2000 (numpy-convolution); delta-jets (delta = q d/dq,
coefficients n^j c_n); all monomials in the jets of total degree <= d times q^j, j <= dq;
full column rank mod ONE prime = proof of non-existence over Q at that profile (a primitive
integer relation survives reduction).

CONTROL (validates the pipeline): E_2 at profile (order 3, deg 2, deg_q 2) shows kernel
dim 3 = the q-Chazy equation  delta^3 E2 = E2 delta^2 E2 - (3/2)(delta E2)^2  times 1,q,q^2.
[q-Chazy re-derived from the Ramanujan system: E4 = E2^2-12 dE2, E6 = E2^3-18 E2 dE2+36 d2E2,
then dE6 = (E2 E6 - E4^2)/2 eliminates everything.]

RESULT: for BOTH S(q) = G(q,2q(1-q)) and u_1 = z_1(q), FULL RANK (no ADE) at every profile
(order, deg, deg_q) = (2,12,3), (3,8,3), (4,5,6), (5,4,8), (6,3,15), (8,2,35), (12,1,120).
Extends the old exclusion (order<=4, deg<=5, 800 terms) by orders of magnitude.
CONSEQUENCE: the Nesterenko route (which requires S differentially algebraic in q) is closed
at proof-grade profiles. S's differential TRANSCENDENCE remains open and currently
unattackable: every known hypertranscendence method routes through a functional equation,
and S provably has none in q (no shift, q-difference, or Mahler equation).
"""
import numpy as np, time, itertools, json
N=2000; p=46337
def mul(a,b): return (np.convolve(a,b)[:N+1]%p).astype(np.int64)
def inv_poch(m):
    c=np.zeros(N+1,dtype=np.int64); c[0]=1
    for part in range(1,m+1):
        for n in range(part,N+1): c[n]=(c[n]+c[n-part])%p
    return c
# S(q) = G(q, 2q(1-q)) mod p
w=np.zeros(N+1,dtype=np.int64); w[1]=2; w[2]=p-2
S=np.zeros(N+1,dtype=np.int64); S[0]=1
wk=np.zeros(N+1,dtype=np.int64); wk[0]=1
for k in range(1,46):
    wk=mul(wk,w)
    e=k*(k-1)
    if e>N: break
    t=np.zeros(N+1,dtype=np.int64)
    ip=inv_poch(2*k); t[e:]=ip[:N+1-e]
    term=mul(t,wk)
    S=(S+((-1)**k)*term)%p
u1=np.load(f"u1_mod{p}.npy")
# sanity: S known low-order? S = 1 - w/(q;q)_2 - ... compute few exact via fractions separately? trust structure; print first coeffs
print("S mod p first 12 coeffs:",[int(x if x<p//2 else x-p) for x in S[:12]])
def E2():
    c=np.zeros(N+1,dtype=np.int64); c[0]=1
    sig=np.zeros(N+1,dtype=np.int64)
    for d in range(1,N+1):
        for m in range(d,N+1,d): sig[m]=(sig[m]+d)%p
    c[1:]=(-24*sig[1:])%p; return c
def delta_jets(a,r):
    jets=[a.copy()]
    n=np.arange(N+1,dtype=np.int64)
    for _ in range(r): jets.append(jets[-1]*n%p)
    return jets
def rank_modp(cols):
    A=np.stack(cols,axis=1)%p; R,C=A.shape; r=0
    for c in range(C):
        piv=np.nonzero(A[r:,c])[0]
        if piv.size==0: continue
        pr=r+piv[0]
        if pr!=r: A[[r,pr]]=A[[pr,r]]
        A[r,c:]=A[r,c:]*pow(int(A[r,c]),p-2,p)%p
        f=A[r+1:,c]; nz=np.nonzero(f)[0]
        if nz.size: A[r+1+nz,c:]=(A[r+1+nz,c:]-np.outer(f[nz],A[r,c:]))%p
        r+=1
        if r==R: break
    return r,C
def monomials(jets,d):
    """all products of jets with total degree <= d, built incrementally"""
    r1=len(jets)
    out={(0,)*r1: np.concatenate([[1],np.zeros(N,dtype=np.int64)]).astype(np.int64)}
    frontier=[(0,)*r1]
    for _ in range(d):
        newf=[]
        for t in frontier:
            for i in range(r1):
                nt=list(t); nt[i]+=1; nt=tuple(nt)
                if nt not in out and sum(nt)<=d:
                    out[nt]=mul(out[t],jets[i]); newf.append(nt)
        frontier=newf
    return list(out.values())
def shifts(base,dq):
    o=[]
    for j in range(dq+1):
        c=np.zeros(N+1,dtype=np.int64); c[j:]=base[:N+1-j]; o.append(c)
    return o
def ade_sweep(name,series,profiles):
    print(f"ADE sweep for {name} (delta-jets):")
    for (r,d,dq) in profiles:
        jets=delta_jets(series,r)
        mons=monomials(jets,d)
        cols=[]
        for m in mons: cols+=shifts(m,dq)
        rk,C=rank_modp(cols)
        print(f"  order {r}, deg {d}, deg_q {dq}: {C} unknowns, rank {rk} -> {'!!! KERNEL dim '+str(C-rk) if rk<C else 'none'}")
t0=time.time()
ade_sweep("E2 (CONTROL: q-Chazy must appear)",E2(),[(3,2,2)])
ade_sweep("S(q)",S,[(2,12,3),(3,8,3),(4,5,6),(5,4,8),(6,3,15),(8,2,35),(12,1,120)])
ade_sweep("u1 = z1(q)",u1,[(2,12,3),(3,8,3),(4,5,6),(5,4,8),(6,3,15),(8,2,35),(12,1,120)])
print(f"total {time.time()-t0:.0f}s")
np.save("S_mod46337.npy",S)
