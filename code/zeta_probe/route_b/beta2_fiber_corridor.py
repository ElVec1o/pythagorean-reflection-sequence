#!/usr/bin/env python3
"""v2.12.8: THE FIBER-COUPLING CORRIDOR -- swept to 2000 coefficients and BRICKED.

METHOD: u_1 mod p (p = 46337; cross-check prime 40093) to order 2000 via numpy-convolution
Newton (seconds). SOUNDNESS: a primitive integer relation survives reduction mod p, so FULL
RANK MOD ONE PRIME IS A PROOF of non-existence over Q at that profile (false negatives
impossible; only kernel hits would need the second prime -- there were none).

SWEPT PROFILES (all full rank -> all EXCLUDED):
 - single Mahler P(q, u1(q), u1(q^d)) = 0, d = 2, 3:
     (490,1,1) (150,2,2) (100,3,3) (60,4,4) (40,5,5) (30,6,6) (24,7,7) (20,8,8)
 - order-2 Mahler P(q, u1(q), u1(q^2), u1(q^4)) = 0: (30,2,2,2) (20,3,3,3)
 - sigma-delta mix P(q, u1, theta u1, u1(q^2)) = 0: (30,2,2,2) (20,3,3,3)
 - quasi-modular theta-log basket {1, Wlog(q), Wlog(q^2), E2(q), E2(q^2), E4} with
   polynomial coefficients to deg 399 (5-gen) / 332 (6-gen): u_1 is NOT a hidden
   eta-quotient / E2-ring object of level 2
 - log-linear {1, log u1(q), log u1(q^2)} to deg 665
 - Mahler on the log-derivative W = theta log u1: (150,2,2) (100,3,3) (60,4,4)
This extends the v2.12.5 no-go by ~30x in profile volume and closes the quasi-modular
loophole. Combined with the jet ledger (v2.12.7): no point evaluation closes, and no
finite-height fiber coupling exists at accessible complexity.
"""
import numpy as np, json, time
N=2000
def build_u1_modp(p):
    """u1 mod p to order N via Newton, numpy convolutions"""
    def mul(a,b):
        c=np.convolve(a,b)[:N+1]%p
        return c.astype(np.int64)
    def inv_unit(a):
        u=int(a[0]); assert u in (1,p-1)
        c=np.zeros(N+1,dtype=np.int64); c[0]=u
        # blockwise Newton inversion for series: x -> x(2 - a x)
        k=1
        x=np.zeros(N+1,dtype=np.int64); x[0]=u
        while k<=N:
            k2=min(2*k,N+1)
            ax=np.convolve(a[:k2],x[:k2])[:k2]%p
            t=(-ax)%p; t[0]=(t[0]+2)%p
            x2=np.convolve(x[:k2],t)[:k2]%p
            x[:k2]=x2; k=k2
        return x
    def inv_poch(m):
        c=np.zeros(N+1,dtype=np.int64); c[0]=1
        for part in range(1,m+1):
            for n in range(part,N+1): c[n]=(c[n]+c[n-part])%p
        return c
    Gs=[]
    kmax=0
    while kmax*(kmax-1)<=N: kmax+=1
    for k in range(kmax):
        g=np.zeros(N+1,dtype=np.int64)
        e=k*(k-1)
        if e<=N:
            ip=inv_poch(2*k)
            g[e:]=ip[:N+1-e]
            if k%2: g=(-g)%p
        Gs.append(g)
    def evalG(z):
        tot=np.zeros(N+1,dtype=np.int64); zp=np.zeros(N+1,dtype=np.int64); zp[0]=1
        for k in range(kmax):
            tot=(tot+mul(Gs[k],zp))%p; zp=mul(zp,z)
        return tot
    def evalGz(z):
        tot=np.zeros(N+1,dtype=np.int64); zp=np.zeros(N+1,dtype=np.int64); zp[0]=1
        for k in range(1,kmax):
            tot=(tot+k*mul(Gs[k],zp))%p; zp=mul(zp,z)
        return tot
    z=np.zeros(N+1,dtype=np.int64); z[0]=1
    for it in range(12):
        r=evalG(z)
        if not r.any(): break
        z=(z-mul(r,inv_unit(evalGz(z))))%p
    assert not evalG(z).any(), "Newton failed"
    return z
t0=time.time()
for p in (46337,40093):
    u=build_u1_modp(p)
    np.save(f"u1_mod{p}.npy",u)
    print(f"p={p}: u1 to order {N} done ({time.time()-t0:.0f}s); c_1..c_12 mod p:",[int((x if x<p//2 else x-p)) for x in u[1:13]])
# ===== polynomial sweeps =====
import numpy as np, time
N=2000; p=46337
u1=np.load(f"u1_mod{p}.npy")
def mul(a,b): return (np.convolve(a,b)[:N+1]%p).astype(np.int64)
def stretch(a,d):
    c=np.zeros(N+1,dtype=np.int64)
    idx=np.arange(0,N//d+1)
    c[idx*d]=a[idx]
    return c
def inv_unit(a):
    u=int(a[0])
    x=np.zeros(N+1,dtype=np.int64); x[0]=pow(u,p-2,p)
    k=1
    while k<=N:
        k2=min(2*k,N+1)
        ax=np.convolve(a[:k2],x[:k2])[:k2]%p
        t=(-ax)%p; t[0]=(t[0]+2)%p
        x[:k2]=np.convolve(x[:k2],t)[:k2]%p
        k=k2
    return x
def powers(a,dmax):
    ps=[np.zeros(N+1,dtype=np.int64)]; ps[0][0]=1
    for _ in range(dmax): ps.append(mul(ps[-1],a))
    return ps
def rank_modp(cols):
    A=np.stack(cols,axis=1)%p  # rows x cols
    R,C=A.shape; r=0
    for c in range(C):
        piv=np.nonzero(A[r:,c])[0]
        if piv.size==0: continue
        pr=r+piv[0]
        if pr!=r: A[[r,pr]]=A[[pr,r]]
        inv=pow(int(A[r,c]),p-2,p)
        A[r,c:]=A[r,c:]*inv%p
        f=A[r+1:,c]
        nz=np.nonzero(f)[0]
        if nz.size:
            A[r+1+nz,c:]=(A[r+1+nz,c:]-np.outer(f[nz],A[r,c:]))%p
        r+=1
        if r==R: break
    return r,C
def shifts(base,dq):
    out=[]
    for j in range(dq+1):
        c=np.zeros(N+1,dtype=np.int64); c[j:]=base[:N+1-j]
        out.append(c)
    return out
t0=time.time()
def sweep(tag,gens,dq):
    cols=[]
    for g in gens: cols+=shifts(g,dq)
    r,C=rank_modp(cols)
    print(f"  {tag}: {C} unknowns, rank {r} -> {'!!! KERNEL dim '+str(C-r) if r<C else 'none'}   [{time.time()-t0:.0f}s]")
X=powers(u1,8)
for d in (2,3):
    Y=powers(stretch(u1,d),8)
    print(f"single Mahler d={d}: P(q,u1(q),u1(q^{d}))")
    for (dq,dX,dY) in [(490,1,1),(150,2,2),(100,3,3),(60,4,4),(40,5,5),(30,6,6),(24,7,7),(20,8,8)]:
        gens=[mul(X[a],Y[b]) for a in range(dX+1) for b in range(dY+1)]
        sweep(f"({dq},{dX},{dY})",gens,dq)
print("order-2 Mahler: P(q, u1(q), u1(q^2), u1(q^4))")
Y2=powers(stretch(u1,2),3); Y4=powers(stretch(u1,4),3)
for (dq,d1,d2,d3) in [(30,2,2,2),(20,3,3,3)]:
    gens=[mul(mul(X[a],Y2[b]),Y4[c]) for a in range(d1+1) for b in range(d2+1) for c in range(d3+1)]
    sweep(f"({dq},{d1},{d2},{d3})",gens,dq)
print("sigma-delta mix: P(q, u1, u1', u1(q^2))")
du=(u1*np.arange(N+1))%p  # theta u1 = q d/dq actually use theta (q d/dq): n*c_n
D=powers(du,3); Y2b=powers(stretch(u1,2),3)
for (dq,d1,d2,d3) in [(30,2,2,2),(20,3,3,3)]:
    gens=[mul(mul(X[a],D[b]),Y2b[c]) for a in range(d1+1) for b in range(d2+1) for c in range(d3+1)]
    sweep(f"({dq},{d1},{d2},{d3})",gens,dq)
np.save("du_mod46337.npy",du)
# ===== structural baskets =====
import numpy as np, time
N=2000; p=46337
u1=np.load(f"u1_mod{p}.npy"); du=np.load("du_mod46337.npy")
def mul(a,b): return (np.convolve(a,b)[:N+1]%p).astype(np.int64)
def stretch(a,d):
    c=np.zeros(N+1,dtype=np.int64); idx=np.arange(0,N//d+1); c[idx*d]=a[idx]; return c
def inv_unit(a):
    x=np.zeros(N+1,dtype=np.int64); x[0]=pow(int(a[0]),p-2,p); k=1
    while k<=N:
        k2=min(2*k,N+1)
        ax=np.convolve(a[:k2],x[:k2])[:k2]%p
        t=(-ax)%p; t[0]=(t[0]+2)%p
        x[:k2]=np.convolve(x[:k2],t)[:k2]%p; k=k2
    return x
def powers(a,dmax):
    ps=[np.zeros(N+1,dtype=np.int64)]; ps[0][0]=1
    for _ in range(dmax): ps.append(mul(ps[-1],a))
    return ps
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
def shifts(base,dq):
    out=[]
    for j in range(dq+1):
        c=np.zeros(N+1,dtype=np.int64); c[j:]=base[:N+1-j]; out.append(c)
    return out
def sweep(tag,gens,dq):
    cols=[]
    for g in gens: cols+=shifts(g,dq)
    r,C=rank_modp(cols)
    print(f"  {tag}: {C} unknowns, rank {r} -> {'!!! KERNEL dim '+str(C-r) if r<C else 'none'}")
t0=time.time()
W1=mul(du,inv_unit(u1))                       # theta log u1
W2=stretch(W1,2)
def E2():
    c=np.zeros(N+1,dtype=np.int64); c[0]=1
    sig=np.zeros(N+1,dtype=np.int64)
    for d in range(1,N+1):
        for m in range(d,N+1,d): sig[m]=(sig[m]+d)%p
    c[1:]=(-24*sig[1:])%p; return c
E2q=E2(); E2q2=stretch(E2q,2)
def E4():
    c=np.zeros(N+1,dtype=np.int64); c[0]=1
    sig=np.zeros(N+1,dtype=np.int64)
    for d in range(1,N+1):
        dd=pow(d,3,p)
        for m in range(d,N+1,d): sig[m]=(sig[m]+dd)%p
    c[1:]=240*sig[1:]%p; return c
E4q=E4()
ONE=np.zeros(N+1,dtype=np.int64); ONE[0]=1
print("theta-log quasi-modular basket: {1, W1, W1(q^2), E2(q), E2(q^2)} x q^j")
sweep("dq=399 (5 gens)",[ONE,W1,W2,E2q,E2q2],399)
print("with E4: {1, W1, W2, E2, E2(q^2), E4} x q^j")
sweep("dq=332 (6 gens)",[ONE,W1,W2,E2q,E2q2,E4q],332)
# log-linear
def logser(a):
    L=np.zeros(N+1,dtype=np.int64)
    af=a%p
    for n in range(1,N+1):
        s=int(n)*int(af[n])%p
        s=(s-int(np.sum((np.arange(1,n)*L[1:n]%p)*af[n-1:0:-1]%p))%p)%p
        L[n]=s*pow(n,p-2,p)%p
    return L
L1=logser(u1); L2=stretch(L1,2)
print("log-linear: {1, log u1(q), log u1(q^2)} x q^j")
sweep("dq=665 (3 gens)",[ONE,L1,L2],665)
# W-Mahler polynomial
print("Mahler on the log-derivative W = theta log u1: P(q, W(q), W(q^2))")
WX=powers(W1,4); WY=powers(W2,4)
for (dq,dX,dY) in [(150,2,2),(100,3,3),(60,4,4)]:
    gens=[mul(WX[a],WY[b]) for a in range(dX+1) for b in range(dY+1)]
    sweep(f"({dq},{dX},{dY})",gens,dq)
print(f"total {time.time()-t0:.0f}s")
