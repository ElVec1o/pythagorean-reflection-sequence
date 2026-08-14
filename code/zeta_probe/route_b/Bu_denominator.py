#!/usr/bin/env python3
"""
Does the cycle-corrected bulk dressing B_U have a pole at any travel pole q_m?
B_U is meromorphic; its poles are where the bulk transfer's spectral radius rho(M(q,y))=1
with y=q (true).  We compute rho of the cycle-weighted bulk transfer at travel poles and
check it stays !=1 (i.e. B_U holomorphic there), and compare to y=1 (relaxed, rho=S1-related).

Cycle-weighted bulk transfer kernel between active half-sizes a,b>=1:
    K(a,b) = q^{max(a,b)} + q^{a+b} * (q y)/(1 - q y)
with full edge factor: transfer entry M[b,a] = 2 q^b * K(a,b) (edge weight 2q^b of the
appended edge times the join kernel).  Spectral radius rho(M)=1 marks the dressing pole.
At y=1 this should reproduce the relaxed bulk pole locus {S1=1}; we VERIFY that rho(M(q,1))
crosses 1 exactly at the bulk poles q_b, confirming the kernel is the right object, then
read rho(M(q_m, q)) at TRAVEL poles for the TRUE dressing.
"""
import mpmath as mp
mp.mp.dps=30

def A(k,q): return 2*q/(1-q**(k+1))
def Cc(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=900):
    t=mp.mpf(0);p=mp.mpf(1)
    for j in range(J):
        t+=A(k+2*j,q)*p;p*=Cc(k+2*j,q)
        if abs(p)<mp.mpf(10)**(-60) and j>25: break
    return t
def al(k,q): return 2*q**(k+1)/(1-q**(k+1))
def ga(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=900):
    t=mp.mpf(0);p=mp.mpf(1)
    for j in range(J):
        t+=al(k+2*j,q)*p;p*=ga(k+2*j,q)
        if abs(p)<mp.mpf(10)**(-60) and j>25: break
    return t
def bis(f,a,b,it=300):
    fa=f(a);fb=f(b)
    if mp.sign(fa)==mp.sign(fb): return None
    for _ in range(it):
        m=(a+b)/2;fm=f(m)
        if fm==0: return m
        if mp.sign(fm)==mp.sign(fa):a,fa=m,fm
        else:b,fb=m,fm
    return (a+b)/2
def find_roots(g,nmax):
    roots=[];w=2.5;prev=None;pq=None
    while len(roots)<nmax and w<400:
        q=mp.e**(-2/mp.mpf(w)**2);val=g(q)
        if prev is not None and mp.sign(val)!=mp.sign(prev):
            r=bis(g,pq,q)
            if r and 0<r<1 and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-20)): roots.append(r)
        prev=val;pq=q;w+=0.05
    return sorted(roots)

def spectral_radius(q,y,Smax=70):
    g=(q*y)/(1-q*y)
    sizes=list(range(1,Smax+1)); n=len(sizes); idx={w:i for i,w in enumerate(sizes)}
    M=mp.matrix(n,n)
    for a in sizes:
        for b in sizes:
            K=q**max(a,b)+q**(a+b)*g
            M[idx[b],idx[a]]=2*q**b*K
    ev=mp.eig(M,left=False,right=False)
    return max(abs(e) for e in ev)

if __name__=="__main__":
    # VERIFY kernel: rho(M(q,1)) = 1 at bulk poles?
    bulk=find_roots(lambda q: Sb(1,q)-1, 4)
    print("verify: spectral radius of relaxed kernel (y=1) at bulk poles (should be ~1):")
    for qb in bulk:
        print(f"   q_bulk={mp.nstr(qb,10)}  rho(M(q,1))={mp.nstr(spectral_radius(qb,mp.mpf(1)),10)}")
    print()
    trav=find_roots(lambda q: Sig(1,q)-1, 12)
    print("At TRAVEL poles: rho of relaxed (y=1) and TRUE (y=q) bulk transfer; <1 => dressing holo:")
    print(f"{'q_m':>14} {'rho(y=1)':>14} {'rho(y=q)TRUE':>14} {'both<1':>8}")
    ok=True
    for qm in trav:
        r1=spectral_radius(qm,mp.mpf(1))
        rt=spectral_radius(qm,qm)
        b=(r1<1 and rt<1)
        if not b: ok=False
        print(f"{mp.nstr(qm,10):>14} {mp.nstr(r1,9):>14} {mp.nstr(rt,9):>14} {str(b):>8}")
    print()
    print("rho<1 at travel pole => bulk dressing has NO pole there => B holomorphic.")
    print("If TRUE rho(y=q) < relaxed rho(y=1) <1, the cycle correction keeps it holo too.")
