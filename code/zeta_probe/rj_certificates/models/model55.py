# truncated power series in x (degree<=D), integer coefficients; paper2 literal model for k>0 sector
D=27
def z(): return [0]*(D+1)
def mono(c,e):
    r=z()
    if 0<=e<=D: r[e]=c
    return r
def add(a,b): return [u+v for u,v in zip(a,b)]
def sc(c,a): return [c*u for u in a]
def mul(a,b):
    r=z()
    for i,u in enumerate(a):
        if u:
            for j in range(D+1-i): r[i+j]+=u*b[j]
    return r
from fractions import Fraction as Fr
NB=D//2+2; NS=D//2+2
def bulk(g, outer):
    # P_b = 2 q^b ( w_b + sum_a (q^max + q^{a+b} g) P_a ), w_b = 1 (paper) or q^b (outer site)
    P=[z() for _ in range(NB+1)]
    for it in range(D+2):
        Pn=[z() for _ in range(NB+1)]
        for b in range(1,NB+1):
            acc=mono(1,2*b) if outer else mono(1,0)
            for a in range(1,NB+1):
                acc=add(acc,mul(add(mono(1,2*max(a,b)),mul(mono(1,2*(a+b)),g)),P[a]))
            Pn[b]=mul(mono(2,2*b),acc)
        P=Pn
    return P
g=z()
for L in range(1,D): g=add(g,mono(1,2*L))   # q/(1-q) at y=1
def vecs(P,B0):
    mu=[];lam=[]
    for s in range(NS):
        m=mono(B0,2*s+1); ex=add(mono(B0,2*s),mono(B0,2*s+2))
        for b in range(1,NB+1):
            m=add(m,[Fr(u,2) for u in mul(P[b],add(mono(1,max(2*b-1,2*s+1)),mono(1,max(2*b+1,2*s+1))))])
            ex=add(ex,mul(P[b],add(mono(1,max(2*s,2*b)),mono(1,max(2*s+2,2*b)))))
        mu.append(m); lam.append(add(ex,sc(2,m)))
    return mu,lam
def travel(v):  # returns (I-T)^{-1} D_e v /x  as series vector  (T=D_e K)
    # w = D_e v + D_e K w, iterate
    e=[mono(2,2+2*s) for s in range(NS)]
    w=[z() for _ in range(NS)]
    for it in range(D+2):
        w=[add(mul(e[s],v[s]), mul(e[s], [sum(c) for c in zip(*[mul(mono(1,2*max(s,t)),w[t]) for t in range(NS)])])) for s in range(NS)]
    return [x[1:]+[0] for x in w]  # divide by x
def dot(a,b):
    r=z()
    for u,v in zip(a,b): r=add(r,mul(u,v))
    return r

def vecs3(P,B0s,B0z):
    mu=[];lam=[]
    for s in range(NS):
        m=mul(B0s,mono(1,2*s+1))
        ex=add(mul(B0z if s==0 else B0s,mono(1,2*s)),mul(B0s,mono(1,2*s+2)))
        for b in range(1,NB+1):
            m=add(m,[Fr(u,2) for u in mul(P[b],add(mono(1,max(2*b-1,2*s+1)),mono(1,max(2*b+1,2*s+1))))])
            ex=add(ex,mul(P[b],add(mono(1,max(2*s,2*b)),mono(1,max(2*s+2,2*b)))))
        mu.append(m); lam.append(add(ex,sc(2,m)))
    return mu,lam
import sys
fix=sys.argv[1]=='fix'
for yl in ('1','q'):
    g=z(); g0=z()
    for L in range(1,D):
        g=add(g,mono(1,2*L+(2*(L-1) if yl=='q' else 0)))
        g0=add(g0,mono(1,2*L+(2*L if (yl=='q' and fix) else (2*(L-1) if yl=='q' else 0))))
    P=bulk(g,1)
    B0s=mono(1,0); B0z=mono(1,0)
    for b in range(1,NB+1):
        B0s=add(B0s,mul(g,mul(mono(1,2*b),P[b]))); B0z=add(B0z,mul(g0,mul(mono(1,2*b),P[b])))
    mu,lam=vecs3(P,B0s,B0z)
    Fm=dot(mu,travel(lam))
    E=[add(l,sc(-2,m)) for l,m in zip(lam,mu)]
    near=[[Fr(c,2) for c in e] for e in E]
    far=[add(sc(2,m),e) for m,e in zip(mu,E)]
    Sn=dot(near,travel(far))
    print('y=',yl,'k>0',[int(c) for c in Fm[:D]]); print('y=',yl,'k<0',[int(c) for c in Sn[:D]])
