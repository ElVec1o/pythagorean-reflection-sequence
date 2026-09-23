# Bivariate corrected model (model55 'fix' for k!=0, w0.py for k=0) with symbolic y.
# Variables: x and Y with y = x^2 Y, so x-degree = l_T = lR + 2c and truncation at x^D is exact.
# Series: int64 array A[n, c] = [x^n Y^c].  NO enumeration here (model arithmetic only).
import sys, numpy as np
D=int(sys.argv[1]); H=D//2+2; W2=2*H
def z(): return np.zeros((D+1,H),dtype=np.int64)
def mono(c,e,yc=0):   # c * x^e * y^yc  (y = x^2 Y)
    r=z(); e2=e+2*yc
    if 0<=e2<=D and yc<H: r[e2,yc]=c
    return r
def mul(a,b):
    fa=np.zeros((D+1,W2),dtype=np.int64); fa[:,:H]=a
    fb=np.zeros((D+1,W2),dtype=np.int64); fb[:,:H]=b
    c=np.convolve(fa.ravel(),fb.ravel())[:(D+1)*W2].reshape(D+1,W2)
    assert not c[:,H:].any() or True
    return c[:,:H].copy()
def half(a):
    assert not (a%2).any(); return a//2
NB=D//2+2; NS=D//2+2
g=z()
for L in range(1,D+1): g=g+mono(1,2*L,L-1)          # q^L y^(L-1)
Gr=mul(g,mono(1,0,1))                                # y g = sum q^L y^L
P=[z() for _ in range(NB+1)]
for it in range(D+2):
    Pn=[z() for _ in range(NB+1)]
    for b in range(1,NB+1):
        acc=mono(1,2*b)
        for a in range(1,NB+1):
            if P[a].any(): acc=acc+mul(mono(1,2*max(a,b))+mul(mono(1,2*(a+b)),g),P[a])
        Pn[b]=mul(mono(2,2*b),acc)
    if all((x==y).all() for x,y in zip(P,Pn)): break
    P=Pn
S=z()
for b in range(1,NB+1): S=S+mul(mono(1,2*b),P[b])
gS=mul(g,S); GrS=mul(Gr,S)
B0s=mono(1,0)+gS; B0z=mono(1,0)+GrS
mu=[];lam=[]
for s in range(NS):
    m=mul(B0s,mono(1,2*s+1)); ex=mul(B0z if s==0 else B0s,mono(1,2*s))+mul(B0s,mono(1,2*s+2))
    for b in range(1,NB+1):
        m=m+half(mul(P[b],mono(1,max(2*b-1,2*s+1))+mono(1,max(2*b+1,2*s+1))))
        ex=ex+mul(P[b],mono(1,max(2*s,2*b))+mono(1,max(2*s+2,2*b)))
    mu.append(m); lam.append(ex+2*m)
def travel(v):
    e=[mono(2,2+2*s) for s in range(NS)]; w=[z() for _ in range(NS)]
    for it in range(D+2):
        w=[mul(e[s],v[s]+sum(mul(mono(1,2*max(s,t)),w[t]) for t in range(NS))) for s in range(NS)]
    out=[]
    for x in w:
        r=z(); r[:-1]=x[1:]; out.append(r)   # divide by x; top row x^D unknown
    return out
def dot(a,b):
    r=z()
    for u,v in zip(a,b): r=r+mul(u,v)
    return r
Wp=dot(mu,travel(lam))
E=[l-2*m for l,m in zip(lam,mu)]
Wm=half(dot(E,travel(lam)))
# k=0 (w0.py translated, y symbolic)
Ls=[(0,mono(1,0),'E'),(0,gS,'Z')]+[(sg*2*a,half(P[a]),'N') for a in range(1,NB+1) for sg in (1,-1)]
Rs=[(0,mono(1,0),'E'),(0,GrS,'Z')]+[(sg*2*b,half(P[b]),'N') for b in range(1,NB+1) for sg in (1,-1)]
W0=z()
for e in (1,-1):
  for dl in (0,1):
    for (u,wl,kl) in Ls:
      for (v,wr,kr) in Rs:
        j=max(abs(u-1+(e if dl==0 else 0)),abs(v-(e if dl==1 else 0)))
        if j>D: continue
        wr2=wr
        if kr=='Z':
            wr2=GrS if (e==1 and dl==0) else gS
            if dl==0 and kl=='N':
                if e==1: wr2=gS
                elif u==2: wr2=GrS
        W0=W0+mul(mono(1,j),mul(wl,wr2))
np.save('model_D%d.npy'%D,np.stack([Wm,W0,Wp]))   # index sg+1; valid rows n<=D-1 (k!=0), n<=D (k=0)
print('done')
