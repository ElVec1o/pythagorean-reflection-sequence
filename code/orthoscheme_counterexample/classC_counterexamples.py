from fractions import Fraction as F
from collections import deque
import sys
N1=4
def comm(i,j): return abs(int(i)-int(j))>=2
def reduce_word(w):
    ch=True
    while ch:
        ch=False
        for i in range(len(w)):
            for j in range(i+1,len(w)):
                if w[i]==w[j] and all(comm(w[i],w[k]) for k in range(i+1,j)):
                    w=w[:i]+w[i+1:j]+w[j+1:]; ch=True; break
            if ch: break
    return w
def canon(w):
    seen={w}; q=deque([w]); best=w
    while q:
        x=q.popleft()
        if x<best: best=x
        for i in range(len(x)-1):
            if x[i]!=x[i+1] and comm(x[i],x[i+1]):
                y=x[:i]+x[i+1]+x[i]+x[i+2:]
                if y not in seen: seen.add(y); q.append(y)
    return best
def nf(w): return canon(reduce_word(w))
def Bf(i,j): return 1 if i==j else (-1 if abs(i-j)==1 else 0)
TG=[]
for i in range(N1):
    M=[[1 if r==c else 0 for c in range(N1)] for r in range(N1)]
    for c in range(N1): M[i][c]-=2*Bf(i,c)
    TG.append(tuple(tuple(r) for r in M))
TI=tuple(tuple(1 if i==j else 0 for j in range(N1)) for i in range(N1))
def tmul(A,B): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(N1)) for j in range(N1)) for i in range(N1))
def tword(w):
    M=TI
    for ch in w: M=tmul(M,TG[int(ch)])
    return M
def lin_refl(m,n):
    d=sum(x*x for x in m)
    return tuple(tuple((F(1) if i==j else F(0))-2*m[i]*m[j]/d for j in range(n)) for i in range(n))
def lgens(a):
    n=len(a); M=[]
    v=[F(0)]*n; v[0]=F(1); M.append(tuple(v))
    for j in range(1,n):
        v=[F(0)]*n; v[j-1]=F(a[j]); v[j]=F(-a[j-1]); M.append(tuple(v))
    v=[F(0)]*n; v[n-1]=F(1); M.append(tuple(v))
    return [lin_refl(m,n) for m in M]
def lmul(A,B,n): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)) for i in range(n))
def find_u(a,D=14):
    n=len(a); G=lgens(a)
    I=tuple(tuple(F(1) if i==j else F(0) for j in range(n)) for i in range(n))
    byword={"":I}; bymat={I:""}; front=[""]
    for d in range(1,D+1):
        new={}
        for w in front:
            X=byword[w]
            for gi in range(len(G)):
                nw=nf(w+str(gi))
                if len(nw)!=d or nw in byword or nw in new: continue
                new[nw]=lmul(X,G[gi],n)
        lvl={}
        for w,Y in new.items():
            if Y in bymat: return w,bymat[Y]
            if Y in lvl:   return w,lvl[Y]
            lvl[Y]=w
        byword.update(new)
        for w,Y in new.items(): bymat.setdefault(Y,w)
        front=list(new)
    return None,None
tuples=[(1,3,2),(2,3,9),(2,6,9),(3,1,5),(3,2,6),(4,9,7),(6,11,7)]
print(f"{'legs':>10}  {'|u|':>4}  u!=1 (Tits)  lin(u)=I   {'|c|':>4}  c!=1 (Tits)  rho_a(c)=1")
for a in tuples:
    n=len(a); w1,w2=find_u(list(a))
    if w1 is None: print(f"{str(a):>10}  no collision found"); continue
    u=w1+w2[::-1]
    G=lgens(list(a))
    I=tuple(tuple(F(1) if i==j else F(0) for j in range(n)) for i in range(n))
    M=I
    for ch in u: M=lmul(M,G[int(ch)],n)
    lin_ok = (M==I)
    unt = tword(u)!=TI
    g="0"; v=g+u+g[::-1]; c=u+v+u[::-1]+v[::-1]
    cnt = tword(c)!=TI
    # rho_a(c)=1 is forced: rho_a(u) is a translation, conjugates of translations are
    # translations, and translations commute.
    print(f"{str(a):>10}  {len(u):>4}  {str(unt):>11}  {str(lin_ok):>8}   {len(c):>4}  {str(cnt):>11}  {'forced' if (lin_ok and unt) else '-'}")
