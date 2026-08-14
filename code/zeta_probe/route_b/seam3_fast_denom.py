#!/usr/bin/env python3
"""
FAST denominator y-test using the determinant lemma.
K(a,b;y)=q^{max(a,b)} + q^{a+b} Phi(q,y),  Phi=qy/(1-qy).
M[b,a]=2q^b K(a,b;y) = M0[b,a] + Phi * u_b v_a,  u_b=2q^{2b}, v_a=q^a  (RANK-1 in Phi).
det(I-M) = det(I-M0) * (1 - Phi * v^T (I-M0)^{-1} u).
So zeros of det(I-M) are:
   (i) zeros of det(I-M0)  [the GAPLESS kernel denominator -- y-FREE], OR
   (ii) 1 - Phi(q,y) * h(q) = 0,  h(q)=v^T(I-M0)^{-1}u   [the y-DEPENDENT branch].
We compute BOTH families fast (one linear solve per q) and compare to 1-S_1.
"""
import mpmath as mp
mp.mp.dps=30

def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def S(k,q,J=2000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-40) and j>40: break
    return tot

def M0_solve(q,Smax=60):
    """return (I-M0)^{-1} action pieces: h=v^T (I-M0)^{-1} u, and det-sign proxy via lu."""
    sizes=list(range(1,Smax+1)); n=len(sizes); idx={s:i for i,s in enumerate(sizes)}
    M0=mp.matrix(n,n)
    for a in sizes:
        for b in sizes:
            M0[idx[b],idx[a]]=2*q**b*q**max(a,b)
    A=mp.eye(n)-M0
    u=mp.matrix(n,1); v=mp.matrix(n,1)
    for b in sizes: u[idx[b],0]=2*q**(2*b)
    for a in sizes: v[idx[a],0]=q**a
    x=mp.lu_solve(A,u)               # (I-M0)^{-1} u
    h=sum(v[i,0]*x[i,0] for i in range(n))
    return h

def h_func(q): return M0_solve(q)

def detM0(q,Smax=60):
    sizes=list(range(1,Smax+1)); n=len(sizes); idx={s:i for i,s in enumerate(sizes)}
    M0=mp.matrix(n,n)
    for a in sizes:
        for b in sizes:
            M0[idx[b],idx[a]]=2*q**b*q**max(a,b)
    return mp.det(mp.eye(n)-M0)

def fz(f,nmax,wlo=2.0,whi=120,step=0.05):
    roots=[]; prev=None; pq=None; w=mp.mpf(wlo)
    while len(roots)<nmax and w<whi:
        q=mp.e**(-2/w**2)
        try: val=f(q)
        except: val=None
        if val is not None and prev is not None and mp.sign(val)!=mp.sign(prev) and prev!=0:
            try:
                r=mp.findroot(f,(pq+q)/2)
                if 0<r<1 and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-12)): roots.append(r)
            except: pass
        prev=val; pq=q; w+=step
    return sorted(roots)

if __name__=="__main__":
    print("relaxed bulk poles 1-S1=0     :", [mp.nstr(r,10) for r in fz(lambda q:S(1,q)-1,6)])
    print("GAPLESS kernel det(I-M0)=0    :", [mp.nstr(r,10) for r in fz(lambda q:detM0(q),6)])
    print()
    print("y-DEPENDENT branch zeros: 1 - Phi(q,y) h(q) = 0")
    for lab,yf in [("y=1 ",lambda q:mp.mpf(1)),("y=q ",lambda q:q),("y=q^2",lambda q:q**2),("y=.3",lambda q:mp.mpf('0.3'))]:
        def g(q):
            Phi=(q*yf(q))/(1-q*yf(q))
            return 1 - Phi*h_func(q)
        print(f"   {lab}:", [mp.nstr(r,10) for r in fz(g,6)])
