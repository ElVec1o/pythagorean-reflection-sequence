#!/usr/bin/env python3
import mpmath as mp, sys
mp.mp.dps=22
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def S(k,q,J=1200):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-30) and j>40: break
    return tot
SM=30
def pieces(q):
    sizes=list(range(1,SM+1)); n=len(sizes)
    M0=mp.matrix(n,n)
    for ai,a in enumerate(sizes):
        for bi,b in enumerate(sizes):
            M0[bi,ai]=2*q**b*q**max(a,b)
    A=mp.eye(n)-M0
    u=mp.matrix(n,1); v=mp.matrix(n,1)
    for bi,b in enumerate(sizes): u[bi,0]=2*q**(2*b)
    for ai,a in enumerate(sizes): v[ai,0]=q**a
    x=mp.lu_solve(A,u)
    h=sum(v[i,0]*x[i,0] for i in range(n))
    d=mp.det(A)
    return h,d
def fz(f,nmax,wlo=2.2,whi=30,step=0.06):
    roots=[]; prev=None; pq=None; w=mp.mpf(wlo)
    while len(roots)<nmax and w<whi:
        q=mp.e**(-2/w**2)
        try: val=f(q)
        except: val=None
        if val is not None and prev is not None and mp.sign(val)!=mp.sign(prev) and prev!=0:
            try:
                r=mp.findroot(f,(pq+q)/2)
                if 0<r<1 and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-9)): roots.append(r)
            except: pass
        prev=val if val is not None else prev; pq=q; w+=step
    return sorted(roots)
print('1-S1=0 (relaxed bulk):', [mp.nstr(r,9) for r in fz(lambda q:S(1,q)-1,5)]); sys.stdout.flush()
print('det(I-M0)=0 (gapless) :', [mp.nstr(r,9) for r in fz(lambda q:pieces(q)[1],5)]); sys.stdout.flush()
for lab,yf in [('y=1 ',lambda q:mp.mpf(1)),('y=q ',lambda q:q),('y=.3',lambda q:mp.mpf('0.3'))]:
    z=fz(lambda q:1-((q*yf(q))/(1-q*yf(q)))*pieces(q)[0],5)
    print(f'1-Phi*h=0 [{lab}]:', [mp.nstr(r,9) for r in z]); sys.stdout.flush()
print("ALLDONE"); sys.stdout.flush()
