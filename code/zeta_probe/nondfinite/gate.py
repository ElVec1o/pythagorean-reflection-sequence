import cmath, math
from ev import series
def Y3(q):
    s=0j; p1=1+0j; p2=1+0j
    for k in range(400):
        t=(-2)**k*(1-q)**k*q**(k*k+3*k)/(p1*p2); s+=t
        p1*=(1-q**(2*k+2)); p2*=(1-q**(5+2*k))
        if abs(t)<1e-18 and k>5: break
    return s
def DU(q):  # (1-q^2)(1-q^3) Se - 2 q^4 Y3  ; zero <=> 1-gU t1=0 (when Se!=0)
    return (1-q*q)*(1-q**3)*series(q,1)[0]-2*q**4*Y3(q)
def DV(q):  # (1-q)(1-q^3) Se - 2 q^4 Y3 ; gV=q/(1-q)
    return (1-q)*(1-q**3)*series(q,1)[0]-2*q**4*Y3(q)
def wind(f,r,n):
    tot=0; prev=None; m=1e300
    for j in range(n+1):
        v=f(r*cmath.exp(2j*math.pi*j/n)); m=min(m,abs(v))
        if prev is not None: tot+=cmath.phase(v/prev)
        prev=v
    return tot/2/math.pi, m
for name,f in [('1-gU t1',DU),('1-gV t1',DV)]:
    for r in [0.45,0.6,0.7,0.8,0.9,0.93]:
        w,m=wind(f,r,6000); print(name,r,round(w,3),'%.2e'%m,flush=True)
# real sign scan
import itertools
xs=[i/2000 for i in range(1,1990)]
for name,f in [('DU',DU),('DV',DV)]:
    ch=[x for a,x in zip(xs,xs[1:]) if (f(a).real>0)!=(f(x).real>0)]
    print(name,'real sign changes on (0,0.995):',ch[:10])
