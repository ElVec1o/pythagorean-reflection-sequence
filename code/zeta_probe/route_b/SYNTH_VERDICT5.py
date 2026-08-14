"""
PART 8 (CLEANEST form): test  P12 = (1/2)(w-W)^2 * Se + Rho.
If Rho = o(tau^{3/2}) i.e. Rho/Se -> 0 FASTER than the leading, then
   t1 = P12/Se = (1/2)(w-W)^2 + Rho/Se,
and (1/2)(w-W)^2 = (1/2)w^2(1-e^{-tau/2})^2 is EXACT ELEMENTARY -> tau/4.
The correction Rho/Se -> 0 by a BOUND (no saddle constant) IFF Rho is genuinely subleading to (tau/4)*Se.

This is the sharpest possible statement: t1 - (1/2)(w-W)^2 = Rho/Se. Measure its order.
Crucially compare (1/2)(w-W)^2 directly to t1 (NO reference to lem:cos saddle value at all).
"""
import mpmath as mp

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0); l1=mp.mpf(0)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
    return l0,l1,u0[0],u1[0]

def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
import math
def slope(xs,ys):
    lx=[math.log(x) for x in xs]; ly=[math.log(abs(y)) for y in ys]
    n=len(lx); sx=sum(lx); sy=sum(ly); sxx=sum(t*t for t in lx); sxy=sum(lx[i]*ly[i] for i in range(n))
    return (n*sxy-sx*sy)/(n*sxx-sx*sx)

print("="*112)
print("PART 8 -- P12 = (1/2)(w-W)^2 * Se + Rho.  t1 - (1/2)(w-W)^2 = Rho/Se.  Is this -> 0 by a BOUND?")
print("="*112)
print(f"{'m':>3} {'tau':>10} {'t1':>13} {'(1/2)(w-W)^2':>14} {'t1-(1/2)(w-W)^2':>16} {'/tau^2':>9} {'Rho=P12-..Se':>13} {'Rho/Se /tau^2':>13}")
taus=[]; difs=[]; rhos=[]
for m in [4,8,12,16,20,24,28,32]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=90+int(3.2*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(120/(1-q))
    W=w*mp.e**(-tau/2)
    b0,b1,t0,t1=raw(q,N); P12,Se,P11,P21=cocycle(q,N)
    half=mp.mpf(1)/2*(w-W)**2
    dif=t1-half
    Rho=P12-half*Se
    taus.append(float(tau)); difs.append(abs(float(dif))); rhos.append(abs(float(Rho)))
    print(f"{m:>3} {float(tau):>10.3e} {float(t1):>13.8f} {float(half):>14.9f} {float(dif):>16.4e} {float(dif/tau**2):>9.5f} {float(Rho):>13.4e} {float((Rho/Se)/tau**2):>13.6f}")
    mp.mp.dps=90
print()
print(f"  slope(|t1 - (1/2)(w-W)^2|) vs tau = {slope(taus,difs):.3f}")
print(f"  slope(|Rho=P12-(1/2)(w-W)^2 Se|)  = {slope(taus,rhos):.3f}   (Se~tau^0.5, so Rho/Se order = slope-0.5)")
print()
print("  t1 - (1/2)(w-W)^2 = Rho/Se. If this is O(tau^2) (slope~2), then since (1/2)(w-W)^2 ~ tau/4,")
print("  the RELATIVE correction is O(tau) -> 0. The leading (1/2)(w-W)^2 is EXACT ELEMENTARY (no lem:cos at all).")
print("  Rho/Se -> 0 needs ONLY |Rho|=o(tau^{3/2})  (a BOUND on the source-1 cocycle remainder, lem:cos-class).")
