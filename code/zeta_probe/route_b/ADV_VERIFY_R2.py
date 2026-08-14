"""
INDEPENDENT adversarial verification of R2: t1 ~ tau/4.
Recompute everything from scratch. Test:
 (1) t1 = P12/Se exact (dictionary D5).
 (2) E_S = sin w sin(w-W), E = (1/2)(w-W)^2 sin w sin(w-W), W = w e^{-tau/2}.
 (3) Is the LEADING constant of P12 (=> t1~tau/4) elementary (from E), or does the
     saddle remainder R = P12 - E contribute at leading order?
 (4) Does R/(tau^{3/2} sin w) -> 0 (R strictly subleading) -- or -> nonzero const?
 (5) (1/2)(w-W)^2 / (tau/4) -> 1 ?
 (6) Sanity: P12 != (tau/4) So off the poles (no false q-identity).
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
    # convA columns. (x,y)=col1 start (0,1)->P12=Y? track per memory: P22=Se=y, P12=Y of col2
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y   # P12, P22=Se

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("=== (1) exactness t1==P12/Se ;  (2)-(5) decomposition ===")
print(f"{'m':>3} {'tau':>9} {'|t1-P12/Se|':>12} {'t1/tau':>9} {'(.5(w-W)^2)/(tau/4)':>18} {'P12/(tau1.5 sinw)':>17} {'R/(tau1.5 sinw)':>16}")
for m in [1,2,4,8,16,24,32,40]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.5*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int(70/(1-q))
    b0,b1,t0,t1=raw(q,N); P12,Se=cocycle(q,N)
    W=w*mp.e**(-tau/2)
    sinw=mp.sin(w)
    E_S=mp.sin(w)*mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*E_S
    R=P12-E
    err_exact=abs(t1-P12/Se)
    ratio_elem=(mp.mpf(1)/2*(w-W)**2)/(tau/4)
    P12_scaled=P12/(tau**mp.mpf('1.5')*sinw)
    R_scaled=R/(tau**mp.mpf('1.5')*sinw)
    print(f"{m:>3} {float(tau):>9.2e} {float(err_exact):>12.2e} {float(t1/tau):>9.6f} {float(ratio_elem):>18.12f} {float(P12_scaled):>17.10f} {float(R_scaled):>16.3e}")
    mp.mp.dps=50

print()
print("1/(4 sqrt2) =", float(1/(4*mp.sqrt(2))))
print("(1/2)*(1/2)^1.5 =", float(mp.mpf(1)/2*(mp.mpf(1)/2)**mp.mpf('1.5')))
