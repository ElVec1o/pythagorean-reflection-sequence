"""
R2 reduction: t1 ~ tau/4 along the travel poles, reduced to PROVEN bulk blocks.

DICTIONARY (machine-verified elsewhere): t1 = P12/Se,  Se = 1 - S1b,  So = (p/2q) S0b.
b0 = S0b/(1-S1b) was reduced to V's footing via S0b ~ w sin w (PROVEN) and Se ~ sqrt(tau/2) sin w (lem:cos).

NEW (this script): along the travel poles
   (A)  P12 ~ (tau/4) * So       [(P12/So)/(tau/4) -> 1 ;  = 1 + (1/4)tau + ...]
   (B)  So ~ Se   i.e. So/Se -> 1 [proven-block ratio; = 1 + (1/2)tau + ...]
=> t1 = P12/Se = (P12/So)*(So/Se) ~ (tau/4)*1 = tau/4.   QED (modulo (A),(B) at lem:cos level)

(A) is the cocycle-saddle estimate. NOT an exact q-identity (the tau=-ln q factor forbids a
q-rational closed form -- verified: P12 != (tau/4)So off the poles). It is the SAME class of
WKB/saddle statement as lem:cos. (B) is the proven-block companion (So,Se both ~ sqrt(tau/2) sinw).
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
    return Y,y   # P12, P22=Se
def Se_So(q,J=None):
    if J is None: J=int(8*mp.sqrt(2/(-mp.log(q))))+200
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0); poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    for j in range(0,J):
        Se+=(-2*onem)**j*q**(j*(j+1))/poch[2*j]
        So+=(-2*onem)**j*q**(j*(j+2))*onem/poch[2*j+1]
    return Se,So
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
print(f"{'m':>3} {'tau':>9} {'t1_raw':>13} {'(P12/So)(So/Se)':>16} {'(P12/So)/(tau/4)':>16} {'So/Se':>10} {'t1/tau':>9}")
for m in [1,2,4,8,16,24,32,40]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=50+int(2.2*float(w)); q=poles[m-1]; tau=-mp.log(q); N=int(60/(1-q))
    b0,b1,t0,t1=raw(q,N); P12,Se=cocycle(q,N); _,So=Se_So(q)
    red=(P12/So)*(So/Se)
    print(f"{m:>3} {float(tau):>9.2e} {float(t1):>13.8f} {float(red):>16.8f} {float((P12/So)/(tau/4)):>16.10f} {float(So/Se):>10.7f} {float(t1/tau):>9.6f}")
    mp.mp.dps=50
