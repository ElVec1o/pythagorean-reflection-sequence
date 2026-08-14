import mpmath as mp, sys
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
    X=mp.mpf(1);Y=mp.mpf(0); x=mp.mpf(0);y=mp.mpf(1); qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        Xn=X*(1+2*q2n)-Y*2*qn; Yn=X*2*q3n+Y*(1-2*q2n)
        xn=x*(1+2*q2n)-y*2*qn; yn=x*2*q3n+y*(1-2*q2n)
        X,Y,x,y=Xn,Yn,xn,yn
    return Y,y
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
sqrt2_8=mp.sqrt(2)/8
print(f"{'m':>3} {'tau':>9} {'t1/tau':>10} {'P12amp/(s2/8)':>13} {'Se_amp':>9} {'P12/E':>9} {'R/(t1.5sw)':>11} {'(.5(w-W)^2)/(t/4)':>16}",flush=True)
for m in [1,2,4,8,16,24,32]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=45+int(1.6*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int(55/(1-q))
    b0,b1,t0,t1=raw(q,N); P12,Se=cocycle(q,N)
    W=w*mp.e**(-tau/2); sinw=mp.sin(w); sinwW=mp.sin(w-W)
    p12amp=P12/(tau**mp.mpf('1.5')*sinw)
    seamp=Se/(mp.sqrt(tau/2)*sinw)
    E=mp.mpf('0.5')*(w-W)**2*sinw*sinwW; R=P12-E
    print(f"{m:>3} {float(tau):>9.2e} {float(t1/tau):>10.6f} {float(p12amp/sqrt2_8):>13.8f} {float(seamp):>9.6f} {float(P12/E):>9.6f} {float(R/(tau**mp.mpf('1.5')*sinw)):>11.2e} {float((mp.mpf('0.5')*(w-W)**2)/(tau/4)):>16.10f}",flush=True)
    mp.mp.dps=45
