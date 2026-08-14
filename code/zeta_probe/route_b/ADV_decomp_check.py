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
    X=mp.mpf(1);Y=mp.mpf(0); x=mp.mpf(0);y=mp.mpf(1); qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        Xn=X*(1+2*q2n)-Y*2*qn; Yn=X*2*q3n+Y*(1-2*q2n)
        xn=x*(1+2*q2n)-y*2*qn; yn=x*2*q3n+y*(1-2*q2n)
        X,Y,x,y=Xn,Yn,xn,yn
    return Y,y   # P12,Se
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# CRUX: is P12's leading order ELEMENTARY E=(1/2)(w-W)^2 sin w sin(w-W), R=P12-E strictly subleading?
# Compare to the alternate framing: P12 = pure tau^{3/2} saddle. The memory's "ELEMENTARY-RATIO route"
# claims E/E_S=(1/2)(w-W)^2 EXACT and P12/E->1 with R/(tau^1.5 sinw)->0.
print(f"{'m':>3} {'tau':>9} {'P12/E':>11} {'R/(t^1.5 sw)':>13} {'(1/2)(w-W)^2/(t/4)':>18} {'t1/tau':>10}")
for m in [1,2,4,8,16,24,32,40,56,72]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.5*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int(70/(1-q))
    b0,b1,t0,t1=raw(q,N); P12,Se=cocycle(q,N)
    W=w*mp.e**(-tau/2)
    sinw=mp.sin(w); sinwW=mp.sin(w-W)
    E=mp.mpf('0.5')*(w-W)**2*sinw*sinwW
    R=P12-E
    ratio_PE = P12/E
    R_scaled = R/(tau**mp.mpf('1.5')*sinw)
    elem_ratio = (mp.mpf('0.5')*(w-W)**2)/(tau/4)
    print(f"{m:>3} {float(tau):>9.2e} {float(ratio_PE):>11.7f} {float(R_scaled):>13.2e} {float(elem_ratio):>18.10f} {float(t1/tau):>10.6f}")
    mp.mp.dps=60
