import mpmath as mp
mp.mp.dps=30
def raw(q,N):
    qp=[mp.mpf(1)]*(N+1)
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
def SeSo(q,J):
    p=1-q; poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    Se=sum((-2*p)**j*q**(j*(j+1))/poch[2*j] for j in range(J))
    So=sum((-2*p)**j*q**(j*(j+2))*p/poch[2*j+1] for j in range(J))
    return Se,So
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x  #P12,P22,P11,P21

print("="*90)
print("PART 1: EXACT CLOSED FORMS vs raw() at generic q  [b0=(2q/p)So/Se ; t1=P12/P22 ; P22=Se]")
print("="*90)
for qf in ['0.85','0.9','0.93','0.97','0.99','0.995']:
    q=mp.mpf(qf); N=int(50/(1-q)); p=1-q; J=int(70/(1-q))
    b0,b1,t0,t1=raw(q,N)
    Se,So=SeSo(q,J); P12,P22,P11,P21=cocycle(q,N)
    b0f=(2*q/p)*So/Se; t1f=P12/P22
    print(f"q={qf}: b0 raw={float(b0):+.8f} formula={float(b0f):+.8f} relerr={float(abs(b0-b0f)/abs(b0)):.1e} | "
          f"t1 raw={float(t1):+.8f} formula={float(t1f):+.8f} relerr={float(abs(t1-t1f)/abs(t1)):.1e} | P22-Se={float(P22-Se):.1e}")

print("="*90)
print("PART 2: TRAVEL-POLE LIMITS  b0*tau->2 and s->1/4, with reductions")
print("="*90)
poles=[mp.mpf(l.strip()) for l in open('poles.txt')]
print(f"{'m':>2} {'w':>8} {'b0*tau':>12} {'So/Se':>10} {'s':>12} {'P12/(p Se)':>12} {'b0*tau err':>11} {'s-1/4':>11}")
for i,q in enumerate(poles[:14]):
    N=int(50/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q; J=int(8*w)+60
    b0,b1,t0,t1=raw(q,N); gV=q/(1-q); s=gV*t1
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N)
    print(f"{i:>2} {float(w):>8.3f} {float(b0*tau):>12.8f} {float(So/Se):>10.6f} {float(s):>12.8f} {float(P12/(p*Se)):>12.8f} {float(abs(b0*tau-2)):>11.1e} {float(s-mp.mpf(1)/4):>11.1e}")
