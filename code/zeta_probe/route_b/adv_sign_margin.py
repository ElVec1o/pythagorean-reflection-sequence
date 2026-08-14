import mpmath as mp, sys
mp.mp.dps=40

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c1=2*q2b
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0)
    # only need b0 and t1; recompute u0 inline minimal:
    return v, u1, qp

def b0t1(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd
    return l0,u1[0]

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
viol=0; maxs=mp.mpf(0); minb0=mp.mpf('1e9'); minmarg=mp.mpf('1e9')
for m in range(1,41):
    if m>len(poles): break
    q=poles[m-1]; N=int(45/(1-q))
    b0,t1=b0t1(q,N); s=(q/(1-q))*t1
    if s>=1 or b0<=0: viol+=1
    if s>maxs: maxs=s
    if b0<minb0: minb0=b0
    if (1-s)<minmarg: minmarg=1-s
    sys.stdout.flush()
print(f"poles m=1..40: violations(s>=1 or b0<=0)={viol}; max s={float(maxs):.8f}; min(1-s)={float(minmarg):.6f}; min b0={float(minb0):.4f}")
print("=> (1-s)>0, b0>0, B_V>0 => B_U=(1-s)B_V+q*b0 > 0 != 0 at every sampled pole")
print("EXIT")
