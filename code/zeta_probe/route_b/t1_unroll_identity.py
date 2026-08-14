import mpmath as mp
mp.mp.dps=80
# CORRECTED: in raw, vb=v[b-1] (the newly computed one). So:
# u[b-1]=u[b](1+2q2b)+qb*c + v[b-1]*(c+2qb u[b]) = u[b][(1+2q2b)+2qb v[b-1]] + c(qb+v[b-1]).
# A_b=(1+2q2b)+2qb v[b-1], f_b=c(qb+v[b-1]).
def direct(q,N,k):
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c=2*qb**k
        u[b-1]=u[b]*(1+2*q2b)+qb*c+vb*(c+2*qb*u[b]); v[b-1]=vb
    return u[0],v,qp
def unroll(q,N,k):
    _,v,qp=direct(q,N,k)
    A=[mp.mpf(0)]*(N+1)
    for b in range(1,N+1):
        qb=qp[b]; A[b]=(1+2*qb*qb)+2*qb*v[b-1]   # v[b-1]
    s=mp.mpf(0); prodA=mp.mpf(1)
    for b in range(1,N+1):
        c=2*qp[b]**k
        s+=prodA*c*(qp[b]+v[b-1])
        prodA*=A[b]
    return s
q=mp.mpf('0.7')
for N in [10,40]:
    d,_,_=direct(q,N,2); u=unroll(q,N,2)
    print(f"N={N}: direct={float(d):.12f} unroll={float(u):.12f} diff={float(d-u):.2e}")
