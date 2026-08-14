import mpmath as mp
mp.mp.dps=60

# Re-read raw EXACTLY:
#   for b in N..1:
#     dd=1-2q2b-2qb*v[b]
#     vb=(v[b](1+2q2b)+2q3b)/dd                  # this is v[b-1]
#     u1[b-1]=u1[b](1+2q2b)+qb*c1 + vb*(c1+2qb*u1[b])   # uses vb=v[b-1], NOT v[b]!
# So the coefficient uses the NEWLY computed vb=v[b-1].
#   u[b-1] = u[b](1+2q2b+2qb*vb) + c_b*(qb+vb)
# where vb=v[b-1]. So A_b uses v[b-1], B_b uses v[b-1].

def raw_full(q,N):
    q=mp.mpf(q)
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    return u0,u1,v,qp

for qf in ['0.80','0.92']:
    q=mp.mpf(qf); N=int(70/(1-q))
    u0,u1,v,qp=raw_full(q,N)
    # A_b=1+2q2b+2qb*v[b-1], B_b=qb+v[b-1]
    A=[None]*(N+1); B=[None]*(N+1)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb
        A[b]=1+2*q2b+2*qb*v[b-1]; B[b]=qb+v[b-1]
    G=[None]*(N+1); pref=mp.mpf(1)
    for b in range(1,N+1):
        G[b]=pref*B[b]; pref*=A[b]
    t0=sum(2*qp[b]*G[b] for b in range(1,N+1))
    t1=sum(2*qp[b]**2*G[b] for b in range(1,N+1))
    print(f"q={qf}: raw t0={float(u0[0]):.8f} green t0={float(t0):.8f} | raw t1={float(u1[0]):.8f} green t1={float(t1):.8f}")
