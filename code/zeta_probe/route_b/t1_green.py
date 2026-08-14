import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])

# Green's function structure. The backward recursion for u (given v precomputed):
#   u[b-1] = u[b]*(1+2q2b) + qb*c_b + v[b]*(c_b+2qb*u[b])
#          = u[b]*(1+2q2b + 2qb v[b]) + c_b*(qb+v[b])
# Let A_b = 1+2q2b+2qb v[b],  B_b = qb+v[b].  Then u[b-1]=A_b u[b] + B_b c_b.
# u[N]=0. Unrolling forward from b=N down to 0:
#   u[0] = sum_{b=1}^{N} (prod_{b'=1}^{b-1} A_{b'}) * B_b c_b
# So G_b = prod_{b'=1}^{b-1} A_{b'} * B_b.   <-- Green's function in closed product form!

def raw_v(q,N):
    q=mp.mpf(q)
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; v[b-1]=vb
    return v,qp

for qf in ['0.80','0.92']:
    q=mp.mpf(qf); N=int(70/(1-q))
    v,qp=raw_v(q,N)
    A=[None]*(N+1); B=[None]*(N+1)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb
        A[b]=1+2*q2b+2*qb*v[b]; B[b]=qb+v[b]
    # G_b = prod_{b'=1}^{b-1} A[b'] * B[b]
    G=[None]*(N+1); pref=mp.mpf(1)
    for b in range(1,N+1):
        G[b]=pref*B[b]; pref*=A[b]
    t0=sum(2*qp[b]*G[b] for b in range(1,N+1))
    t1=sum(2*qp[b]**2*G[b] for b in range(1,N+1))
    # cross-check against direct raw
    def raw_src(q,N,csrc):
        v2,qp2=raw_v(q,N); u=[mp.mpf(0)]*(N+1)
        for b in range(N,0,-1):
            qb=qp2[b]; q2b=qb*qb
            c=csrc(b,qb,q2b)
            u[b-1]=u[b]*(1+2*q2b)+qb*c+v2[b]*(c+2*qb*u[b])
        return u[0]
    t0d=raw_src(q,N,lambda b,qb,q2b: 2*qb)
    t1d=raw_src(q,N,lambda b,qb,q2b: 2*q2b)
    print(f"q={qf}: t0={float(t0):.8f} (direct {float(t0d):.8f}) t1={float(t1):.8f} (direct {float(t1d):.8f})")
    print(f"       A[1..4]={[round(float(A[b]),5) for b in range(1,5)]}  B[1..4]={[round(float(B[b]),5) for b in range(1,5)]}")
