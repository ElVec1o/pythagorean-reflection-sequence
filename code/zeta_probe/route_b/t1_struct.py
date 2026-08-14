import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])

# Understand the source-1 recursion. From raw():
#   v[b-1] = (v[b](1+2q2b)+2q3b)/dd,  dd=1-2q2b-2qb v[b]
#   u1[b-1] = u1[b](1+2q2b)+qb*c1 + vb*(c1+2qb u1[b]),  c1=2q2b
#   t1 = u1[0]
# This is the SAME backward recursion as u0 but with source c1=2q2b (vs c0=2qb for u0/t0).
# Note t0=u0[0]=b1=S1b/(1-S1b)=S1b/Se.  So u0[0]/source-0 gives S1b/Se.
# Let's see if u1 relates to a SHIFTED version.

# KEY: c1=2q2b = q^b * c0 (since c0=2qb).  And c0=2qb.
# So source-1 = (extra q^b weight) on source-0. This is a "k-shift" or derivative in disguise.

# Build the full u0,u1 arrays and inspect
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
    print(f"q={qf}: u0[0]={float(u0[0]):.6f} u1[0]={float(u1[0]):.6f}")
    # check ratio u1[b]/u0[b]
    print("  b   u0[b]      u1[b]     u1/u0    qp[b]")
    for b in [0,1,2,3,5,10]:
        r=float(u1[b]/u0[b]) if u0[b]!=0 else 0
        print(f"  {b:>2} {float(u0[b]):>10.5f} {float(u1[b]):>10.5f} {r:>8.4f} {float(qp[b]):>8.5f}")
