import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])

# The memory note (D4,D2) tells us:
#   b1=t0=u0[0]=S1b/Se.  source-0 has c0=2qb.
# The forward sum form (from memory): L_b first-order system, b0 = source-0 L.
# u0[0] is a DIFFERENT contraction (it's the T-value, not L). 
# Both u0[0]=t0 and u1[0]=t1 are produced by the SAME backward recursion, sources c0,c1.
#
# Let's find a "transfer" telescoping. Define for source-c the output T(c)=u[0].
# By linearity in the source, T is LINEAR in the source sequence {c_b}.
# t0 = T({2qb}),  t1 = T({2q2b}) = T({2qb * qb}).
# 
# Idea: T({c_b}) = sum_b G_b c_b  for a Green's function G_b (indep of source).
# Then t0 = sum_b G_b 2qb, t1 = sum_b G_b 2q2b.
# G_b can be extracted by probing with delta sources.

def raw_src(q,N,csrc):
    # csrc: function b-> source value c_b (b=1..N)
    q=mp.mpf(q)
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c=csrc(b,qb,q2b)
        u[b-1]=u[b]*(1+2*q2b)+qb*c+vb*(c+2*qb*u[b]); v[b-1]=vb
    return u[0]

for qf in ['0.80']:
    q=mp.mpf(qf); N=int(70/(1-q))
    t0=raw_src(q,N,lambda b,qb,q2b: 2*qb)
    t1=raw_src(q,N,lambda b,qb,q2b: 2*q2b)
    print(f"q={qf}: t0={float(t0):.7f} t1={float(t1):.7f}")
    # Extract Green's function G_b: source = delta at b0 with unit amplitude
    print("  Green's fn G_b (response u[0] to unit delta source at b):")
    Gsum0=mp.mpf(0); Gsum1=mp.mpf(0)
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    for bb in [1,2,3,4,5,8]:
        G=raw_src(q,N,lambda b,qb,q2b,bb=bb: (1 if b==bb else 0))
        print(f"    b={bb}: G_b={float(G):>12.6f}   2qb*G={float(2*qp[bb]*G):>10.6f}  2q2b*G={float(2*qp[bb]**2*G):>10.6f}")
    # verify t0 = sum_b 2qb G_b
    for bb in range(1,N+1):
        G=raw_src(q,N,lambda b,qb,q2b,bb=bb: (1 if b==bb else 0))
        Gsum0+=2*qp[bb]*G; Gsum1+=2*qp[bb]**2*G
    print(f"  reconstructed t0={float(Gsum0):.7f} (should be {float(t0):.7f})")
    print(f"  reconstructed t1={float(Gsum1):.7f} (should be {float(t1):.7f})")
