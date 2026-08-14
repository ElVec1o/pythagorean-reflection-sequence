import mpmath as mp
mp.mp.dps=60
def raw(q,N):
    q=mp.mpf(q)
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
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-120) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# KEY new idea: t1 should be obtainable from the SAME block family but it's the source-1
# resolvent's BOUNDARY (b=0) value, whereas l1 is its DIAGONAL (sum) value.
# For source-0: boundary b0... no. Let me instead get t1 from c=t0 b1 - b0 t1 and the fact that
# the relaxed-V analog: the bulk block B(q,y) is KNOWN in closed form via Sb. Let me reconstruct
# the FULL bulk block B(q,y)=Sigma_0/(1-Sigma_1) style and read off t1 as the y-coefficient.
# Actually simpler: numerically, is t1 = (Sb(0)-2*q*Sb-ish)? Let me try a derivative.
# theta f = (1/2) q f'(q)*? Use numerical q-derivative of Sb(1):
def dq(f,q,h=mp.mpf(10)**-25):
    return (f(q+h)-f(q-h))/(2*h)
print("Test t1 against q-derivatives / theta of blocks:")
print(f"{'tau':>8} {'t1':>14} {'qd/dq Sb1':>16} {'qd/dq Sb0':>16}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02']]:
    q=mp.e**(-tau); N=int(70/(1-q))
    b0,l1,t0,t1=raw(q,N)
    d1=q*dq(lambda x:Sb(1,x),q); d0=q*dq(lambda x:Sb(0,x),q)
    print(f"{float(tau):>8.4f} {mp.nstr(t1,10):>14} {mp.nstr(d1,10):>16} {mp.nstr(d0,10):>16}")
print()
# Different tack: t1 is fully determined by the v-array & u1 recursion. Since l1=S1b/(1-S1b)=t0,
# and the resolvent matrix is [[l0,?],[t0,?]] with c=t0*l1-l0*t1. Maybe there's a determinant
# identity: l0*? - t0*t1 = simple. The bulk block is a 2x2 Mobius; its DET might be clean.
# B(g)=(b0+g c)/(1-g t1). Cross-ratio invariant. Let me compute the "second" resolvent entry.
# Actually the cleanest: s=g_V t1. We found s->1/4. Let me just test s as a block ratio at poles
# using ONLY Sb, since at poles S1b is bounded away from 1 (Se=1-S1b !=0).
print("At poles: express s via blocks. s=g_V t1. Test s*(1-S1b)/S1b, s*(1-S1b), etc:")
print(f"{'m':>3} {'tau':>9} {'s':>12} {'S1b':>11} {'s*(1-S1b)':>12} {'s*(1-S1b)/S1b':>14}")
for m in [1,2,4,8,16,32]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); gV=q/(1-q)
    N=int(70/(1-q)); b0,l1,t0,t1=raw(q,N); s=gV*t1; s1b=Sb(1,q)
    print(f"{m:>3} {float(tau):>9.5f} {float(s):>12.8f} {float(s1b):>11.7f} {float(s*(1-s1b)):>12.7f} {float(s*(1-s1b)/s1b):>14.7f}")
