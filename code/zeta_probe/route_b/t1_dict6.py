import mpmath as mp
mp.mp.dps=70
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
    return l0,l1,u0[0],u1[0],v[0]
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-140) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
# v[0] is the Riccati value at b=0. b0=l0, b1=l1=t0=S1b/D. The block B(q,y)=(b0+g c)/(1-g t1),
# c=t0 b1 - b0 t1.  Pole at g=1/t1, i.e s=g_V t1.
# Maybe v[0] is the clean block! Test v[0] vs S1b and against t1.
print("v[0] (Riccati boundary) vs blocks; and relation to t1:")
print(f"{'tau':>8} {'v0':>14} {'t1':>14} {'S1b':>12} {'v0/(1-?)':>0}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    q=mp.e**(-tau); N=int(70/(1-q))
    l0,l1,t0,t1,v0=raw(q,N)
    print(f"{float(tau):>8.4f} {mp.nstr(v0,10):>14} {mp.nstr(t1,10):>14} {mp.nstr(Sb(1,q),8):>12}  v0/t1={mp.nstr(v0/t1,8)}  v0/S1b={mp.nstr(v0/Sb(1,q),8)}")
print()
# Determinant route: the cocycle [[l0+?]] ... let me test the cross-quantity l0*t1 - l1*t0 (=det-like)
print("Determinant-type combos (look for clean block):")
print(f"{'tau':>8} {'l0*t1-l1*t0':>16} {'l1^2-l0*?':>0}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    q=mp.e**(-tau); N=int(70/(1-q))
    l0,l1,t0,t1,v0=raw(q,N)
    D=1-Sb(1,q)
    print(f"{float(tau):>8.4f} l0t1-l1t0={mp.nstr(l0*t1-l1*t0,10):>14}  c=t0*l1-l0*t1={mp.nstr(t0*l1-l0*t1,10)}  c*D={mp.nstr((t0*l1-l0*t1)*D,10)}  c*D^2={mp.nstr((t0*l1-l0*t1)*D*D,10)}")
print()
# c = t0*b1 - b0*t1 = l1*l1 - l0*t1 (since t0=l1,b1=l1). c*D^2 maybe clean. test:
print("c=l1^2-l0*t1, and c*D^2 vs blocks (S0b,S1b):")
print(f"{'tau':>8} {'c':>14} {'c*D^2':>14} {'S1b^2':>12} {'S0b':>12} {'cD^2 vs S1b^2-S0b*?':>0}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    q=mp.e**(-tau); N=int(70/(1-q))
    l0,l1,t0,t1,v0=raw(q,N)
    s0b=Sb(0,q);s1b=Sb(1,q);D=1-s1b
    c=t0*l1-l0*t1; cD2=c*D*D
    print(f"{float(tau):>8.4f} {mp.nstr(c,9):>14} {mp.nstr(cD2,9):>14} {mp.nstr(s1b**2,8):>12} {mp.nstr(s0b,8):>12}  cD2-(S1b^2)={mp.nstr(cD2-s1b**2,4)}  cD2/S0b={mp.nstr(cD2/s0b,6)}")
