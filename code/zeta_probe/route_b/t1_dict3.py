import mpmath as mp
mp.mp.dps=90
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
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-170) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# We have l0=S0b/(1-S1b), l1=S1b/(1-S1b).  Now t0=u0[0], t1=u1[0].
# These are the b=0 values of the backward source-dressings (the "incoming" amplitudes).
# Note c=t0*b1-b0*t1 with b1=l1. Let me hunt t0,t1 directly.
# Guess: t0,t1 are also block ratios. Test t0*(1-S1b), t1*(1-S1b):
print("t0,t1 numerators (multiply by 1-S1b):")
print(f"{'tau':>8} {'t0':>13} {'t0*(1-S1b)':>14} {'t1':>13} {'t1*(1-S1b)':>14}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01','0.003']]:
    q=mp.e**(-tau); N=int(70/(1-q))
    b0,l1,t0,t1=raw(q,N); D=1-Sb(1,q)
    print(f"{float(tau):>8.4f} {mp.nstr(t0,9):>13} {mp.nstr(t0*D,9):>14} {mp.nstr(t1,9):>13} {mp.nstr(t1*D,9):>14}")
print()
# t0*(1-S1b) and t1*(1-S1b) -- recognize. Compare to Sb(0),Sb(1),Sb(2) and q-powers.
print("Recognize t0*(1-S1b) =: N0  and t1*(1-S1b) =: N1. Compare to blocks:")
print(f"{'tau':>8} {'N0':>13} {'N1':>13} {'Sb0*(1-q)/2q':>13} {'(Sb1-?)':>10}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01','0.003']]:
    q=mp.e**(-tau); N=int(70/(1-q))
    b0,l1,t0,t1=raw(q,N); D=1-Sb(1,q)
    N0=t0*D; N1=t1*D
    s0b=Sb(0,q); s1b=Sb(1,q); s2b=Sb(2,q)
    # So = (1-q)/(2q) Sb0 = the source0 numerator. t0 might equal So-related boundary.
    print(f"{float(tau):>8.4f} {mp.nstr(N0,9):>13} {mp.nstr(N1,9):>13} {mp.nstr((1-q)/(2*q)*s0b,9):>13} N1/N0={mp.nstr(N1/N0,8)}")
print()
# N1/N0 ratio -- maybe constant relation t1/t0. And s=g_V t1. Let me check t1/t0 ~ q? and
# the s formula. Actually focus: R2 is about s=g_V t1 -> 1/4. Express t1 cleanly.
# Try: is t1*(1-S1b) = (1-q)/(2q) * [Sb0 - 2 q So-ish]? Let me brute force a 2-term fit
# t1*(1-S1b) = a*Sb0 + b*Sb1 + c, solve a,b,c from 3 q's, then test 4th.
import itertools
qs=[mp.e**(-mp.mpf(t)) for t in ['0.1','0.05','0.02']]
rows=[]; rhs=[]
for q in qs:
    N=int(70/(1-q)); b0,l1,t0,t1=raw(q,N); D=1-Sb(1,q)
    rows.append([Sb(0,q), Sb(1,q), mp.mpf(1)]); rhs.append(t1*D)
Mx=mp.matrix(rows); bx=mp.matrix(rhs); sol=mp.lu_solve(Mx,bx)
print("fit t1*(1-S1b) = a*Sb0+b*Sb1+c :", [mp.nstr(x,6) for x in sol])
qt=mp.e**(-mp.mpf('0.007')); N=int(70/(1-qt)); b0,l1,t0,t1=raw(qt,N); D=1-Sb(1,qt)
pred=sol[0]*Sb(0,qt)+sol[1]*Sb(1,qt)+sol[2]
print(f"  test tau=0.007: t1*(1-S1b)={mp.nstr(t1*D,10)} pred={mp.nstr(pred,10)} diff={mp.nstr(abs(t1*D-pred),3)}")
