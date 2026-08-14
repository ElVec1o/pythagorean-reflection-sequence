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
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
# source-1 numerator block: alpha1(k)=2 q^{2(k+1)}/(1-q^{k+1})  (source exponent doubled)
def alpha1(k,q): return 2*q**(2*(k+1))/(1-q**(k+1))
def Sb1num(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha1(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-170) and j>60: break
    return tot
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-170) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("l1 (source-1 diagonal) =? Sb1num(0)/(1-S1b)? And what about Sb with doubled source.")
print(f"{'tau':>8} {'l1':>14} {'Sb1num(0)/(1-S1b)':>18} {'diff':>9}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    q=mp.e**(-tau); N=int(70/(1-q))
    b0,l1,t0,t1=raw(q,N)
    cand=Sb1num(0,q)/(1-Sb(1,q))
    print(f"{float(tau):>8.4f} {mp.nstr(l1,10):>14} {mp.nstr(cand,10):>18} {mp.nstr(abs(l1-cand),3):>9}")
print()
# We established l1=S1b/(1-S1b). Let me confirm Sb1num(0) relation, and find t1.
# t1=u1[0]: the source-1 BOUNDARY amplitude. By the source-0 analogy t0=u0[0]=l1=S1b/(1-S1b).
# Wait t0 turned out = l1. By symmetry u1[0] (t1) might = a DIFFERENT block. Let me just
# fit t1*(1-S1b) against {Sb0, Sb1, Sb1num(0), Sb1num... , 1, q-powers} with a 4-term fit
# at 4 q's then test a 5th.
import itertools
basis=lambda q:[Sb(0,q),Sb(1,q),Sb1num(0,q),mp.mpf(1)]
qs=[mp.e**(-mp.mpf(t)) for t in ['0.13','0.1','0.05','0.02']]
rows=[];rhs=[]
for q in qs:
    N=int(70/(1-q));b0,l1,t0,t1=raw(q,N);D=1-Sb(1,q)
    rows.append(basis(q));rhs.append(t1*D)
sol=mp.lu_solve(mp.matrix(rows),mp.matrix(rhs))
print("fit t1*(1-S1b)=a*Sb0+b*Sb1+c*Sb1num(0)+d:",[mp.nstr(x,6) for x in sol])
for tt in ['0.035','0.007']:
    qt=mp.e**(-mp.mpf(tt));N=int(70/(1-qt));b0,l1,t0,t1=raw(qt,N);D=1-Sb(1,qt)
    pred=sum(sol[i]*basis(qt)[i] for i in range(4))
    print(f"  test tau={tt}: t1*(1-S1b)={mp.nstr(t1*D,10)} pred={mp.nstr(pred,10)} diff={mp.nstr(abs(t1*D-pred),3)}")
print()
# Alternative: maybe t1 directly = Sb1num(0)*(1-q)/(2q)/(1-S1b)*something. Test t1 vs Sb1num(0):
print("t1 vs Sb1num(0)/(1-S1b)*factor:")
print(f"{'tau':>8} {'t1':>14} {'Sb1num0/(1-S1b)':>17} {'ratio':>14}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    q=mp.e**(-tau); N=int(70/(1-q))
    b0,l1,t0,t1=raw(q,N)
    c=Sb1num(0,q)/(1-Sb(1,q))
    print(f"{float(tau):>8.4f} {mp.nstr(t1,10):>14} {mp.nstr(c,10):>17} {mp.nstr(t1/c,8) if c!=0 else 'inf':>14}")
