import mpmath as mp
mp.mp.dps=80
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
def Sb(k,q,J=12000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot
# Generalized bulk block with arbitrary source exponent. The b0 block came from source 2q^b.
# Build a telescoping block with source 2q^{(p)*b}? Let me instead just look for t1's block.
# Conjecture by analogy: l1 = N1/(1-S1b) where N1 is a source-1 numerator block.
# And t1=u1[0]. Try t1 in terms of Sb(0),Sb(1),Sb(2),Sb(3).
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print("l1 = source-1 resolvent at diagonal. Test l1 vs Sb(k)/(1-S1b):")
print(f"{'tau':>8} {'l1':>14} {'l1*(1-Sb1)':>14} {'Sb1':>11} {'Sb2':>11} {'Sb3':>11}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    q=mp.e**(-tau); N=int(60/(1-q))
    b0,l1,t0,t1=raw(q,N)
    n1=l1*(1-Sb(1,q))
    print(f"{float(tau):>8.4f} {mp.nstr(l1,9):>14} {mp.nstr(n1,9):>14} {mp.nstr(Sb(1,q),8):>11} {mp.nstr(Sb(2,q),8):>11} {mp.nstr(Sb(3,q),8):>11}")
print()
# The KEY for R2 is s=g_V*t1 -> 1/4. s = (q/(1-q))*t1. And s is what enters B_U.
# Maybe s itself has a clean block form. s -> 1/4. Test s vs blocks.
print("s = (q/(1-q))*t1.  Test s structure (off-pole and ramps to 1/4 only at poles):")
print(f"{'tau':>8} {'s':>14} {'Sb1':>11} {'Sb2':>11} {'s vs (1-Sb1)?':>14}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    q=mp.e**(-tau); N=int(60/(1-q))
    b0,l1,t0,t1=raw(q,N); s=(q/(1-q))*t1
    print(f"{float(tau):>8.4f} {mp.nstr(s,9):>14} {mp.nstr(Sb(1,q),8):>11} {mp.nstr(Sb(2,q),8):>11} {mp.nstr(s/(1-Sb(1,q)),8) if Sb(1,q)!=1 else 'inf':>14}")
print()
# t0=u0[0]. We have b0 (l0) and t0(u0[0]). Recall B(q,y)=(b0+g c)/(1-g t1), c=t0 b1 - b0 t1.
# Let me see if t0,t1 relate to b0,b1 simply. Also test the AT-POLE clean expansions once more, robustly.
print("AT POLES (robust, high dps): s->1/4, 4t1/tau->1, and s-1/4 ~ tau/16:")
print(f"{'m':>3} {'tau':>9} {'s':>14} {'4t1/tau':>12} {'(s-1/4)/tau':>14}")
for m in [1,2,4,8,16,32,48]:
    if m>len(poles):break
    q=poles[m-1]; N=int(80/(1-q)); tau=-mp.log(q)
    b0,l1,t0,t1=raw(q,N); s=(q/(1-q))*t1
    print(f"{m:>3} {float(tau):>9.5f} {float(s):>14.9f} {float(4*t1/tau):>12.7f} {float((s-mp.mpf(1)/4)/tau):>14.8f}")
