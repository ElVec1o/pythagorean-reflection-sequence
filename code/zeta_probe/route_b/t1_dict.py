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
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
# P12 = t1*Se, with Se=1-Sb(1). So P12 = t1*(1-Sb1). What is P12's closed series?
# t1 = P12/Se. We have t1~tau/4. Let me hunt P12 against the bulk blocks.
# t1 is the source-1 dressing. Maybe t1 relates to Sb(2)? or a derivative block.
# Test t1 = (1-q)/(2q) * (something) like So did. Or t1*Se in terms of blocks.
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print("Probe t1 structure.  t1~tau/4. Test t1 vs bulk blocks Sb(k) and q-factors.")
print(f"{'tau':>9} {'t1':>16} {'t1/(1-q)':>14} {'4t1/tau':>12} {'Sb2':>12} {'Sb1':>12}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01','0.003']]:
    q=mp.e**(-tau); N=int(60/(1-q)); w=mp.sqrt(2/tau)
    b0,b1,t0,t1=raw(q,N)
    s1b=Sb(1,q); s2b=Sb(2,q)
    print(f"{float(tau):>9.4f} {mp.nstr(t1,12):>16} {mp.nstr(t1/(1-q),10):>14} {float(4*t1/tau):>12.6f} {mp.nstr(s2b,8):>12} {mp.nstr(s1b,8):>12}")
print()
# t1 came from source c1=2q^2 (vs source0 c0=2q). The bulk block with shifted source.
# Let me directly express t1 via a Se-like / So-like Pochhammer sum. Recall:
#   b0=(2q/(1-q))*So/Se, t1=P12/Se, s=(q/(1-q))t1.
# P12 is the OTHER cocycle entry. Try: P12 = ? maybe P12 = q*(1-So')/... Let me get P12=t1*Se numerically
# and recognize it. P12 ~ t1*1 ~ tau/4 near q->1 (since Se->cos->varies). Actually Se=1-Sb1 oscillates.
print("P12 = t1*Se = t1*(1-Sb1). Recognize P12:")
print(f"{'tau':>9} {'P12':>16} {'P12*2q/(1-q)':>14} {'P12/So':>14} {'P12/(q*So)':>14}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01','0.003']]:
    q=mp.e**(-tau); N=int(60/(1-q))
    b0,b1,t0,t1=raw(q,N)
    s1b=Sb(1,q); s0b=Sb(0,q)
    Se=1-s1b; So=(1-q)/(2*q)*s0b
    P12=t1*Se
    print(f"{float(tau):>9.4f} {mp.nstr(P12,12):>16} {mp.nstr(P12*2*q/(1-q),10):>14} {mp.nstr(P12/So,10):>14} {mp.nstr(P12/(q*So),10):>14}")
