import mpmath as mp
mp.mp.dps=60

# ============================================================================
# SYNTHESIS VERIFICATION: the dictionary {Se,So,P12,SUM,t1} <-> {S1,S0,Sigma_1,Sigma_0}
# Build EVERYTHING from the exact formulas in the prompt. Confirm/refute each
# candidate identity at generic q AND at travel poles, to >=6 sig figs.
# ============================================================================

# ---- raw gapless bulk resolvent (b0,b1,t0,t1) + L array + qpow ----
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
    l0=mp.mpf(0); l1=mp.mpf(0); L=[mp.mpf(0)]
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
        L.append(l0)
    return l0,l1,u0[0],u1[0],L,qp

# ---- exact q-series Se, So (closed forms in the prompt) ----
def qpoch(q,n,cache={}):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def Se_So(q,J=None):
    if J is None: J=int(6*mp.sqrt(2/(-mp.log(q))))+120
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0)
    poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    for j in range(0,J):
        Se+=(-2*onem)**j*q**(j*(j+1))/poch[2*j]
        So+=(-2*onem)**j*q**(j*(j+2))*onem/poch[2*j+1]
    return Se,So

# ---- cocycle (convention A): P12=Y, P22=y=Se, P11=X, P21=x ----
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x   # P12,P22,P11,P21

# ---- lem:cos TRAVEL blocks Sigma_0, Sigma_1 (A,C) ----
def Aq(k,q): return 2*q/(1-q**(k+1))
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=None):
    if J is None: J=20000
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=Aq(k+2*j,q)*prod; prod*=Cq(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>60: break
    return tot
# ---- lem:cos BULK blocks S_0, S_1 (alpha,gamma) ----
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sbulk(k,q,J=None):
    if J is None: J=20000
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>60: break
    return tot

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*128)
print("PART 1.  GENERIC q (off-pole): pin the EXACT dictionary identities (must hold for ALL q, not just poles)")
print("="*128)
print(f"{'q':>6} | {'Se':>12} {'1-S1b':>12} {'Se-(1-S1b)':>12} | {'b1':>11} {'S1b/Se':>11} {'b1-S1b/Se':>11} | {'So':>11} {'S0b*p/2q':>11} {'diff':>10}")
for qf in ['0.70','0.80','0.88','0.92','0.96','0.985']:
    q=mp.mpf(qf); p=1-q; N=int(70/(1-q)); w=mp.sqrt(2/(-mp.log(q)))
    Jb=int(8*float(w))+200
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q)
    S1b=Sbulk(1,q); S0b=Sbulk(0,q)
    # candidate exact identities:
    d_Se   = Se-(1-S1b)            # Se ?= 1 - S1_bulk
    d_b1   = b1-S1b/Se             # b1=t0 ?= S1_bulk/Se
    So_pred= S0b*p/(2*q)           # So ?= (p/2q) S0_bulk
    d_So   = So-So_pred
    print(f"{qf:>6} | {float(Se):>12.7f} {float(1-S1b):>12.7f} {float(d_Se):>12.2e} | {float(b1):>11.6f} {float(S1b/Se):>11.6f} {float(d_b1):>11.2e} | {float(So):>11.6f} {float(So_pred):>11.6f} {float(d_So):>10.2e}")

print()
print("  Also test: b0 = (2q/p)*So/Se  AND  b0 = S0_bulk/(1-S1_bulk)  [the bulk resolvent]")
print(f"{'q':>6} | {'b0':>13} {'(2q/p)So/Se':>13} {'S0b/(1-S1b)':>13} | {'t1=P12/Se':>13} {'rawt1':>13}")
for qf in ['0.70','0.80','0.88','0.92','0.96','0.985']:
    q=mp.mpf(qf); p=1-q; N=int(70/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q)
    S1b=Sbulk(1,q); S0b=Sbulk(0,q)
    P12,P22,P11,P21=cocycle(q,N)
    print(f"{qf:>6} | {float(b0):>13.7f} {float((2*q/p)*So/Se):>13.7f} {float(S0b/(1-S1b)):>13.7f} | {float(P12/Se):>13.8f} {float(t1):>13.8f}")
