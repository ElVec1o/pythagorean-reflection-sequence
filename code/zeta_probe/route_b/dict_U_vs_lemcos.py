import mpmath as mp
mp.mp.dps = 50

# ---------- raw bulk resolvent (source-0): returns b0,b1,t0,t1, L array, qpow ----------
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

# ---------- closed forms Se, So, P12 (need high dps for cancellation) ----------
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def Se_So(q,J=400):
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0)
    for j in range(0,J):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te; So+=to
        if abs(te)<mp.mpf(10)**(-mp.mp.dps-5) and j>2*int(mp.sqrt(2/(-mp.log(q)))): break
    return Se,So

# ---------- lem:cos blocks ----------
# travel block Sigma (A,C); bulk block S (alpha,gamma)
def Aq(k,q): return 2*q/(1-q**(k+1))
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=Aq(k+2*j,q)*prod; prod*=Cq(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>40: break
    return tot
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sbulk(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>40: break
    return tot

poles=[mp.mpf(l) for l in open("poles.txt") if l.strip()]

print("="*120)
print("DICTIONARY: U-residual blocks (Se,So,P12,SUM,t1) vs lem:cos blocks (Sigma_0,Sigma_1 travel ; S_0,S_1 bulk)")
print("="*120)
print("At travel poles q_m (Sigma_1=1). w=sqrt(2/tau).")
print()
hdr=f"{'m':>2} {'tau':>9} {'w':>7} | {'Se':>11} {'So':>11} {'So/Se':>9} | {'SUM':>9} {'t1':>10} {'t1/tau':>9} | {'Sig1':>8} {'Sig0':>9} {'S1b':>8} {'S0b':>9}"
print(hdr)
print("-"*120)
data=[]
for m in [1,2,3,4,6,8,12,16,24,32]:
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(60/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    SUM=q*sum(qp[b]*L[b]*(1-qp[b]) for b in range(1,N))
    Se,So=Se_So(q)
    Sig1=Sigma(1,q); Sig0=Sigma(0,q); S1b=Sbulk(1,q); S0b=Sbulk(0,q)
    # P12 from t1 = P12/Se  => P12 = t1*Se
    P12=t1*Se
    data.append((m,q,tau,w,b0,b1,t0,t1,SUM,Se,So,P12,Sig1,Sig0,S1b,S0b))
    print(f"{m:>2} {float(tau):>9.5f} {float(w):>7.3f} | {float(Se):>11.5f} {float(So):>11.5f} {float(So/Se):>9.6f} | {float(SUM):>9.6f} {float(t1):>10.6f} {float(t1/tau):>9.6f} | {float(Sig1):>8.5f} {float(Sig0):>9.5f} {float(S1b):>8.5f} {float(S0b):>9.5f}")

print()
print("OBSERVATIONS to test as identities (need >=6 sig fig match):")
print("  Sig1 should be ~1 at poles (definition). S1b is bulk block at SAME q.")
print()
# Test candidate relations
print("="*120)
print("CANDIDATE RELATION TESTS (ratios; const => exact relation)")
print("="*120)
print(f"{'m':>2} | {'So/Se':>10} | {'Sig0/Sig1':>10} {'S0b/S1b':>10} | {'P12/w':>11} {'P12/(w*tau)':>12} | {'Se*(1-Sig1)':>12} {'Se-? ':>8}")
for (m,q,tau,w,b0,b1,t0,t1,SUM,Se,So,P12,Sig1,Sig0,S1b,S0b) in data:
    print(f"{m:>2} | {float(So/Se):>10.6f} | {float(Sig0/Sig1):>10.5f} {float(S0b/S1b):>10.5f} | {float(P12/w):>11.6f} {float(P12/(w*tau)):>12.6f} | {float(Se*(1-S1b)):>12.6f}")
