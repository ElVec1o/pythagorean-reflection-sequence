import mpmath as mp
mp.mp.dps=60

# ---------- gapless bulk raw resolvent (b0,b1,t0,t1) + L_b ----------
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

def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p

# ---------- gapless-bulk closed forms Se, So, P12 ----------
def Se_clf(q,J=400):
    onem=1-q; tot=mp.mpf(0)
    for j in range(J):
        t=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        tot+=t
        if abs(t)<mp.mpf(10)**(-80) and j>5: break
    return tot
def So_clf(q,J=400):
    onem=1-q; tot=mp.mpf(0)
    for j in range(J):
        t=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        tot+=t
        if abs(t)<mp.mpf(10)**(-80) and j>5: break
    return tot

# ---------- lem:cos TRAVEL blocks Sigma_0, Sigma_1 ----------
def A_t(k,q): return 2*q/(1-q**(k+1))
def C_t(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A_t(k+2*j,q)*prod; prod*=C_t(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>60: break
    return tot

# ---------- lem:cos BULK blocks S_0, S_1 ----------
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sblk(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>60: break
    return tot

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*120)
print("DICTIONARY SEARCH: gapless-bulk {Se,So,P12,SUM,t1} vs lem:cos blocks {Sigma_0,Sigma_1,S_0,S_1}")
print("="*120)
print(f"{'q':>10} {'Se':>14} {'So':>14} {'SUM':>12} {'t1':>12} {'b0':>12} | {'Sig0':>12} {'Sig1':>12} {'S0blk':>12} {'S1blk':>12}")
testqs=[mp.mpf('0.7'),mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95')]
data=[]
for q in testqs:
    N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    SUM=q*sum(qp[b]*L[b]*(1-qp[b]) for b in range(1,N))
    Se=Se_clf(q); So=So_clf(q)
    Sig0=Sigma(0,q); Sig1=Sigma(1,q); S0b=Sblk(0,q); S1b=Sblk(1,q)
    data.append(dict(q=q,tau=tau,w=w,b0=b0,b1=b1,t0=t0,t1=t1,SUM=SUM,Se=Se,So=So,
                     Sig0=Sig0,Sig1=Sig1,S0b=S0b,S1b=S1b,P12=t1*Se))
    print(f"{float(q):>10.3f} {float(Se):>14.6f} {float(So):>14.6f} {float(SUM):>12.6f} {float(t1):>12.6f} {float(b0):>12.6f} | {float(Sig0):>12.6f} {float(Sig1):>12.6f} {float(S0b):>12.6f} {float(S1b):>12.6f}")

print("\n--- Sanity: closed forms reproduce raw ---")
for d in data:
    b0_clf=(2*d['q']/(1-d['q']))*d['So']/d['Se']
    print(f" q={float(d['q']):.2f}: b0_raw vs (2q/(1-q))So/Se : {float(d['b0']):.8f} vs {float(b0_clf):.8f}  diff={float(abs(d['b0']-b0_clf)):.1e}")
    # SUM = b0/2 - q/(1-q)  (from b0=2q/(1-q)+2SUM)
    SUM_id=d['b0']/2 - d['q']/(1-d['q'])
    print(f"          SUM_raw vs b0/2-q/(1-q): {float(d['SUM']):.8f} vs {float(SUM_id):.8f}  diff={float(abs(d['SUM']-SUM_id)):.1e}")
