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

def Se_So(q):
    onem=1-q;Se=mp.mpf(0);So=mp.mpf(0)
    for j in range(0,600):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te;So+=to
        if j>10 and abs(te)+abs(to)<mp.mpf(10)**(-90):break
    return Se,So

def A_t(k,q): return 2*q/(1-q**(k+1))
def C_t(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=12000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A_t(k+2*j,q)*prod; prod*=C_t(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot

def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=12000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*130)
print("DICTIONARY: raw(b0,t1,Se,So) vs travel Sigma_0,Sigma_1 and bulk S0,S1")
print("="*130)
print(f"{'m':>3} {'tau':>9} {'b0':>13} {'t1':>12} {'Se':>13} {'So':>13} {'Sig1':>10} {'Sig0':>11} {'S1b':>10} {'S0b':>11}")
testpoles=[1,2,4,8,16]
for m in testpoles:
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q)
    sig1=Sigma(1,q); sig0=Sigma(0,q)
    s1b=Sb(1,q); s0b=Sb(0,q)
    print(f"{m:>3} {float(tau):>9.5f} {float(b0):>13.5f} {float(t1):>12.5e} {float(Se):>13.5e} {float(So):>13.5e} {float(sig1):>10.5f} {float(sig0):>11.3f} {float(s1b):>10.5f} {float(s0b):>11.3f}")

print()
print("="*130)
print("RATIOS / candidate identities:")
print("="*130)
print(f"{'m':>3} {'b0(1-q)/2q':>13} {'So/Se':>12} {'Se/cosw':>11} {'(So*w)/sinw':>12} {'t1/tau':>10} {'S1b@pole':>11} {'S0b/(wsinw)':>12}")
for m in testpoles:
    q=poles[m-1]; N=int(60/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q)
    s1b=Sb(1,q); s0b=Sb(0,q)
    print(f"{m:>3} {float(b0*(1-q)/(2*q)):>13.8f} {float(So/Se):>12.8f} {float(Se/mp.cos(w)):>11.5f} {float(So*w/mp.sin(w)):>12.5f} {float(t1/tau):>10.7f} {float(s1b):>11.7f} {float(s0b/(w*mp.sin(w))):>12.6f}")
