import mpmath as mp
mp.mp.dps=60

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
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
    return dict(b0=l0,b1=l1,t0=u0[0],t1=u1[0],v0=v[0],L=L,qp=qp)

def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def Se_So(q,J=4000):
    onem=1-q;Se=mp.mpf(0);So=mp.mpf(0)
    for j in range(0,J):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te;So+=to
        if j>20 and abs(te)+abs(to)<mp.mpf(10)**(-(mp.mp.dps+10)):break
    return Se,So

def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=400000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-(mp.mp.dps+5)) and j>60: break
    return tot

def A_T(k,q): return 2*q/(1-q**(k+1))
def C_T(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma_T(k,q,J=400000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A_T(k+2*j,q)*prod; prod*=C_T(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-(mp.mp.dps+5)) and j>60: break
    return tot

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*100)
print("PART 1: independent dictionary check. dps=",mp.mp.dps)
print(f"{'where':>9} | {'|Se-(1-S1b)|':>13} {'|So-(p/2q)S0b|':>15} {'|b0-S0b/(1-S1b)|':>17} {'|t1-v0|':>10}")
samples=[('off t=0.1',mp.e**(-mp.mpf('0.1'))),('off t=0.03',mp.e**(-mp.mpf('0.03'))),('off t=0.01',mp.e**(-mp.mpf('0.01')))]
samples+=[('pole%d'%m,poles[m-1]) for m in [1,2,4,8,16]]
for nm,q in samples:
    p=1-q; N=int(85/p)
    r=raw(q,N); Se,So=Se_So(q); s0b=Sb(0,q); s1b=Sb(1,q)
    e1=abs(Se-(1-s1b)); e2=abs(So-(p/(2*q))*s0b); e3=abs(r['b0']-s0b/(1-s1b)); e4=abs(r['t1']-r['v0'])
    print(f"{nm:>9} | {mp.nstr(e1,2):>13} {mp.nstr(e2,2):>15} {mp.nstr(e3,2):>17} {mp.nstr(e4,2):>10}")

print()
print("="*100)
print("PART 2: Sb(bulk) vs Sigma_T(travel) at travel poles. Sigma_T(1) should be 1 (pole defn).")
print("="*100)
print(f"{'m':>3} {'tau':>10} {'Sigma_T(1)':>14} {'S1b=Sb(1)':>14} {'Sigma_T(0)':>14} {'S0b=Sb(0)':>14}")
for m in [2,4,8,16]:
    q=poles[m-1]; tau=-mp.log(q)
    print(f"{m:>3} {float(tau):>10.6f} {mp.nstr(Sigma_T(1,q),9):>14} {mp.nstr(Sb(1,q),9):>14} {mp.nstr(Sigma_T(0,q),9):>14} {mp.nstr(Sb(0,q),9):>14}")

print()
print("="*100)
print("PART 3: R1/R2 reduction table along travel poles (independent recompute). P12=t1*Se.")
print("="*100)
print(f"{'m':>3} {'tau':>9} {'b0*tau':>13} {'So/Se':>11} {'S0b/(wsw)':>10} {'Se*w':>9} {'P12w/tau':>9} {'t1/tau':>9} {'s':>9}")
for m in [2,4,8,16,32,40,64,80]:
    if m>len(poles): break
    q=poles[m-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(90/p)
    r=raw(q,N); Se,So=Se_So(q); s0b=Sb(0,q)
    t1=r['t1']; b0=r['b0']; gV=q/p; s=gV*t1
    P12=t1*Se
    s0b_wsw=s0b/(w*mp.sin(w))
    print(f"{m:>3} {float(tau):>9.6f} {mp.nstr(b0*tau,11):>13} {mp.nstr(So/Se,8):>11} {float(s0b_wsw):>10.6f} {float(Se*w):>9.6f} {float(P12*w/tau):>9.6f} {float(t1/tau):>9.6f} {float(s):>9.6f}")

print()
print("="*100)
print("PART 4: Se*w / Se*sqrt(tau) limits.  colleague: Se*w->1, Se/sqrt(tau)->1/sqrt2.")
print("="*100)
print(f"{'m':>3} {'tau':>10} {'Se/sqrt(tau)':>14} {'Se*w':>12} {'1/sqrt2':>10}")
for m in [4,8,16,32,40,80]:
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    Se,So=Se_So(q)
    print(f"{m:>3} {float(tau):>10.6f} {float(Se/mp.sqrt(tau)):>14.8f} {float(Se*w):>12.8f} {float(1/mp.sqrt(2)):>10.6f}")
