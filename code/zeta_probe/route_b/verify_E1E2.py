import mpmath as mp

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
def Se_So(q,Jmax):
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0)
    for j in range(0,Jmax):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te; So+=to
    return Se,So
def Aq(k,q): return 2*q/(1-q**(k+1))
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=Aq(k+2*j,q)*prod; prod*=Cq(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>40: break
    return tot
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sbulk(k,q,J):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>40: break
    return tot

poles=[mp.mpf(l) for l in open("poles.txt") if l.strip()]

mp.mp.dps=60
print("="*100)
print("E1: Se = 1 - S1_bulk   |   E2: So * Sigma0_travel = 1   [generic q, dps=60]")
print("="*100)
print(f"{'q':>6} | {'|Se-(1-S1b)|':>13} | {'|So*Sig0-1|':>13} | {'P12 vs Sig0?':>20}")
for qv in ['0.5','0.7','0.8','0.85','0.9','0.93']:
    q=mp.mpf(qv); N=int(80/(1-q)); J=int(6/(1-q))+200
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q,J); S1b=Sbulk(1,q,4000); Sig0=Sigma(0,q,4000); Sig1=Sigma(1,q,4000)
    P12=t1*Se
    # candidate: P12 = -So + something? print P12*Sig0 and P12 vs (Sig1-... )
    print(f"{qv:>6} | {mp.nstr(abs(Se-(1-S1b)),3):>13} | {mp.nstr(abs(So*Sig0-1),3):>13} | P12*Sig0={mp.nstr(P12*Sig0,8)}")

print()
print("="*100)
print("At travel poles (adaptive dps to beat Se/So cancellation: dps ~ 1.2*w/ln10 + 40)")
print("="*100)
print(f"{'m':>2} {'w':>8} {'dps':>4} | {'|Se-(1-S1b)|':>13} {'|So*Sig0-1|':>13} {'|Sig1-1|':>10}")
for m in [1,2,4,8,12,16,20,24,28,32,40,48,56,64,72,80]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=float(mp.sqrt(2/tau))
    dps=int(1.3*w/2.302)+50
    mp.mp.dps=dps
    qq=mp.mpf(str(q))
    # reload q at this dps from poles file string
    qstr=[l.strip() for l in open("poles.txt") if l.strip()][m-1]
    qq=mp.mpf(qstr)
    N=int(80/(1-qq)); J=2*int(w)+200
    b0,b1,t0,t1,L,qp=raw(qq,N)
    Se,So=Se_So(qq,J); S1b=Sbulk(1,qq,4000); Sig0=Sigma(0,qq,4000); Sig1=Sigma(1,qq,4000)
    print(f"{m:>2} {w:>8.3f} {dps:>4} | {mp.nstr(abs(Se-(1-S1b)),3):>13} {mp.nstr(abs(So*Sig0-1),3):>13} {mp.nstr(abs(Sig1-1),3):>10}")
