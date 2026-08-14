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

polestr=[l.strip() for l in open("poles.txt") if l.strip()]

print("="*118)
print("PART 2  AT travel poles. Independent recompute of R1 (So/Se->1) and R2 (t1/tau->1/4).")
print(" Also verify E1 holds at pole, E3 (Se=Sigma1-S1b), subleading c_T,c_B, E4(P12), and asymptotic forms.")
print("="*118)
sqrt2=mp.sqrt(2)
hdr=f"{'m':>3} {'w':>7} {'dps':>4} | {'So/Se':>9} {'t1/tau':>9} | {'Se/(sqtau sinw)':>15} {'So/(..)':>9} | {'P12/(tau^1.5 sw)':>15}"
print(hdr)
rows=[]
for m in [1,2,4,8,16,24,32,40,48,56,64]:
    if m>len(polestr): continue
    qstr=polestr[m-1]
    # set dps from w
    qf=float(qstr); tauf=-mp.log(mp.mpf(qstr)) if False else None
    import math
    tauf=-math.log(qf); wf=math.sqrt(2/tauf)
    dps=int(1.4*wf/2.302)+55
    mp.mp.dps=dps
    q=mp.mpf(qstr); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    N=int(80/(1-q)); J=2*int(float(w))+250
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q,J)
    S1b=Sbulk(1,q,6000); S0b=Sbulk(0,q,6000)
    Sig0=Sigma(0,q,6000); Sig1=Sigma(1,q,6000)
    # P12: from t1 = P12/Se  => P12 = t1*Se  (this is the DEFINITION used to extract P12)
    P12=t1*Se
    sinw=mp.sin(w)
    sqtau=mp.sqrt(tau)
    SoSe=So/Se
    t1tau=t1/tau
    Se_norm=Se/(sqtau*sinw)
    So_norm=So/(sqtau*sinw)
    P12_norm=P12/(tau**mp.mpf('1.5')*sinw)
    rows.append((m,q,tau,w,p,Se,So,S1b,S0b,Sig0,Sig1,t1,P12,b0))
    print(f"{m:>3} {float(w):>7.2f} {dps:>4} | {float(SoSe):>9.6f} {float(t1tau):>9.6f} | {float(Se_norm):>15.7f} {float(So_norm):>9.6f} | {float(P12_norm):>15.7f}")

print()
print("Targets: So/Se->1 ; t1/tau->1/4=0.25 ; Se/(sqtau sinw) & So/(..)->1/sqrt2=%.7f ; P12/(tau^1.5 sinw)->1/(4sqrt2)=%.7f"%(float(1/sqrt2),float(1/(4*sqrt2))))

print()
print("="*118)
print("PART 3  verify at-pole structural identities the closure rests on")
print(" E1@pole: Se=1-S1b   E3: Se=Sigma1-S1b (needs Sigma1=1)   E4: P12 ~ -(p/2q)(Sigma0-S0b)")
print("="*118)
print(f"{'m':>3} | {'|Sig1-1|':>10} {'|Se-(1-S1b)|':>13} {'|Se-(Sig1-S1b)|':>15} | {'P12/[-(p/2q)(Sig0-S0b)]':>24}")
for (m,q,tau,w,p,Se,So,S1b,S0b,Sig0,Sig1,t1,P12,b0) in rows:
    e1=abs(Se-(1-S1b)); e3=abs(Se-(Sig1-S1b)); sig1err=abs(Sig1-1)
    denom=-(p/(2*q))*(Sig0-S0b)
    e4ratio=P12/denom if denom!=0 else mp.mpf('nan')
    print(f"{m:>3} | {mp.nstr(sig1err,3):>10} {mp.nstr(e1,3):>13} {mp.nstr(e3,3):>15} | {mp.nstr(e4ratio,8):>24}")

print()
print("="*118)
print("PART 4  subleading coefficients at EXTREME PHASE w=(k+1/2)pi (cos w=0 exactly), NOT at a pole")
print(" c_T=(Sigma1-1)/(sqtau sinw) -> sqrt2/36=%.8f ;  c_B=(S1b-1)/(sqtau sinw) -> sqrt2/36-1/sqrt2=%.8f"%(float(mp.sqrt(2)/36),float(mp.sqrt(2)/36-1/mp.sqrt(2))))
print("="*118)
for k in [20,30,40,50]:
    w=mp.mpf(k)+mp.mpf('0.5')  # will reset dps below
    dps=int(1.4*float(w)/2.302)+60
    mp.mp.dps=dps
    w=mp.pi*(mp.mpf(k)+mp.mpf('0.5'))
    tau=2/w**2; q=mp.e**(-tau); p=1-q
    sinw=mp.sin(w); sqtau=mp.sqrt(tau)
    Sig1=Sigma(1,q,8000); S1b=Sbulk(1,q,8000)
    cT=(Sig1-1)/(sqtau*sinw); cB=(S1b-1)/(sqtau*sinw)
    print(f" k={k} w={float(w):.2f} dps={dps}: c_T={float(cT):+.8f}  c_B={float(cB):+.8f}  c_B-c_T={float(cB-cT):+.8f} (target -1/sqrt2=-0.70710678)")
