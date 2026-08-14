import mpmath as mp, math

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

print("="*110)
print("ADVERSARIAL PROBE A: does R1 need c_T,c_B SEPARATELY, or only Se itself?")
print(" Mechanism check: R1 = So/Se. So~(p/2q)S0b (EXACT E2) -> (1/sqrt2)sqtau sinw [via S0b~w sinw].")
print(" Se: at pole, Se=Sigma1-S1b (E3). Does Se->(1/sqrt2)sqtau sinw REQUIRE c_T,c_B, or is it direct?")
print(" Test: Se/(sqtau sinw) -> 1/sqrt2 directly (no decomposition needed since E1 makes Se a real block).")
print("="*110)
sqrt2=mp.sqrt(2)
print(f"{'m':>3} {'w':>7} | {'Se/(sqtau sw)':>13} {'-(1/sqrt2)':>11} {'diff*w':>10} | {'So/(sqtau sw)':>13} {'diff*w':>10}")
for m in [4,8,16,32,48,64]:
    if m>len(polestr): continue
    qstr=polestr[m-1]; qf=float(qstr); wf=math.sqrt(2/-math.log(qf))
    mp.mp.dps=int(1.5*wf/2.302)+60
    q=mp.mpf(qstr); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    N=int(80/(1-q)); J=2*int(float(w))+250
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q,J)
    sinw=mp.sin(w); sqtau=mp.sqrt(tau)
    Sen=Se/(sqtau*sinw); Son=So/(sqtau*sinw)
    d1=Sen-1/sqrt2; d2=Son-1/sqrt2
    print(f"{m:>3} {float(w):>7.2f} | {float(Sen):>13.8f} {float(1/sqrt2):>11.7f} {float(d1*w):>10.5f} | {float(Son):>13.8f} {float(d2*w):>10.5f}")
print(" If (diff*w) is BOUNDED, the approach to 1/sqrt2 is O(1/w)=O(sqtau) => clean subleading.")

print()
print("="*110)
print("ADVERSARIAL PROBE B: is R1's limit CIRCULAR? Check So/Se -1 ~ const*tau (independent of assuming the limit).")
print(" (So/Se - 1) should ~ c*tau. Fit c from consecutive poles.")
print("="*110)
prev=None
for m in [4,8,16,32,48,64]:
    if m>len(polestr): continue
    qstr=polestr[m-1]; qf=float(qstr); wf=math.sqrt(2/-math.log(qf))
    mp.mp.dps=int(1.5*wf/2.302)+60
    q=mp.mpf(qstr); tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int(80/(1-q)); J=2*int(float(w))+250
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q,J)
    r=So/Se-1
    print(f"m={m:>3} w={float(w):>7.2f} tau={float(tau):.3e}  (So/Se-1)={float(r):.3e}  (So/Se-1)/tau={float(r/tau):.6f}")

print()
print("="*110)
print("ADVERSARIAL PROBE C: R2 weak link. P12=t1*Se is a DEFINITION (t1 from raw). Is the closure of R2")
print(" t1/tau->1/4 INDEPENDENT of E4, or does it rely on the unproven P12 asymptotic?")
print(" Direct: t1/tau->1/4 is computed straight from raw(). E4 is only an INTERPRETATION of P12.")
print(" Cross-check the chain: t1 = P12/Se = [(1/4sqrt2)tau^1.5 sinw]/[(1/sqrt2)sqtau sinw] = tau/4.")
print("="*110)
for m in [4,8,16,32,64]:
    if m>len(polestr): continue
    qstr=polestr[m-1]; qf=float(qstr); wf=math.sqrt(2/-math.log(qf))
    mp.mp.dps=int(1.5*wf/2.302)+60
    q=mp.mpf(qstr); tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    N=int(80/(1-q)); J=2*int(float(w))+250
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q,J)
    P12=t1*Se
    sinw=mp.sin(w); sqtau=mp.sqrt(tau)
    # reconstruct t1 from the asymptotic forms and compare
    P12_as=(1/(4*sqrt2))*tau**mp.mpf('1.5')*sinw
    Se_as=(1/sqrt2)*sqtau*sinw
    t1_recon=P12_as/Se_as
    print(f"m={m:>3}: t1={float(t1):.8e} t1/tau={float(t1/tau):.7f} | recon t1_as={float(t1_recon):.8e}={float(t1_recon/tau):.4f}*tau  ratio t1/t1_recon={float(t1/t1_recon):.6f}")

print()
print("="*110)
print("ADVERSARIAL PROBE D: sign + positivity sanity. b0>0, s<1 at all sampled poles (the actual B_U!=0 inputs).")
print("="*110)
for m in [1,4,16,32,48,64]:
    if m>len(polestr): continue
    qstr=polestr[m-1]; qf=float(qstr); wf=math.sqrt(2/-math.log(qf))
    mp.mp.dps=int(1.5*wf/2.302)+60
    q=mp.mpf(qstr); tau=-mp.log(q); p=1-q
    N=int(80/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    s=(q/p)*t1
    print(f"m={m:>3}: b0={float(b0):.4f}(>0:{b0>0}) b0*tau={float(b0*tau):.7f} s={float(s):.7f}(<1:{s<1})")
