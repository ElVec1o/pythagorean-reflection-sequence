import mpmath as mp, sys
mp.mp.dps=130

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0); l1=mp.mpf(0)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
    return dict(b0=l0,b1=l1,t0=u0[0],t1=u1[0],v0=v[0])

def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def Se_So(q,J=6000):
    onem=1-q;Se=mp.mpf(0);So=mp.mpf(0)
    for j in range(0,J):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te;So+=to
        if j>20 and abs(te)+abs(to)<mp.mpf(10)**(-(mp.mp.dps+10)):break
    return Se,So
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=2000000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-(mp.mp.dps+5)) and j>60: break
    return tot

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("dps=130. R1b decomposition + R2 independence. P12=t1*Se.")
print("a_T = cos(w_m)/(sqrt(tau)*sin w) ->? sqrt2/36 ; c_bulk=(S1b-(1-cos w))/(sqrt(tau)sin w) ->? sqrt2/36-1/sqrt2")
print("Se*w -> 1 ; (1-S1b)*w=Se*w.")
print(f"{'m':>3} {'tau':>10} {'a_T':>12} {'c_bulk':>12} {'a_T-c_bulk':>12} {'Se*w':>11} {'sgn(sinw)':>9}")
sqrt2=mp.sqrt(2)
for m in [4,8,16,24,32,40,48]:
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); st=mp.sqrt(tau); sw=mp.sin(w)
    Se,So=Se_So(q); s1b=Sb(1,q)
    a_T=mp.cos(w)/(st*sw)
    c_bulk=(s1b-(1-mp.cos(w)))/(st*sw)
    print(f"{m:>3} {float(tau):>10.6f} {float(a_T):>12.8f} {float(c_bulk):>12.8f} {float(a_T-c_bulk):>12.8f} {float(Se*w):>11.8f} {int(mp.sign(sw)):>9}")
print("  sqrt2/36 =",mp.nstr(sqrt2/36,9),"  sqrt2/36-1/sqrt2 =",mp.nstr(sqrt2/36-1/sqrt2,9),"  1/sqrt2 =",mp.nstr(1/sqrt2,9))

print()
print("R2 independence: is P12*w/tau -> 1/4 a SEPARATE fact, or does it follow from R1?")
print("t1/tau = (P12*w/tau)/(Se*w).  Se*w->1 (R1b). So t1/tau->1/4 IFF P12*w/tau->1/4. INDEPENDENT input.")
print("Check (P12*w/tau - 1/4)/tau  (subleading rate) and compare to (t1/tau-1/4)/tau:")
print(f"{'m':>3} {'tau':>10} {'P12*w/tau':>13} {'(P12w/tau-1/4)/tau':>20} {'t1/tau':>11} {'(t1/tau-1/4)/tau':>18}")
for m in [4,8,16,32,40,64,80]:
    if m>len(poles): break
    q=poles[m-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(95/p)
    r=raw(q,N); Se,So=Se_So(q); t1=r['t1']; P12=t1*Se
    val=P12*w/tau
    print(f"{m:>3} {float(tau):>10.6f} {float(val):>13.9f} {float((val-mp.mpf(1)/4)/tau):>20.9f} {float(t1/tau):>11.8f} {float((t1/tau-mp.mpf(1)/4)/tau):>18.9f}")
sys.stdout.flush()
