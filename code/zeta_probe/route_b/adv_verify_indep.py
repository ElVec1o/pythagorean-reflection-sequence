import mpmath as mp
mp.mp.dps=60

# Independent adversarial verification of exact-qbessel claims.

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0); l1=mp.mpf(0); Larr=[mp.mpf(0)]
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
        Larr.append(l0)
    return dict(b0=l0,b1=l1,t0=u0[0],t1=u1[0],v0=v[0],L=Larr)

def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def Se_So(q):
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0)
    for j in range(0,4000):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te; So+=to
        if j>10 and abs(te)+abs(to)<mp.mpf(10)**(-int(mp.mp.dps)-30): break
    return Se,So

def SUM_from_L(q,r,N):
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    return q*sum(qp[b]*r['L'][b]*(1-qp[b]) for b in range(1,N))

def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=400000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-int(mp.mp.dps)-40) and j>60: break
    return tot

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*92)
print("PART A: dictionary identities (off-pole + travel poles)")
print("="*92)
samples=[('off t=.1',mp.e**(-mp.mpf('0.1'))),('off t=.03',mp.e**(-mp.mpf('0.03'))),
         ('off t=.01',mp.e**(-mp.mpf('0.01')))]+[('pole'+str(m),poles[m-1]) for m in [1,2,4,8,16]]
print(f"{'where':>10}|{'Se-(1-S1b)':>12}|{'So-(1q)/2q*S0b':>14}|{'b0-S0b/(1-S1b)':>14}|{'b1-S1b/(1-S1b)':>14}|{'t0-b1':>9}|{'t1-v0':>9}|{'b0-2qSoSe/(1-q)':>15}")
for nm,q in samples:
    N=int(80/(1-q)); r=raw(q,N)
    Se,So=Se_So(q); s0b=Sb(0,q); s1b=Sb(1,q); D=1-s1b
    e_Se=Se-(1-s1b); e_So=So-(1-q)/(2*q)*s0b
    e_b0=r['b0']-s0b/D; e_b1=r['b1']-s1b/D
    e_t0=r['t0']-r['b1']; e_t1=r['t1']-r['v0']
    e_b0v2=r['b0']-(2*q/(1-q))*So/Se
    print(f"{nm:>10}|{mp.nstr(abs(e_Se),2):>12}|{mp.nstr(abs(e_So),2):>14}|{mp.nstr(abs(e_b0),2):>14}|{mp.nstr(abs(e_b1),2):>14}|{mp.nstr(abs(e_t0),2):>9}|{mp.nstr(abs(e_t1),2):>9}|{mp.nstr(abs(e_b0v2),2):>15}")

print()
print("="*92)
print("PART B: R1 (So/Se->1). Also SUM->1/2, b0*tau->2, cos/sqrt(tau)->sqrt2/36.")
print("="*92)
print(f"{'m':>3}{'tau':>11}{'w*Se':>12}{'w*So':>12}{'So/Se':>15}{'SUM':>12}{'b0*tau':>14}{'cos/sqtau':>13}{'(SoSe-1)/sqtau':>15}")
for m in [4,8,16,32,48,64,80]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(80/(1-q))
    Se,So=Se_So(q); r=raw(q,N); SUM=SUM_from_L(q,r,N)
    soe=So/Se
    print(f"{m:>3}{float(tau):>11.6f}{float(w*Se):>12.7f}{float(w*So):>12.7f}{float(soe):>15.10f}{float(SUM):>12.8f}{float(r['b0']*tau):>14.10f}{float(mp.cos(w)/mp.sqrt(tau)):>13.8f}{float((soe-1)/mp.sqrt(tau)):>15.8f}")
print("  sqrt2/36 =",mp.nstr(mp.sqrt(2)/36,10))

print()
print("="*92)
print("PART C: R2 (s=g_V*t1->1/4). Check t1=v0, s, (s-1/4)/tau->1/16.")
print("="*92)
print(f"{'m':>3}{'tau':>11}{'t1':>16}{'|t1-v0|':>10}{'s=gV*t1':>15}{'|s-1/4|':>10}{'(s-1/4)/tau':>14}")
for m in [4,8,16,32,48,64,80]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); gV=q/(1-q); N=int(90/(1-q)); r=raw(q,N)
    s=gV*r['t1']
    print(f"{m:>3}{float(tau):>11.6f}{float(r['t1']):>16.11f}{float(abs(r['t1']-r['v0'])):>10.1e}{float(s):>15.11f}{float(abs(s-mp.mpf(1)/4)):>10.2e}{float((s-mp.mpf(1)/4)/tau):>14.9f}")
print("  -> 1/16 =",float(mp.mpf(1)/16))
