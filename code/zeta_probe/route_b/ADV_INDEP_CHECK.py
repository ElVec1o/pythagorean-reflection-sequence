import mpmath as mp

# ---- raw gapless bulk resolvent (returns b0,b1,t0,t1,v0,L) ----
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

def Se_So(q):
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0)
    for j in range(0,4000):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te; So+=to
        if j>10 and abs(te)+abs(to)<mp.mpf(10)**(-(mp.mp.dps+20)): break
    return Se,So

# lem:cos bulk blocks (continued-fraction-free product form from DICTIONARY_FINAL)
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=400000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-(mp.mp.dps+20)) and j>60: break
    return tot

# travel-pole Sigma blocks (Lambert). Sigma_1 travel = sum_c q^c L_c (the block whose root=1 defines poles)
# From sigma_exact: Sigma = sum_{c>=1} S_c q^{c-1}, S_c partial tails. We just need Sigma0_travel object
# used by colleague: "So*Sigma0_travel -> 1". Define Sigma0 via their struct. Let me derive Sigma0 numerically.

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

mp.mp.dps=40
print("="*100)
print("PART A: EXACT generic-q identities E1, E2', E0 (independent recompute, dps=40)")
print("="*100)
print(f"{'q':>8} | {'|Se-(1-S1b)|':>14} | {'|So-(p/2q)S0b|':>16} | {'|b0-S0b/(1-S1b)|':>18} | {'|b1-t0|':>10}")
for tt in ['0.5','0.6','0.7','0.8','0.9']:
    q=mp.mpf(tt); N=int(80/(1-q)); r=raw(q,N)
    Se,So=Se_So(q); s0b=Sb(0,q); s1b=Sb(1,q); p=1-q
    e1=abs(Se-(1-s1b))
    e2=abs(So-(p/(2*q))*s0b)
    e0=abs(r['b0']-s0b/(1-s1b))
    eb=abs(r['b1']-r['t0'])
    print(f"{tt:>8} | {mp.nstr(e1,3):>14} | {mp.nstr(e2,3):>16} | {mp.nstr(e0,3):>18} | {mp.nstr(eb,3):>10}")

print()
print("Cross-check: does b0 = (2q/p)*So/Se hold (the original identity)?")
for tt in ['0.5','0.7','0.9']:
    q=mp.mpf(tt); N=int(80/(1-q)); r=raw(q,N)
    Se,So=Se_So(q); p=1-q
    print(f"  q={tt}: b0={mp.nstr(r['b0'],8)}  (2q/p)So/Se={mp.nstr((2*q/p)*So/Se,8)}  diff={mp.nstr(abs(r['b0']-(2*q/p)*So/Se),2)}")

print()
print("="*100)
print("PART B: SCALING at travel poles. S0b~w sinw ; 1-S1b ~ (tau/2) w sinw ; b0*tau->2")
print("="*100)
print(f"{'m':>3} {'tau':>10} {'S0b/(w sinw)':>14} {'(1-S1b)/((t/2)w sinw)':>22} {'b0*tau':>13} {'cos(w)/sqrt(tau)':>16}")
for m in [1,2,4,8,16,24,32]:
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); sw=mp.sin(w)
    s0b=Sb(0,q); s1b=Sb(1,q); N=int(80/(1-q)); r=raw(q,N)
    r1=s0b/(w*sw); r2=(1-s1b)/((tau/2)*w*sw)
    print(f"{m:>3} {float(tau):>10.6f} {float(r1):>14.8f} {float(r2):>22.8f} {float(r['b0']*tau):>13.9f} {float(mp.cos(w)/mp.sqrt(tau)):>16.10f}")
