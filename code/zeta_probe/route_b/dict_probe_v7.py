import mpmath as mp
mp.mp.dps=80
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
    l0=mp.mpf(0); l1=mp.mpf(0)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
    return l0,l1,u0[0],u1[0]
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=12000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("CONSEQUENCE 1:  b0 = S0_bulk / (1 - S1_bulk)   [from Se=1-S1b, So=(1-q)/(2q)S0b]")
print(f"{'where':>12} {'b0(raw)':>18} {'S0b/(1-S1b)':>18} {'|diff|':>10}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    q=mp.e**(-tau); N=int(60/(1-q))
    b0,b1,t0,t1=raw(q,N); s0b=Sb(0,q); s1b=Sb(1,q)
    cand=s0b/(1-s1b)
    print(f"tau={float(tau):>7.4f} {mp.nstr(b0,14):>18} {mp.nstr(cand,14):>18} {mp.nstr(abs(b0-cand),3):>10}")
for m in [1,2,4,8,16]:
    q=poles[m-1]; N=int(60/(1-q))
    b0,b1,t0,t1=raw(q,N); s0b=Sb(0,q); s1b=Sb(1,q)
    cand=s0b/(1-s1b)
    print(f"pole m={m:>2} {mp.nstr(b0,14):>18} {mp.nstr(cand,14):>18} {mp.nstr(abs(b0-cand),3):>10}")

print()
print("R1 mechanism: So/Se = [(1-q)/(2q) S0b]/(1-S1b).")
print("At travel poles, the relevant block is the BULK S1b (=Se-related), NOT the travel Sigma_1.")
print("Check at-pole values of bulk S1b and how So/Se->1:")
print(f"{'m':>3} {'tau':>9} {'S1b@pole':>12} {'1-S1b=Se':>12} {'S0b@pole':>12} {'So/Se':>12} {'(So/Se-1)/tau':>14}")
for m in [1,2,4,8,16,32,48,64]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    s0b=Sb(0,q); s1b=Sb(1,q)
    Se=1-s1b; So=(1-q)/(2*q)*s0b
    print(f"{m:>3} {float(tau):>9.5f} {float(s1b):>12.7f} {float(Se):>12.7f} {float(s0b):>12.4f} {float(So/Se):>12.8f} {float((So/Se-1)/tau):>14.6f}")
