import mpmath as mp
mp.mp.dps=80
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def Se_So(q):
    onem=1-q;Se=mp.mpf(0);So=mp.mpf(0)
    for j in range(0,800):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te;So+=to
        if j>10 and abs(te)+abs(to)<mp.mpf(10)**(-110):break
    return Se,So
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=12000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("TEST  So = Sb(0)*(1-q)/(2q)   [exact?]  off-pole and at poles:")
print(f"{'where':>13} {'So':>20} {'Sb0*(1-q)/(2q)':>20} {'|diff|':>10}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01','0.003','0.001']]:
    q=mp.e**(-tau)
    Se,So=Se_So(q); s0b=Sb(0,q)
    cand=s0b*(1-q)/(2*q)
    print(f"tau={float(tau):>8.4f} {mp.nstr(So,14):>20} {mp.nstr(cand,14):>20} {mp.nstr(abs(So-cand),3):>10}")
for m in [1,2,4,8,16,32]:
    if m>len(poles):break
    q=poles[m-1]
    Se,So=Se_So(q); s0b=Sb(0,q)
    cand=s0b*(1-q)/(2*q)
    print(f"pole m={m:>3} {mp.nstr(So,14):>20} {mp.nstr(cand,14):>20} {mp.nstr(abs(So-cand),3):>10}")
