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
# Also need Sb(2) maybe: the bulk block So-analog might be the k-shifted. Let me look:
# Se = 1 - Sb(1). Maybe So = (something)*Sb(0) - it's the NEXT block in a coupled recursion.
# The bulk lem:cos recursion: S_k = alpha_k(1+S_1) ... NO. Let me just hunt the exact form of So.
print("Hunt exact So. Candidates with Sb(0) and q-factors:")
print(f"{'tau':>9} {'So/Sb0':>16} {'*(2/(1-q))':>14} {'*2/(1-q^? )':>0}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01','0.003','0.001']]:
    q=mp.e**(-tau)
    Se,So=Se_So(q); s0b=Sb(0,q)
    r=So/s0b
    print(f"{float(tau):>9.4f} r={mp.nstr(r,12):>16} r*2/(1-q)={mp.nstr(r*2/(1-q),12)} r*2/(1-q^2)={mp.nstr(r*2/(1-q**2),12)}")
print()
# Maybe So is a different bulk block entirely. Note So has q^{j(j+2)}(1-q)/(q;q)_{2j+1}.
# Compare to Sb(0) = telescoping. Let me try: is there a k such that So = (1-q)/2 * Sb(0)? exact?
print("Test So = (1-q)/2 * Sb(0) exactly:")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01']]:
    q=mp.e**(-tau)
    Se,So=Se_So(q); s0b=Sb(0,q)
    cand=(1-q)/2*s0b
    print(f"  tau={float(tau):.4f} So={mp.nstr(So,12)} (1-q)/2*Sb0={mp.nstr(cand,12)} diff={mp.nstr(abs(So-cand),3)}")
print()
# Hmm. Let me instead directly relate So to Sb(0) via the DEFINITION.
# Sb(0)= sum_j alpha(2j) prod_{i<j} gamma(2i). alpha(2j)=2q^{2j+1}/(1-q^{2j+1}).
# This is a continued-fraction-like telescoping, NOT a single q-Pochhammer sum like So.
# So they are equal only ASYMPTOTICALLY. Let me confirm So/Sb0 -> ? exactly via series,
# and whether So itself has its OWN clean form: So ~ sin(w)/w. test high-precision functional:
print("So vs sin(w)/w precisely (the leading asymptotic), and the correction:")
print(f"{'tau':>9} {'So':>16} {'sinw/w':>16} {'(So-sinw/w)/tau':>16}")
for tau in [mp.mpf(x) for x in ['0.02','0.01','0.005','0.002','0.001','0.0005']]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    Se,So=Se_So(q); sw=mp.sin(w)/w
    print(f"{float(tau):>9.4f} {mp.nstr(So,12):>16} {mp.nstr(sw,12):>16} {mp.nstr((So-sw)/tau,10):>16}")
