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
def A_t(k,q): return 2*q/(1-q**(k+1))
def C_t(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=12000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A_t(k+2*j,q)*prod; prod*=C_t(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot

# OFF-POLE functional asymptotics of Se, So as q->1 (NOT at poles). Pin leading form.
print("OFF-POLE: Se, So vs cos w, sin w / w   (q=e^{-tau}, w=sqrt(2/tau))")
print(f"{'tau':>9} {'w':>10} {'Se':>14} {'cos w':>12} {'Se/cosw':>11} {'So':>14} {'sinw/w':>12} {'So/(sinw/w)':>12}")
for tau in [mp.mpf(x) for x in ['0.05','0.02','0.01','0.005','0.002','0.001','0.0005','0.0002','0.0001']]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    Se,So=Se_So(q)
    cw=mp.cos(w); sw=mp.sin(w)/w
    print(f"{mp.nstr(tau,3):>9} {float(w):>10.3f} {mp.nstr(Se,8):>14} {mp.nstr(cw,8):>12} {float(Se/cw):>11.5f} {mp.nstr(So,8):>14} {mp.nstr(sw,8):>12} {float(So/sw):>12.6f}")

print()
print("So/(sinw/w) -> 1 strongly. Se/cos w wanders. Test Se against 1-Sb(1)/something and Sb(1):")
print(f"{'tau':>9} {'w':>10} {'Se':>14} {'1-cosw':>12} {'Sb1':>12} {'Se vs ?':>10}")
for tau in [mp.mpf(x) for x in ['0.02','0.01','0.005','0.002','0.001']]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    Se,So=Se_So(q)
    s1b=Sb(1,q)
    # candidate: Se = 1 - Sb(1)/2 ?  Sb(1)~1-cos w => 1-Sb1/2 ~ (1+cos w)/2. test
    print(f"{mp.nstr(tau,3):>9} {float(w):>10.3f} {mp.nstr(Se,8):>14} {mp.nstr(1-mp.cos(w),8):>12} {mp.nstr(s1b,8):>12} Se/(1-Sb1/2)={float(Se/(1-s1b/2)):.5f} Se/(1-Sb1)={float(Se/(1-s1b)):.5f}")

print()
print("Direct: is Se EXACTLY a simple function of Sb(0),Sb(1) or Sigma(0),Sigma(1)?")
print("Try Se =? 1 - Sigma1/2, etc. And So =? Sigma0 * something. (off pole)")
print(f"{'tau':>9} {'Se':>13} {'1-Sig1/2':>12} {'So':>13} {'Sig0':>12} {'So*w^2/Sig0':>12}")
for tau in [mp.mpf(x) for x in ['0.02','0.01','0.005','0.002']]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    Se,So=Se_So(q)
    sig0=Sigma(0,q); sig1=Sigma(1,q)
    print(f"{mp.nstr(tau,3):>9} {mp.nstr(Se,7):>13} {mp.nstr(1-sig1/2,7):>12} {mp.nstr(So,7):>13} {mp.nstr(sig0,7):>12} {float(So*w*w/sig0) if sig0!=0 else 0:>12.6f}")
