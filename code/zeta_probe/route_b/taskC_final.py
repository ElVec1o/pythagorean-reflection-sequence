#!/usr/bin/env python3
"""
TASK C - FINAL: map A(y), Phi'(y); compute IBP control integral; report sup A, saddle.
tau=0.01. Integrand of T2 = -int Im(psi(iy))/sinh(pi y) dy = -A(y) sin Phi(y).
  A(y)=|g_iy| sqrt(coth(pi y)/(pi y)),  Phi(y)=2y log W + Im log g_iy - Im logGamma(1+2iy).
KEY: representation has a POLE at y=pi/tau (=314.16) from phi(2iy*tau~2 pi i); the real-axis
integral DIVERGES past it. Valid/meaningful range is 0<y< pi/tau, dominated by saddle y*=W/2=7.04.
"""
import mpmath as mp
from taskC_Bs import B_s
mp.mp.dps = 40

tau = mp.mpf('0.01')
w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2); ystar = W/2
KMAX, PMAX = 120, 20

def g_iy(y):
    return 1 - mp.e**(-B_s(mp.mpc(0,1)*y, tau, Kmax=KMAX, Pmax=PMAX))

def A(y):
    y = mp.mpf(y)
    return abs(g_iy(y))*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))

def Phi(y):
    y = mp.mpf(y)
    return 2*y*mp.log(W) + mp.im(mp.log(g_iy(y))) - mp.im(mp.loggamma(1+2*mp.mpc(0,1)*y))

def Phip(y):
    return mp.diff(Phi, mp.mpf(y))

def AoverPhip(y):
    return A(y)/Phip(y)

if __name__ == "__main__":
    print(f"=== TASK C  tau={tau}  w={mp.nstr(w,8)}  W={mp.nstr(W,9)}  y*=W/2={mp.nstr(ystar,8)} ===")
    print(f"tau^(-2/3)={mp.nstr(tau**(-mp.mpf(2)/3),6)}  pi/tau (pole)={mp.nstr(mp.pi/tau,7)}")
    print()
    # ---- (a) amplitude scalings ----
    print("(a) AMPLITUDE A(y):")
    print("  small-y limit A(0+) = |c1|/pi, c1=B'(0):")
    c1 = mp.diff(lambda s: B_s(s,tau,Kmax=KMAX,Pmax=PMAX), mp.mpf(0))
    print(f"     c1 = {mp.nstr(c1,10)}  (= -tau^2/36? -tau^2/36={mp.nstr(-tau**2/36,8)})")
    print(f"     A(0+) predicted |c1|/pi = {mp.nstr(abs(c1)/mp.pi,8)};  A(0.05)={mp.nstr(A('0.05'),8)}")
    print("  intermediate regime A ~ C*tau^2*y^2.5 (C~const):")
    for y in [3,5,8,12,18,25]:
        print(f"     y={y:>3}: A/(tau^2 y^2.5) = {mp.nstr(A(y)/(tau**2*mp.mpf(y)**mp.mpf('2.5')),7)}")
    print("  near/after peak A*sqrt(y) (envelope ~ const => A~1/sqrt(y)); |g| oscillates:")
    for y in [40,55,64,70,100,150,200,280]:
        print(f"     y={y:>3}: A={mp.nstr(A(y),7)}  A*sqrt(y)={mp.nstr(A(y)*mp.sqrt(y),6)}")
    print()
    # ---- (b) phase ----
    print("(b) PHASE Phi'(y) (monotone decr through y*, vanishes at y*=W/2):")
    for y in [0.5,1,2,4,6,7.0358,8,10,15,25,50,100,200,300]:
        pp = Phip(y); lg = mp.log(2*mp.mpf(y)/W)
        print(f"     y={y:>8}: Phi'={mp.nstr(pp,8):>13}  -2log(2y/W)={mp.nstr(-2*lg,7):>11}  ratio={mp.nstr(pp/(-2*lg) if lg!=0 else mp.nan,5)}")
    print()
    # ---- sup A ----
    print("sup A over the VALID range (0,pi/tau):")
    import numpy as np
    best=(0,0)
    for y in [float(x) for x in np.linspace(1,313,400)]:
        a=A(y)
        if a>best[1]: best=(y,a)
    # refine
    y0=best[0]
    for y in [float(x) for x in np.linspace(y0-3,y0+3,60)]:
        a=A(y)
        if a>best[1]: best=(y,a)
    print(f"     sup_{{0<y<pi/tau}} A = {mp.nstr(best[1],8)} at y = {mp.nstr(best[0],6)}")
    print(f"     (envelope max; A keeps ~rising toward the pole y=pi/tau where A->inf)")
    print()
    # ---- saddle value ----
    print("saddle s*=iW/2 amplitude (controls leading T2):")
    bstar=B_s(mp.mpc(0,1)*ystar,tau,Kmax=KMAX,Pmax=PMAX)
    print(f"     B_(iW/2) = {mp.nstr(bstar,10)}  |B*|={mp.nstr(abs(bstar),6)} (O(sqrt tau)? sqrt(tau)={mp.nstr(mp.sqrt(tau),5)})")
    print(f"     A(y*) = {mp.nstr(A(ystar),8)}")
