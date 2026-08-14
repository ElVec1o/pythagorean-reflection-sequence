#!/usr/bin/env python3
"""
TASK C - MAP amplitude and phase, and quantify the non-stationary tail.

Integrand of Abel-Plana T2 = -int_0^inf Im(psi(iy))/sinh(pi y) dy.
Write psi(iy)/sinh(pi y) = (real amplitude) * e^{i Phi(y)} up to sign, with
   A(y) = |g_{iy}| * sqrt(coth(pi y)/(pi y)) >= 0   [from |Gamma(1+2iy)| = sqrt(2 pi y/sinh 2pi y)]
   Phi(y) = 2 y log W + arg(g_{iy}) - arg Gamma(1+2iy)
   integrand = -A(y) sin Phi(y).
We compute A and Phi DIRECTLY (no asymptotics) from B_s, then Phi'(y) by autodiff (mpmath.diff).

Claims to confirm at tau=0.01 (W~14.07, y*~7):
 (a) A(y) ~ tau^2 y^{5/2} for small y; peaks near y ~ tau^{-2/3}; decays ~ 1/sqrt(y) after.
 (b) Phi'(y) monotone decreasing through y*=W/2 where it vanishes;
     |Phi'(y)| >= c |log(2y/W)| away from y*.
 (c) I = int_{|y-y*|>1} |d/dy (A/Phi')| dy  (the IBP non-stationary control integral).
"""
import mpmath as mp
from taskC_Bs import B_s
mp.mp.dps = 40

tau = mp.mpf('0.01')
w = mp.sqrt(2/tau)
W = w*mp.e**(-tau/2)
ystar = W/2

def g_iy(y):
    s = mp.mpc(0,1)*y
    return 1 - mp.e**(-B_s(s, tau, Kmax=40, Pmax=8))

def A(y):
    y = mp.mpf(y)
    return abs(g_iy(y))*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))

def Phi(y):
    y = mp.mpf(y)
    s = mp.mpc(0,1)*y
    # arg of psi(iy)*... ; full phase = arg( W^{2iy} g_{iy} / Gamma(1+2iy) )
    # = 2y log W + arg g_{iy} - arg Gamma(1+2iy)
    val = 2*y*mp.log(W) + mp.arg(g_iy(y)) - mp.arg(mp.gamma(1+2*mp.mpc(0,1)*y))
    return val

def Phi_unwrapped(y):
    # Use loggamma to get a continuous arg of Gamma(1+2iy): arg = Im(loggamma(1+2iy))
    y = mp.mpf(y)
    arg_gamma = mp.im(mp.loggamma(1+2*mp.mpc(0,1)*y))
    arg_g = mp.im(mp.log(g_iy(y)))   # continuous near where g~B (small phase)
    return 2*y*mp.log(W) + arg_g - arg_gamma

def Phip(y):
    # derivative of the *unwrapped* phase (smooth), via mpmath.diff
    return mp.diff(Phi_unwrapped, mp.mpf(y))

if __name__ == "__main__":
    print(f"tau={tau}  w={mp.nstr(w,8)}  W={mp.nstr(W,8)}  y*=W/2={mp.nstr(ystar,8)}")
    print(f"tau^(-2/3) = {mp.nstr(tau**(-mp.mpf(2)/3),6)}  (predicted A-peak location)")
    print()
    hdr = "{:>7} {:>14} {:>16} {:>14} {:>14} {:>12}".format('y','A(y)','A/(tau^2 y^2.5)','Phi(y)',"Phi'(y)",'log(2y/W)')
    print(hdr)
    ys = [0.1,0.2,0.3,0.5,0.7,1,1.5,2,3,4,5,6,6.5,7.0358,7.5,8,9,10,12,15,18,21.5,25,30,40,60,80]
    for y in ys:
        y=mp.mpf(y)
        a=A(y); pp=Phip(y)
        ratio=a/(tau**2*y**mp.mpf('2.5'))
        lg=mp.log(2*y/W)
        print(f"{mp.nstr(y,5):>7} {mp.nstr(a,7):>14} {mp.nstr(ratio,7):>16} {mp.nstr(Phi_unwrapped(y),7):>14} {mp.nstr(pp,7):>14} {mp.nstr(lg,5):>12}")
