#!/usr/bin/env python3
"""
TASK C - the IBP non-stationary control integral
  I(Y) = int_{1<|y-y*|, y<Y} |d/dy (A(y)/Phi'(y))| dy
Study its dependence on the cutoff Y (does it stay O(1)/O(sqrt tau) or diverge as Y->pi/tau).
Also report sup A on (0, pi/tau) EXCLUDING the pole neighborhood.
"""
import mpmath as mp
import numpy as np
from taskC_Bs import B_s
mp.mp.dps = 35

tau = mp.mpf('0.01')
w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2); ystar = W/2
POLE = mp.pi/tau
KMAX, PMAX = 100, 18

def g_iy(y):
    return 1 - mp.e**(-B_s(mp.mpc(0,1)*y, tau, Kmax=KMAX, Pmax=PMAX))
def A(y):
    y = mp.mpf(y); return abs(g_iy(y))*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
def Phi(y):
    y = mp.mpf(y)
    return 2*y*mp.log(W) + mp.im(mp.log(g_iy(y))) - mp.im(mp.loggamma(1+2*mp.mpc(0,1)*y))
def Phip(y):
    return mp.diff(Phi, mp.mpf(y))
def F(y):  # A/Phi'
    return A(y)/Phip(y)

if __name__ == "__main__":
    print(f"tau={tau}  y*={mp.nstr(ystar,7)}  pole pi/tau={mp.nstr(POLE,8)}")
    print()
    # sup A excluding pole region (0, 300]:
    best=(0,0)
    for y in [float(x) for x in np.linspace(1,300,500)]:
        a=A(y)
        if a>best[1]: best=(y,a)
    print(f"sup A on (0,300] = {mp.nstr(best[1],7)} at y={mp.nstr(best[0],6)}")
    # envelope rises toward pole; report A at a few approaches
    for y in [305,310,313,314]:
        print(f"   A({y}) = {mp.nstr(A(y),7)}   (-> infinity at pole {mp.nstr(POLE,7)})")
    print()
    # IBP integral with grid-based |F'| (trapezoid on |dF|), two sides of y*.
    # Right side: y from y*+1 to Ycut.  Left side: y from 0.1 to y*-1.
    def tv_integral(ya, yb, npts):
        # total variation-ish: integral of |F'| via fine sampling of F then sum |dF|...
        # but we want int |F'| dy. Use mp.diff at nodes * spacing (trapezoid of |F'|).
        ys = [ya + (yb-ya)*mp.mpf(k)/(npts-1) for k in range(npts)]
        fp = [abs(mp.diff(F, y)) for y in ys]
        tot = mp.mpf(0)
        for k in range(npts-1):
            tot += (fp[k]+fp[k+1])/2*(ys[k+1]-ys[k])
        return tot
    # left piece [0.3, y*-1]:
    left = tv_integral(mp.mpf('0.3'), ystar-1, 80)
    print(f"left  I[0.3, y*-1]                 = {mp.nstr(left,7)}")
    print("right I[y*+1, Ycut] as Ycut grows toward the pole:")
    prev=None
    for Yc in [15,30,60,100,150,200,250,290,300,305,310]:
        right = tv_integral(ystar+1, mp.mpf(Yc), 120)
        print(f"   Ycut={Yc:>4}: right={mp.nstr(right,7)}   total I = {mp.nstr(left+right,7)}")
