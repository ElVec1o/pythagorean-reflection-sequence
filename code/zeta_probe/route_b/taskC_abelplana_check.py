#!/usr/bin/env python3
"""
TASK C - validation: confirm the Abel-Plana integral reproduces the TRUE T2.
  T2 = - int_0^inf Im(psi(iy)) / sinh(pi y) dy,   psi(s) = W^{2s} g_s / Gamma(2s+1),
  g_s = 1 - exp(-B_s),  W = w e^{-tau/2}, w = sqrt(2/tau).
TRUE T2 = S1(bulk) - (1-cos w) - (cos w - cos W).
"""
import mpmath as mp
from taskC_Bs import B_s
mp.mp.dps = 50

def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb1(q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(1+2*j,q)*prod; prod*=gamma(1+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>50: break
    return tot

def psi_iy(y, tau, W, Kmax=60):
    s = mp.mpc(0,1)*y
    g = 1 - mp.e**(-B_s(s, tau, Kmax=Kmax, Pmax=8))
    return W**(2*s) * g / mp.gamma(2*s+1)

def integrand(y, tau, W):
    return -mp.im(psi_iy(y, tau, W)) / mp.sinh(mp.pi*y)

for tau in [mp.mpf('0.02'), mp.mpf('0.01'), mp.mpf('0.004')]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    S1=Sb1(q)
    T2_true=S1-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))
    # integrate the Abel-Plana representation. Integrand decays like e^{-2 pi y} for large y.
    f=lambda y: integrand(y, tau, W)
    # use quadosc-friendly: split into [0, ymax] with mpmath quad over subintervals through y*=W/2
    ystar=W/2
    nodes=[mp.mpf('1e-6'), ystar/2, ystar, ystar*1.5, ystar*2, ystar*3, ystar*5]
    I=mp.quad(f, nodes)
    print(f"tau={mp.nstr(tau,4)}  W={mp.nstr(W,8)}  y*={mp.nstr(ystar,6)}")
    print(f"   T2_true   = {mp.nstr(T2_true,14)}")
    print(f"   AbelPlana = {mp.nstr(I,14)}")
    print(f"   ratio     = {mp.nstr(I/T2_true,10)}   abs diff={mp.nstr(abs(I-T2_true),4)}")
