#!/usr/bin/env python3
"""
TASK C - does a TRUNCATED Abel-Plana integral over [eps, Y0] (Y0 well before pole) reproduce T2?
We integrate the SIGNED integrand -Im psi/sinh with fine oscillatory-aware quadrature, splitting
on Phi-zero (the saddle) and using many panels. Compare to true T2.
Also report sup A on the truly-physical window and the IBP integral there.
"""
import mpmath as mp
from taskC_Bs import B_s
mp.mp.dps = 35

tau = mp.mpf('0.01'); q=mp.e**(-tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ystar=W/2
KMAX,PMAX=80,16
def integ(y):
    y=mp.mpf(y); s=mp.mpc(0,1)*y
    psi=W**(2*s)*(1-mp.e**(-B_s(s,tau,Kmax=KMAX,Pmax=PMAX)))/mp.gamma(2*s+1)
    return -mp.im(psi)/mp.sinh(mp.pi*y)
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2))-2*q**(k+1)/(1-q**(k+1))
def Sb1(q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(1+2*j,q)*prod; prod*=gamma(1+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>50: break
    return tot
T2_true=Sb1(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))
print(f"T2_true={mp.nstr(T2_true,14)}")
print("Truncated Abel-Plana integral over [1e-6, Y0] (fine panels through saddle y*=7.036):")
for Y0 in [12,20,30,40,50,70]:
    # nodes: ramp through saddle and out; mp.quad adaptive with many seed nodes
    nodes=[mp.mpf('1e-6')]
    yy=mp.mpf('0.5')
    while yy<Y0:
        nodes.append(yy); yy+=mp.mpf('0.5')
    nodes.append(mp.mpf(Y0))
    I=mp.quad(integ,nodes)
    print(f"   Y0={Y0:>3}: I={mp.nstr(I,12)}   I-T2={mp.nstr(I-T2_true,4)}")
