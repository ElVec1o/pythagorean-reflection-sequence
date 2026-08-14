#!/usr/bin/env python3
"""
TASK C - confirm the saddle window carries T2: high-order composite Simpson of the
signed Abel-Plana integrand over [eps, Y0], fine fixed grid (fast, no adaptive quad).
"""
import mpmath as mp
from taskC_Bs import B_s
mp.mp.dps = 30
tau=mp.mpf('0.01'); q=mp.e**(-tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ystar=W/2
KMAX,PMAX=70,14
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
print(f"T2_true={mp.nstr(T2_true,12)}",flush=True)
# Composite Simpson over [a,Y0]; oscillation period near saddle is large, far out small,
# so use h=0.02 (Phi' max ~5 => period ~1.2; h=0.02 resolves it).
a=mp.mpf('0.02'); h=mp.mpf('0.02')
# precompute integrand on grid up to 80 once:
N=int((80-float(a))/float(h))
ys=[a+h*k for k in range(N+1)]
vals=[integ(y) for y in ys]
print("cumulative Simpson integral up to Y0:",flush=True)
def simpson_upto(Y0):
    m=int((float(Y0)-float(a))/float(h))
    if m%2==1: m-=1
    tot=vals[0]+vals[m]
    for k in range(1,m):
        tot+= (4 if k%2==1 else 2)*vals[k]
    return tot*h/3
for Y0 in [12,20,30,40,50,60,70,78]:
    I=simpson_upto(Y0)
    print(f"   Y0={Y0:>3}: I={mp.nstr(I,11)}  I-T2={mp.nstr(I-T2_true,4)}",flush=True)
