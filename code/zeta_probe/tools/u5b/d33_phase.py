#!/usr/bin/env python3
# Analyze the integrand of the IZ rep as tau->0.  Integrand (up to constants):
#   F(x;tau) = exp(-x^2/4tau) * G(x;tau),   G = S_in(x)/[(-p e^{ix};p)_inf]  (and overall 1/(p32) const)
# As p->1 (tau->0) each (.;p)_inf has dilog asymptotics:  log (a;p)_inf ~ (1/log p) Li2(a) + ...
# Goal: find the effective exponent Psi(x;tau) = -x^2/4tau + log G, locate its saddle x*, and
# see if Re Psi has a clean max (Watson/steepest descent) or a confluent structure.
import mpmath as mp
mp.mp.dps=30
def qpoch_inf(a,p,tol=mp.mpf(10)**(-30),NM=20000):
    r=mp.mpc(1);ai=a
    for i in range(NM):
        r*=(1-ai);ai*=p
        if abs(ai)<tol:break
    return r
def S_in(x,c,p,N=2000):
    e=mp.e**(1j*x);t=mp.mpc(1)/(1-p);s=t
    for n in range(1,N):
        t=t*(-c*e)/(1-p**(n+1));s+=t
        if abs(t)<mp.mpf(10)**(-30) and n>10:break
    return s
def logG(x,tau):
    q=mp.e**(-tau);p=q*q;c=2*q**2*(1-q);e=mp.e**(1j*x)
    return mp.log(S_in(x,c,p)) - mp.log(qpoch_inf(-p*e,p))
# Sample log|G| and arg G near x=0 for shrinking tau, scaled by the Gaussian width sqrt(2 tau).
print("Examine G(x) structure vs tau.  Report G(0), and d/dx log G at 0 (numeric).")
for tau in [mp.mpf("0.2"),mp.mpf("0.1"),mp.mpf("0.05"),mp.mpf("0.02")]:
    G0=logG(mp.mpf("0.0"),tau)
    h=mp.mpf("1e-6")
    d1=(logG(h,tau)-logG(-h,tau))/(2*h)
    d2=(logG(h,tau)-2*G0+logG(-h,tau))/h**2
    w=mp.sqrt(2/tau)
    print(f"tau={mp.nstr(tau,3):>6} w={mp.nstr(w,5):>8}: logG(0)={mp.nstr(G0,10):>22}  dlogG={mp.nstr(d1,8):>22}  d2logG={mp.nstr(d2,8)}",flush=True)
