#!/usr/bin/env python3
# Look for the OSCILLATION-carrying saddle: a complex x* (likely O(sqrt tau)) where Im(Phitot(x*)) ~ +/- w.
# Phitot(x)=-x^2/4tau + log H(x).  Near x=0, log H is smooth; expand. The -x^2/4tau term has saddle structure
# only combined with log H. For SMALL x (scale sqrt tau), log H(x) ~ logH(0) + a1 x + a2 x^2/2 + ...
# with a1 = dlogH/dx|0 (we saw ~ -i/tau scale earlier => a1 ~ i*alpha/tau).  Then
#   Phitot ~ logH(0) + a1 x + (a2 - 1/2tau) x^2/2.  Saddle x* = -a1/(a2 - 1/2tau).
# If a1 ~ i*alpha/tau and a2~beta/tau, x* ~ -i alpha/tau /((beta-1/2)/... ) -- compute exactly and Im Phitot(x*).
import mpmath as mp
mp.mp.dps=40
def qpoch_inf(a,p,tol=mp.mpf(10)**(-35),NM=80000):
    r=mp.mpc(1);ai=a
    for i in range(NM):
        r*=(1-ai);ai*=p
        if abs(ai)<tol:break
    return r
def setup(tau):
    q=mp.e**(-tau);p=q*q;c=2*q**2*(1-q);return q,p,c
def H(x,tau):
    q,p,c=setup(tau);e=mp.e**(1j*x);t=-c*e
    Sin=(1/t)*(1/qpoch_inf(t,p)-1)
    return Sin/qpoch_inf(-p*e,p)
def logH(x,tau): return mp.log(H(x,tau))
def Phitot(x,tau): return -x*x/(4*tau)+logH(x,tau)
print("Taylor of logH at 0 and predicted oscillatory saddle:",flush=True)
for tau in [mp.mpf("0.05"),mp.mpf("0.02"),mp.mpf("0.01")]:
    q,p,c=setup(tau);w=mp.sqrt(2/tau)
    h=mp.mpf("1e-5")
    L0=logH(0,tau)
    a1=(logH(h,tau)-logH(-h,tau))/(2*h)
    a2=(logH(h,tau)-2*L0+logH(-h,tau))/h**2
    # saddle of quadratic approx: Phitot' = a1 + (a2 - 1/(2tau)) x =0 => x*=-a1/(a2-1/(2tau))
    A=a2-1/(2*tau)
    xstar=-a1/A
    Ph=L0 + a1*xstar + A*xstar**2/2
    print(f"tau={mp.nstr(tau,3)} w={mp.nstr(w,6)}: a1={mp.nstr(a1,6)}  a2={mp.nstr(a2,6)}  x*={mp.nstr(xstar,6)}",flush=True)
    print(f"    Phitot(x*) approx = {mp.nstr(Ph,8)}   Im={mp.nstr(Ph.imag,8)}  (compare w={mp.nstr(w,6)}, -w={mp.nstr(-w,6)})",flush=True)
    # also exact-H saddle near xstar:
    try:
        def Pp(x):return (Phitot(x+h,tau)-Phitot(x-h,tau))/(2*h)
        xs=mp.findroot(Pp, xstar)
        print(f"    exact saddle x*={mp.nstr(xs,8)}  Phitot={mp.nstr(Phitot(xs,tau),8)}  Im={mp.nstr(Phitot(xs,tau).imag,8)}",flush=True)
    except Exception as ex:
        print("    exact saddle fail:",str(ex)[:60],flush=True)
