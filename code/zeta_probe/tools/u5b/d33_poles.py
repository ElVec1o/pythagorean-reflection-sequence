#!/usr/bin/env python3
# Where does cos(w), w=sqrt(2/tau), come from in the IZ integral? Hypothesis: from poles of the
# integrand 1/(-p e^{ix};p)_inf and 1/(t;p)_inf approaching the real x-axis.
#  (-p e^{ix};p)_inf = 0 when -p e^{ix} p^n = 1 => e^{ix} = -p^{-(n+1)} => ix = i pi - (n+1) ln p = i pi + (n+1)*2tau
#    => x = pi - i (n+1) 2tau.  These are in the LOWER half plane (Im x = -(n+1)2tau), distance ~2tau from real axis,
#    accumulating onto x=pi (mod 2pi) as tau->0.  Real part pi, NOT near 0 where Gaussian lives. So these are far.
#  1/(t;p)_inf, t=-c e^{ix}, c=2q^2(1-q): zero when -c e^{ix} p^n=1 => e^{ix}=-p^{-n}/c => |e^{ix}|=p^{-n}/c ~ 1/(2tau) huge
#    => need Im x = -ln(p^{-n}/c) = ln(c) + n ln p = ln(2tau) - 2tau n -> -inf. Far below real axis. Also far.
# So no poles near x=0.  Then where is the oscillation? Let's just NUMERICALLY isolate the oscillatory part:
# compute the integral over a SMALL window |x|<delta (Gaussian core) vs the rest, and see which carries cos w.
import mpmath as mp
mp.mp.dps=30
def qpoch_inf(a,p,tol=mp.mpf(10)**(-28),NM=50000):
    r=mp.mpc(1);ai=a
    for i in range(NM):
        r*=(1-ai);ai*=p
        if abs(ai)<tol:break
    return r
def setup(tau):
    q=mp.e**(-tau);p=q*q;c=2*q**2*(1-q);return q,p,c
def integrand(x,tau):
    q,p,c=setup(tau);e=mp.e**(1j*x);t=-c*e
    Sin=(1/t)*(1/qpoch_inf(t,p)-1)
    return mp.e**(-x*x/(4*tau))*Sin/qpoch_inf(-p*e,p)
def Sigma_direct(tau,K=400):
    q=mp.e**(-tau);p=q*q;u=2*q/(1-p);s=u
    for k in range(K):
        u*=-2*(1-q)*q**(2*k+3)/((1-q**(2*k+4))*(1-q**(2*k+3)));s+=u
        if abs(u)<mp.mpf(10)**(-40) and k>20:break
    return s
# The PRE factor:
def PRE(tau):
    q,p,c=setup(tau);return 2*q/(mp.sqrt(4*mp.pi*tau)*qpoch_inf(p**mp.mpf(1.5),p))
print("Decompose integral by x-window; which window carries cos(w)?",flush=True)
for tau in [mp.mpf("0.05"),mp.mpf("0.02")]:
    q,p,c=setup(tau);w=mp.sqrt(2/tau)
    pre=PRE(tau)
    gw=mp.sqrt(2*tau)  # gaussian sd
    windows=[(0,3*gw),(3*gw,8*gw),(8*gw,mp.mpf("30"))]
    tot=mp.mpf(0)
    print(f" tau={mp.nstr(tau,3)} w={mp.nstr(w,6)} gauss_sd={mp.nstr(gw,4)}  1-cosw={mp.nstr(1-mp.cos(w),8)}  Sigma={mp.nstr(Sigma_direct(tau),8)}",flush=True)
    for (a,b) in windows:
        val=2*mp.quad(lambda x:integrand(x,tau).real,[a,b])  # 2x for +/- symmetry of even part
        print(f"    window x in [{mp.nstr(a,4)},{mp.nstr(b,4)}]: PRE*contrib = {mp.nstr(pre*val,8)}",flush=True)
        tot+=pre*val
    print(f"    SUM = {mp.nstr(tot,10)}",flush=True)
