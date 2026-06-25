#!/usr/bin/env python3
# Full leading-order steepest descent of the IZ integral, INCLUDING prefactor, vs Sigma_direct.
# Sigma = PRE * INT_{-inf}^{inf} exp(-x^2/4tau) * H(x) dx   (real part), where
#   PRE = 2q / [ sqrt(4 pi tau) * (p^{3/2};p)_inf ]
#   H(x) = S_in(x) / (-p e^{ix};p)_inf,   S_in(x)=(1/t)[1/(t;p)_inf -1], t=-c e^{ix}, c=2q^2(1-q).
# We replace the FULL integrand exp(Phi_tot(x)) and do saddle.  But cleanest: numerically saddle the
# EXACT integrand (not dilog approx) to confirm the method's validity, then separately confirm the
# dilog/Watson asymptotic.  Here we do exact-integrand steepest descent (Laplace) leading term:
#   I ~ exp(Phi_tot(x*)) * sqrt(2 pi / (-Phi_tot''(x*)))   [standard]
# with Phi_tot(x) = -x^2/4tau + log H(x).  Compare PRE*Re(I) to Sigma_direct.
import mpmath as mp
mp.mp.dps=30
def qpoch_inf(a,p,tol=mp.mpf(10)**(-30),NM=50000):
    r=mp.mpc(1);ai=a
    for i in range(NM):
        r*=(1-ai);ai*=p
        if abs(ai)<tol:break
    return r
def setup(tau):
    q=mp.e**(-tau);p=q*q;c=2*q**2*(1-q);return q,p,c
def logH(x,tau):
    q,p,c=setup(tau);e=mp.e**(1j*x);t=-c*e
    Sin=(1/t)*(1/qpoch_inf(t,p)-1)
    return mp.log(Sin)-mp.log(qpoch_inf(-p*e,p))
def Phitot(x,tau):
    return -x*x/(4*tau)+logH(x,tau)
def Sigma_direct(tau,K=400):
    q=mp.e**(-tau);p=q*q;u=2*q/(1-p);s=u
    for k in range(K):
        u*=-2*(1-q)*q**(2*k+3)/((1-q**(2*k+4))*(1-q**(2*k+3)));s+=u
        if abs(u)<mp.mpf(10)**(-40) and k>20:break
    return s
print("Exact-integrand steepest descent leading term vs Sigma_direct:",flush=True)
for tau in [mp.mpf("0.1"),mp.mpf("0.05"),mp.mpf("0.02"),mp.mpf("0.01")]:
    q,p,c=setup(tau);w=mp.sqrt(2/tau)
    PRE=2*q/(mp.sqrt(4*mp.pi*tau)*qpoch_inf(p**mp.mpf(1.5),p))
    # find complex saddle of Phitot near x* ~ pi/2 - i y
    h=mp.mpf("1e-7")
    def Pp(x):return (Phitot(x+h,tau)-Phitot(x-h,tau))/(2*h)
    try:
        xs=mp.findroot(Pp, mp.mpc(1.5,-1.0-0.4*(0.1/tau)))
    except Exception as ex:
        print("  tau",mp.nstr(tau,3),"saddle fail",ex);continue
    Ppp=(Phitot(xs+h,tau)-2*Phitot(xs,tau)+Phitot(xs-h,tau))/h**2
    I = mp.e**(Phitot(xs,tau))*mp.sqrt(2*mp.pi/(-Ppp))
    # the contour through x* picks the steepest path; for a real integral the leading contribution is 2*Re of one saddle
    # (the integrand is Hermitian: H(-x)=conj? check by symmetry) => total ~ 2 Re( PRE * I ) possibly, or PRE*Re(I).
    approx1=PRE*I
    Sd=Sigma_direct(tau)
    print(f"  tau={mp.nstr(tau,3):>6} w={mp.nstr(w,5):>7}: x*={mp.nstr(xs,7):>24}  SD=PRE*I={mp.nstr(approx1,9):>26}  2Re={mp.nstr(2*approx1.real,9):>14}  Sigma={mp.nstr(Sd,9)}",flush=True)
