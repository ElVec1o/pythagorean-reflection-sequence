#!/usr/bin/env python3
# Does deforming the x-contour through the imaginary saddle x* ~ 0.478 i resolve the cancellation?
# The integrand exp(-x^2/4tau)*H(x) is analytic in x in a strip around R (poles only near x=pi, far).
# Shift contour x -> x + i*b (b = saddle height ~0.478). On x' = u + i b (u real):
#   exp(-(u+ib)^2/4tau) = exp(-(u^2 - b^2 + 2 i u b)/4tau) = exp((b^2-u^2)/4tau) * exp(-i u b/2tau).
# The exp(+b^2/4tau) is the large factor; exp(-iub/2tau) oscillates in u with freq b/2tau.
# So on the shifted contour, the integrand is exp(+b^2/4tau)*[Gaussian in u]*[oscillation e^{-iub/2tau}]*H(u+ib).
# This is a clean Gaussian*oscillation = Fourier-Gaussian => Watson-amenable IF H(u+ib) is tame there.
# Test: compute Sigma via the shifted contour and check it equals Sigma, and whether the integrand
# magnitude is single-signed-ish (no catastrophic cancellation along u).
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
def H(x,tau):
    q,p,c=setup(tau);e=mp.e**(1j*x);t=-c*e
    Sin=(1/t)*(1/qpoch_inf(t,p)-1)
    return Sin/qpoch_inf(-p*e,p)
def PRE(tau):
    q,p,c=setup(tau);return 2*q/(mp.sqrt(4*mp.pi*tau)*qpoch_inf(p**mp.mpf(1.5),p))
def Sigma_direct(tau,K=400):
    q=mp.e**(-tau);p=q*q;u=2*q/(1-p);s=u
    for k in range(K):
        u*=-2*(1-q)*q**(2*k+3)/((1-q**(2*k+4))*(1-q**(2*k+3)));s+=u
        if abs(u)<mp.mpf(10)**(-40) and k>20:break
    return s
def Sigma_shifted(tau,b,T=8):
    # integral along x = u + i b, dx=du
    pre=PRE(tau)
    def integ(u):
        x=u+1j*b
        return (mp.e**(-x*x/(4*tau))*H(x,tau))
    # need real result; integrate complex then take real
    val=mp.quad(integ,[-T,0,T])
    return pre*val
for tau in [mp.mpf("0.05"),mp.mpf("0.02")]:
    q,p,c=setup(tau);w=mp.sqrt(2/tau)
    # scan saddle height b on imaginary axis: maximize Re Phitot(i b).
    def Phitot_im(b):
        x=1j*b; return (-x*x/(4*tau)+mp.log(H(x,tau))).real
    bb=max([mp.mpf(k)/100 for k in range(20,70)], key=Phitot_im)
    Ss=Sigma_shifted(tau,bb); Sd=Sigma_direct(tau)
    print(f"tau={mp.nstr(tau,3)} w={mp.nstr(w,5)} saddle_b={mp.nstr(bb,6)}: Sigma_shifted={mp.nstr(Ss,12)}  Sigma={mp.nstr(Sd,12)}  diff={mp.nstr(Ss-Sd,3)}",flush=True)
    # check cancellation along the shifted contour: max|integrand| vs |result/pre|
    mx=max(abs(mp.e**(-(u+1j*bb)**2/(4*tau))*H(u+1j*bb,tau)) for u in [mp.mpf(k)/10 for k in range(-30,31)])
    print(f"    max|integrand on shifted contour|={mp.nstr(mx,6)}  |result/PRE|={mp.nstr(abs(Sd/PRE(tau)),6)}  ratio(cancellation)={mp.nstr(mx/abs(Sd/PRE(tau)),5)}",flush=True)
