#!/usr/bin/env python3
# Effective steepest-descent phase of the IZ integral as tau->0.
# Integrand exponent (leading dilog approx), Sigma = const * INT exp(Psi(x)) dx (real part),
#   Psi(x) = -x^2/(4 tau) + (1/(2 tau)) [ Li2(-c e^{ix}) + Li2(-p e^{ix}) ] + log-prefactors
# with c=2q^2(1-q), p=q^2, eps=2tau.  We test:
#  (A) does Psi have a saddle x* near the imaginary axis whose Re Psi gives a sensible leading term?
#  (B) does the saddle reproduce the confluence limit 1-cos w (w=sqrt(2/tau))?
import mpmath as mp
mp.mp.dps=30

def pieces(tau):
    q=mp.e**(-tau);p=q*q;c=2*q**2*(1-q);eps=2*tau
    return q,p,c,eps

def Psi(x,tau,full=True):
    q,p,c,eps=pieces(tau)
    e=mp.e**(1j*x)
    val = -x*x/(4*tau) + (mp.polylog(2,-c*e)+mp.polylog(2,-p*e))/eps
    return val

# saddle: Psi'(x)=0.  Psi'(x) = -x/(2tau) + (1/(2tau)) d/dx[Li2(-c e^{ix})+Li2(-p e^{ix})]
#   d/dx Li2(-a e^{ix}) = -ln(1+ a e^{ix}) * (i)   [since d/dz Li2(z)=-ln(1-z)/z, z=-a e^{ix}, dz/dx=i z]
#   => d/dx Li2(-a e^{ix}) = (-ln(1-z)/z)(i z) = -i ln(1+ a e^{ix}).
# So Psi'(x) = -x/(2tau) - (i/(2tau))[ ln(1+c e^{ix}) + ln(1+ p e^{ix}) ].
def Psip(x,tau):
    q,p,c,eps=pieces(tau)
    e=mp.e**(1j*x)
    return -x/(2*tau) - (1j/(2*tau))*( mp.log(1+c*e)+mp.log(1+p*e) )

# Solve for saddle near x = i*y0.  As tau->0, p->1 so ln(1+p e^{ix})=ln(1+e^{ix}); c->0 so ln(1+c e^{ix})~c e^{ix}~0.
# Leading saddle eq: -x - i ln(1+e^{ix}) = 0 (drop the c term, multiply by 2tau). Solve x* = -i ln(1+e^{ix*}).
# Try purely imaginary x=i y: -i y - i ln(1+e^{-y})=0 => y + ln(1+e^{-y})=0 => e^{-y}(... ) hmm => y=-ln(1+e^{-y}).
# RHS negative => y<0.  Let's just numerically root-find Psip=0 for each tau (complex).
print("Saddle of full Psi (dilog approx) and value, vs 1-cos w:",flush=True)
for tau in [mp.mpf("0.1"),mp.mpf("0.05"),mp.mpf("0.02"),mp.mpf("0.01")]:
    w=mp.sqrt(2/tau)
    # initial guess: solve leading -x - i ln(1+e^{ix})=0 ; near x ~ i*(-something) OR x~ pi-ish.
    # Actually 1+e^{ix}=0 at x=pi: ln-> -inf.  Expect saddle near x where e^{ix}~-1 => x near pi (real!).
    try:
        xs=mp.findroot(lambda x: Psip(x,tau), mp.mpc(3.0,0.5))
    except Exception as ex:
        xs=None
    if xs is not None:
        ps=Psi(xs,tau)
        print(f"  tau={mp.nstr(tau,3):>6} w={mp.nstr(w,5):>7}: x*={mp.nstr(xs,8):>26}  Psi(x*)={mp.nstr(ps,8):>26}  1-cosw={mp.nstr(1-mp.cos(w),8)}",flush=True)
    else:
        print(f"  tau={mp.nstr(tau,3)}: no saddle found",flush=True)
