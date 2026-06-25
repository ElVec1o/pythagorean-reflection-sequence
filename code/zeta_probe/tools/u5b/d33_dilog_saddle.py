#!/usr/bin/env python3
# Clean dilog-phase saddle analysis (overflow-safe: uses polylog, not q-products).
# Effective exponent (leading order, with the prefactor's dilog folded in):
#   Sigma ~ PRE * INT exp(F(x)/tau) dx ,  but careful: write everything over a common 1/(2tau)=1/eps.
# Total exponent including PRE:  the prefactor 1/(p^{3/2};p)_inf ~ exp(+Li2(p^{3/2})/eps - (1/2)log(1-p^{3/2})).
# As p->1: p^{3/2}->1, Li2(1)=pi^2/6.  And the integrand's denom (-p e^{ix};p)_inf ~ exp(-Li2(-p e^{ix})/eps).
# S_in ~ (1/t)/(t;p)_inf ~ exp(-Li2(t)/eps)/t, t=-c e^{ix}.  c=2q^2(1-q) -> ~2tau -> 0, so Li2(t)->Li2(0)=0;
#   but t->0 means S_in ~ (1/t)(1 + t + ...) ~ 1/t * (stuff). Need care: c~2tau so t~ -2tau e^{ix} -> 0.
#   (t;p)_inf with t->0: ->1. So S_in ~ (1/t)(1/1 - 1) -> indeterminate; expand: 1/(t;p)_inf -1 = t/(1-p)+...
#   => S_in -> 1/(1-p) ~ 1/(2tau). So S_in ~ 1/(1-p), roughly x-INDEPENDENT to leading order! (since t small)
# This means the c-factor (S_in) is NOT a saddle driver; the saddle comes only from (-p e^{ix};p)_inf and PRE.
# Reduced exponent (collect 1/eps terms, eps=2tau):
#   Sigma ~ [2q/(sqrt(4pi tau)) ] * [1/(1-p)] * exp(Li2(p^{3/2})/eps) *
#               INT exp(-x^2/4tau) exp(-Li2(-p e^{ix})/eps) dx  (leading)
#   = C(tau) INT exp( Phi(x)/eps ) dx,  Phi(x) = -x^2/2 - Li2(-p e^{ix})  [since -x^2/4tau = -x^2/(2 eps)]
#   wait: -x^2/4tau = -x^2/(2*(2tau)) = -x^2/(2 eps). And -Li2(-p e^{ix})/eps. So Phi(x)= -x^2/2 - Li2(-p e^{ix}).
import mpmath as mp
mp.mp.dps=30
def setup(tau):
    q=mp.e**(-tau);p=q*q;eps=2*tau;return q,p,eps
def Phi(x,tau):
    q,p,eps=setup(tau)
    return -x*x/2 - mp.polylog(2,-p*mp.e**(1j*x))
def Phip(x,tau):
    q,p,eps=setup(tau)
    e=mp.e**(1j*x)
    # d/dx[-Li2(-p e^{ix})] = -(-ln(1+p e^{ix}))*(i) = i ln(1+p e^{ix})  ... check sign:
    # d/dz Li2(z) = -ln(1-z)/z; z=-p e^{ix}; dz/dx = i z; d/dx Li2(z)= -ln(1-z)/z * i z = -i ln(1+p e^{ix}).
    # so d/dx[-Li2] = +i ln(1+p e^{ix}).
    return -x + 1j*mp.log(1+p*e)
def Phipp(x,tau):
    q,p,eps=setup(tau)
    e=mp.e**(1j*x)
    # d/dx[ i ln(1+p e^{ix}) ] = i * (p i e^{ix})/(1+p e^{ix}) = -p e^{ix}/(1+p e^{ix})
    return -1 - p*e/(1+p*e)
print("Dilog-phase saddle (Phi(x)=-x^2/2 - Li2(-p e^{ix})), eps=2tau:",flush=True)
for tau in [mp.mpf("0.1"),mp.mpf("0.05"),mp.mpf("0.02"),mp.mpf("0.01"),mp.mpf("0.005")]:
    q,p,eps=setup(tau);w=mp.sqrt(2/tau)
    # saddle near x where 1+p e^{ix} ~ 0 i.e. x ~ pi. Solve Phip=0.
    xs=mp.findroot(lambda x:Phip(x,tau), mp.mpc(2.5,-0.5))
    ph=Phi(xs,tau); pp2=Phipp(xs,tau)
    # the second (conjugate) saddle:
    xs2=mp.findroot(lambda x:Phip(x,tau), mp.mpc(-2.5,-0.5))
    ph2=Phi(xs2,tau)
    print(f"  tau={mp.nstr(tau,4):>7} w={mp.nstr(w,5):>7}: x*={mp.nstr(xs,8):>24}  Phi/eps={mp.nstr(ph/eps,8):>26}",flush=True)
    print(f"           Phi''={mp.nstr(pp2,6)}  x2*={mp.nstr(xs2,8)}  Phi2/eps={mp.nstr(ph2/eps,8)}",flush=True)
