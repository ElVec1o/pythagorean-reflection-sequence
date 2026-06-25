#!/usr/bin/env python3
# Dilog (p->1) asymptotics of the integrand pieces, to expose the effective saddle-point phase.
# p = e^{-eps}, eps = 2 tau.  Euler-Maclaurin:
#   log (a;p)_inf = sum_{n>=0} log(1 - a e^{-n eps})
#                 ~ (1/eps) INT_0^inf log(1-a e^{-s}) ds  +  (1/2) log(1-a)  +  ...
#                 = -(1/eps) Li2(a)  +  (1/2) log(1-a) + O(eps)       [since INT_0^inf log(1-a e^{-s})ds = -Li2(a)]
# Check this numerically, then assemble Psi.
import mpmath as mp
mp.mp.dps=30
def qpoch_inf(a,p,tol=mp.mpf(10)**(-30),NM=50000):
    r=mp.mpc(1);ai=a
    for i in range(NM):
        r*=(1-ai);ai*=p
        if abs(ai)<tol:break
    return r
def log_qpoch_inf_asym(a,eps):
    return -mp.polylog(2,a)/eps + mp.log(1-a)/2  # leading + half-correction
# test for a few a, eps
print("Check log(a;p)_inf ~ -Li2(a)/eps + (1/2)log(1-a):",flush=True)
for tau in [mp.mpf("0.1"),mp.mpf("0.03")]:
    eps=2*tau;p=mp.e**(-eps)
    for a in [mp.mpf("0.3"),mp.mpf("-0.7"),mp.mpc(0.2,0.5)]:
        exact=mp.log(qpoch_inf(a,p))
        asym=log_qpoch_inf_asym(a,eps)
        print(f"  tau={mp.nstr(tau,3)} a={mp.nstr(a,3):>14}: exact={mp.nstr(exact,10):>22} asym={mp.nstr(asym,10):>22} diff={mp.nstr(exact-asym,3)}",flush=True)
print()
# Now assemble integrand exponent.  Integrand factors (ignoring the x-independent const 1/(p32) and 2q/sqrt(4pi tau)):
#   numerator S_in(x) = sum_n (-c e^{ix})^n/(p;p)_{n+1}.  Hmm S_in is NOT a single (.;p)_inf.
#   But recall S_in(x) = sum_j p^j/(-c p^j e^{ix};p)_inf  and also relate to q-exp.
#   Actually 1/(p;p)_{n+1}: note S_in(x)=(1/(1-p)) sum_n (-c e^{ix})^n/( (p^2;p)_n )? since (p;p)_{n+1}=(1-p)(p^2;p)_n.
#   => S_in(x) = 1/(1-p) * 1phi0-type = 1/(1-p) * 1/( -c e^{ix} ; p)_inf-ish? Check: sum_n t^n/(p^2;p)_n is a q-exp e_p with base.. let's just identify numerically.
tau=mp.mpf("0.1");eps=2*tau;p=mp.e**(-eps);q=mp.e**(-tau);c=2*q**2*(1-q);x=mp.mpf("0.4");e=mp.e**(1j*x)
def S_in(x,c,p,N=2000):
    e=mp.e**(1j*x);t=mp.mpc(1)/(1-p);s=t
    for n in range(1,N):
        t=t*(-c*e)/(1-p**(n+1));s+=t
        if abs(t)<mp.mpf(10)**(-30) and n>10:break
    return s
val=S_in(x,c,p)
# candidate: 1/(1-p) * 1/( (-c e^{ix}) ; p )_inf ??  i.e. sum_n t^n/(p;p)_n with t=-c e -> 1/(t;p)_inf, but we have (p;p)_{n+1}.
cand1=(1/(1-p))/qpoch_inf(-c*e,p)  # wrong denom index; just to compare scale
print("S_in =",mp.nstr(val,12),"  (1/(1-p))/(-c e;p)_inf =",mp.nstr(cand1,12),flush=True)
# Better: sum_n t^n/(p;p)_{n+1} = (1/t) sum_{m>=1} t^m/(p;p)_m = (1/t)[ 1/(t;p)_inf - 1 ].
cand2=(1/(-c*e))*(1/qpoch_inf(-c*e,p) - 1)
print("S_in vs (1/t)[1/(t;p)_inf -1], t=-c e:",mp.nstr(val,12),mp.nstr(cand2,12),"diff",mp.nstr(val-cand2,3),flush=True)
