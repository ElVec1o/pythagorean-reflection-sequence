#!/usr/bin/env python3
import mpmath as mp
mp.mp.dps=30
def qpoch_inf(a,p,tol=mp.mpf(10)**(-32),NM=5000):
    r=mp.mpc(1);ai=a
    for i in range(NM):
        r*=(1-ai);ai*=p
        if abs(ai)<tol:break
    return r
def qpoch(a,p,n):
    r=mp.mpc(1);ai=a
    for i in range(n):r*=(1-ai);ai*=p
    return r
tau=mp.mpf("0.2");q=mp.e**(-tau);p=q*q
# (1) q-binomial: 1/(t;p)_inf =? sum_n t^n/(p;p)_n
t=mp.mpf("0.3")
lhs=1/qpoch_inf(t,p)
rhs=mp.fsum([t**n/qpoch(p,p,n) for n in range(200)])
print("q-binomial 1/(t;p)_inf vs sum t^n/(p;p)_n:",mp.nstr(lhs,12),mp.nstr(rhs,12),"diff",mp.nstr(lhs-rhs,3),flush=True)
# So the expansion uses sign: with argument -c e^{ix}, t = -c e^{ix}.  1/(-c e^{ix};p)_inf = sum (-c e^{ix})^n/(p;p)_n. OK.
# (2) Direct: S_in(x) = sum_j p^j / (-c p^j e^{ix};p)_inf.  Reindex via q-binom:
#     = sum_j p^j sum_n (-c e^{ix})^n p^{jn}/(p;p)_n = sum_n (-c e^{ix})^n/(p;p)_n * (1/(1-p^{n+1}))
c=2*q**2*(1-q);x=mp.mpf("0.0");e=mp.e**(1j*x)
brute=mp.fsum([p**j/qpoch_inf(-c*p**j*e,p) for j in range(2000)])
viaqb=mp.fsum([(-c*e)**n/qpoch(p,p,n)/(1-p**(n+1)) for n in range(300)])
print("S_in brute      =",mp.nstr(brute,12),flush=True)
print("S_in via qbinom =",mp.nstr(viaqb,12),flush=True)
# closed used (p;p)_{n+1} = (p;p)_n (1-p^{n+1}); check viaqb == sum (-c e)^n/(p;p)_{n+1}
clf=mp.fsum([(-c*e)**n/qpoch(p,p,n+1) for n in range(300)])
print("S_in closed sum =",mp.nstr(clf,12),flush=True)
