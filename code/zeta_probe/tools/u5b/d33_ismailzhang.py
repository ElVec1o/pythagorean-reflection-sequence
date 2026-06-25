#!/usr/bin/env python3
# ISMAIL-ZHANG (2018) integral representation of the Hahn-Exton q-Bessel J_nu^{(3)},
# applied in OUR base p=q^2, nu=1/2.  Goal: realize Phi (hence Sigma) as a real-line
# Laplace/Watson integral with Gaussian weight exp(-x^2/(4 tau)) that is ANALYTIC in tau
# and bypasses the natural boundary.
#
# IZ formula (base Q, |Q|<1):
#   J_nu^{(3)}(z;Q) = z^nu/sqrt(pi log Q^{-2}) * INT_{-inf}^{inf}
#         exp(x^2/log Q^2) / ( Q, -Q^{nu+1/2} e^{ix}, -Q^{1/2} z^2 e^{ix} ; Q)_inf  dx
#
# Power series (Wikipedia, base Q):
#   J_nu^{(3)}(z;Q) = z^nu (Q^{nu+1};Q)_inf/(Q;Q)_inf * sum_{k>=0} (-1)^k Q^{k(k+1)/2} z^{2k}/[(Q^{nu+1};Q)_k (Q;Q)_k]
#
# Our pure kernel:  Phi(y) = sum_k (-1)^k p^{k(k+1)/2} y^k /[(p;p)_k (p^{3/2};p)_k],   (y plays role of z^2)
#   with Q=p, nu=1/2 => Q^{nu+1}=p^{3/2}. MATCH: the IZ series with z^2=y gives exactly
#     J_{1/2}^{(3)}(z;p) = z * (p^{3/2};p)_inf/(p;p)_inf * Phi(z^2).
#   => Phi(y) = (p;p)_inf/(p^{3/2};p)_inf * J_{1/2}^{(3)}(sqrt(y); p) / sqrt(y).
#
# So Phi(y) = [(p;p)_inf/(p^{3/2};p)_inf] * (1/sqrt(y)) * J_{1/2}^{(3)}(sqrt(y);p)
#           = [(p;p)_inf/(p^{3/2};p)_inf] * (1/sqrt(y)) * sqrt(y)/sqrt(pi log p^{-2}) * I(sqrt(y))
#   where I(z) = INT exp(x^2/log p^2)/(p, -p e^{ix}, -q z^2 e^{ix}; p)_inf dx   (since p^{nu+1/2}=p, p^{1/2}=q)
#   The sqrt(y) cancels!  =>
#     Phi(y) = [(p;p)_inf/(p^{3/2};p)_inf] / sqrt(pi log p^{-2})
#                 * INT_{-inf}^{inf} exp(x^2/log p^2) / (p, -p e^{ix}, -q y e^{ix}; p)_inf  dx
#   with log p^2 = -4 tau, log p^{-2}=4 tau.   z^2=y so -q z^2 e^{ix} = -q y e^{ix}.  Clean.
import mpmath as mp
mp.mp.dps = 30

def qpoch_inf(a,p,tol=mp.mpf(10)**(-35),NM=200000):
    r=mp.mpf(1) if not isinstance(a,complex) else mp.mpc(1)
    ai=a
    for i in range(NM):
        r*=(1-ai); ai*=p
        if abs(ai)<tol: break
    return r

def Phi_series(y,p,b,K=300):
    s=mp.mpf(1);term=mp.mpf(1)
    for k in range(K):
        term*=-p**(k+1)*y/((1-p**(k+1))*(1-b*p**k));s+=term
        if abs(term)<mp.mpf(10)**(-40) and k>10:break
    return s

def Phi_IZ(y,p,q,T=40):
    # Phi(y) = C0 * INT exp(x^2/log p^2)/(p,-p e^{ix},-q y e^{ix};p)_inf dx
    pp=qpoch_inf(p,p); p32=qpoch_inf(p**mp.mpf(1.5),p)
    logp2=mp.log(p*p)  # = -4 tau
    C0 = (pp/p32)/mp.sqrt(mp.pi*(-logp2))
    pinf = qpoch_inf(p,p)  # the (p;p)_inf factor inside integrand (constant)
    def integ(x):
        e=mp.e**(1j*x)
        den = pinf * qpoch_inf(-p*e,p) * qpoch_inf(-q*y*e,p)
        return (mp.e**(x*x/logp2)/den).real   # integrand is even-ish; take real part
    val=mp.quad(integ,[-T,0,T])
    return C0*val

tau=mp.mpf("0.2"); q=mp.e**(-tau); p=q*q; b=q**3
for y in [mp.mpf("0.3"), mp.mpf("0.9"), mp.mpf("-0.5")]:
    ser=Phi_series(y,p,b)
    iz=Phi_IZ(y,p,q)
    print(f"y={mp.nstr(y,4):>7}  Phi_series={mp.nstr(ser,16):>20}  Phi_IZ={mp.nstr(iz,16):>20}  diff={mp.nstr(ser-iz,4)}")
