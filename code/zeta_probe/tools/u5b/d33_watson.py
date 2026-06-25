#!/usr/bin/env python3
# WATSON / Mellin-Barnes integral for Phi(y)=0phi1(-;b;p,z),  z=p*y, b=p^{3/2}=q3.
#
# Strategy: build a Barnes-type integrand whose residues at the poles s=-k (k=0,1,2,...) of a chosen
# pole-generating factor reproduce the series terms t_k = (-1)^k p^{k(k-1)/2} z^k/[(p;p)_k (b;p)_k].
#
# Pole-generating factor:  G(s) = pi/sin(pi s) = Gamma(s)Gamma(1-s) ... gives simple poles at all integers s.
# At s = k (k>=0): Res_{s=k} pi/sin(pi s) = (-1)^k.   (Res of pi/sin(pi s) at s=n is (-1)^n.)
# We want the SUM over k>=0 of residues to equal Phi.  Use a contour that, when closed to the RIGHT
# (enclosing s=0,1,2,...), picks up sum_k (-1)^k * [rest(k)].   We need rest(k)=p^{k(k-1)/2} z^k/[(p;p)_k(b;p)_k].
#
# Building blocks (q-Gamma-free, using (.;p)_inf):
#   1/(p;p)_k = (p^{k+1};p)_inf/(p;p)_inf.   As a function of s with k->s: f1(s)=(p^{s+1};p)_inf/(p;p)_inf.
#       At s=k integer>=0 this is 1/(p;p)_k.  At s=k it's analytic (no pole) -> fine.
#   1/(b;p)_k = (b p^k;p)_inf/(b;p)_inf.   f2(s)=(b p^s;p)_inf/(b;p)_inf.  At s=k: 1/(b;p)_k.
#   z^k:  z^s.
#   p^{k(k-1)/2}:  this is theta-like, p^{s(s-1)/2}.  ENTIRE in s (since p^{s(s-1)/2}=exp(ln p * s(s-1)/2)).
# So define
#   H(s) = p^{s(s-1)/2} z^s * (p^{s+1};p)_inf/(p;p)_inf * (b p^s;p)_inf/(b;p)_inf.
# Then Phi(y) = sum_{k>=0} (-1)^k H(k) = sum_{k>=0} Res_{s=k}[ -pi/sin(pi s) ] H(s) ... need sign/orientation.
# Res_{s=k} pi/sin(pi s) = (-1)^k.  So  (1/2pi i) oint_{enclosing 0,1,2..} pi/sin(pi s) H(s) ds
#    = sum_{k>=0} (-1)^k H(k) = Phi   (if contour is clockwise around right poles => -2pi i sum res;
#    take the standard Watson orientation: integral over vertical line, close to the right).
#
# Concretely (Watson): Phi = (1/2i) \int_{c-i\infty}^{c+i\infty} H(s)/sin(pi s) ds  with -1<c<0,
#   provided H(s)/sin(pi s) -> 0 fast enough in Im s and the right-half residues sum to Phi.
# Equivalent real form: s = c + i t.   Let's just test numerically.
import mpmath as mp
mp.mp.dps = 30

def qpoch_inf(a,p,tol=mp.mpf(10)**(-35)):
    r=mp.mpf(1);ai=a;
    for i in range(100000):
        r*= (1-ai); ai*=p
        if abs(ai)<tol: break
    return r

def Phi_series(y,p,b,K=300):
    s=mp.mpf(1);term=mp.mpf(1)
    for k in range(K):
        term*=-p**(k+1)*y/((1-p**(k+1))*(1-b*p**k));s+=term
        if abs(term)<mp.mpf(10)**(-40) and k>10:break
    return s

def Phi_watson(y,p,b,c=mp.mpf("-0.5"),T=60,N=4000):
    z = p*y
    pp_inf = qpoch_inf(p,p)
    b_inf = qpoch_inf(b,p)
    lnp = mp.log(p)
    def H(s):
        return mp.e**(lnp*s*(s-1)/2) * mp.e**(s*mp.log(z) if z>0 else (s*mp.log(-z)+s*mp.pi*1j)) \
               * qpoch_inf(p**(s+1),p)/pp_inf * qpoch_inf(b*p**s,p)/b_inf
    def integrand(t):
        s = c + 1j*t
        return H(s)/mp.sin(mp.pi*s)
    # integrate over t in [-T,T]; (1/2i) prefactor; ds = i dt
    val = mp.quad(integrand, [-T, 0, T])
    return (1/(2j))*1j*val   # (1/2i)*\int H/sin ds, ds=i dt

tau=mp.mpf("0.2"); q=mp.e**(-tau); p=q*q; b=q**3; y=mp.mpf("0.3")
ser=Phi_series(y,p,b)
wat=Phi_watson(y,p,b)
print(f"tau={mp.nstr(tau,3)}  y={mp.nstr(y,3)}")
print("Phi series  =",mp.nstr(ser,18))
print("Phi watson  =",mp.nstr(wat,18))
print("diff =",mp.nstr(ser-wat,5))
