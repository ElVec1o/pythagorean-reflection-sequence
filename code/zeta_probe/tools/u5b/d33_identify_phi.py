#!/usr/bin/env python3
# Identify Phi(y)=sum_k (-1)^k p^{k(k+1)/2} y^k /[(p;p)_k (q3;p)_k]  (q3=p^{3/2}=q^3)
# as a basic hypergeometric series r-phi-s.  The term ratio:
#   t_{k+1}/t_k = (-1) p^{k+1} y /[(1-p^{k+1})(1-q3 p^k)]
# Standard r-phi-s term ratio for {}_r phi_s(a..;b..;p,x):
#   t_{k+1}/t_k = [ prod_i (1-a_i p^k) / prod_j (1-b_j p^k) ] * ((-1)^k p^{k(k-1)/2})^{1+s-r} * x /(1-p^{k+1})
# We have the extra p^{k(k+1)/2}/p^{?}. Compare: our explicit p^{k+1} factor and a single (1-q3 p^k) in den.
# Our ratio = x * p^{k+1} /[(1-q3 p^k)(1-p^{k+1})], x=-y.
# Write p^{k+1} = p * p^k.  A {}_0phi_1(;b;p,X) has ratio X/[(1-b p^k)(1-p^{k+1})] with the convention
# {}_0phi_1(-;b;p,z)= sum z^k ((-1)^k p^{k(k-1)/2})^{1}/[(p;p)_k (b;p)_k]  -> ratio includes (-1)p^k.
# Indeed {}_0phi_1 term ratio: t_{k+1}/t_k = (-1) p^k z /[(1-b p^k)(1-p^{k+1})].
# Ours: (-1) p^{k+1} y/[(1-q3 p^k)(1-p^{k+1})] = (-1)p^k (p y)/[...].  MATCH with b=q3, z=p y.
# So Phi(y) = {}_0phi_1(-; q3; p, p y)  with the (Gasper-Rahman) {}_0phi_1 convention
#   {}_0phi_1(-;b;p,z) = sum_k (-1)^k p^{k(k-1)/2} z^k /[(p;p)_k (b;p)_k].
# Check: our t_k = (-1)^k p^{k(k+1)/2} y^k = (-1)^k p^{k(k-1)/2} p^{k} y^k = (-1)^k p^{k(k-1)/2}(p y)^k. YES exact.
import mpmath as mp
mp.mp.dps = 40
def qpoch(a,p,n):
    r=mp.mpf(1);ai=a
    for i in range(n): r*=(1-ai);ai*=p
    return r
def Phi(y,p,q3,K=300):
    s=mp.mpf(1);term=mp.mpf(1)
    for k in range(K):
        term*=-p**(k+1)*y/((1-p**(k+1))*(1-q3*p**k));s+=term
        if abs(term)<mp.mpf(10)**(-50) and k>10:break
    return s
def basic_0phi1(b,z,p,K=300):
    # sum_k (-1)^k p^{k(k-1)/2} z^k /[(p;p)_k (b;p)_k]
    s=mp.mpf(0);
    for k in range(K):
        t=(-1)**k * p**(mp.mpf(k*(k-1))/2) * z**k /(qpoch(p,p,k)*qpoch(b,p,k))
        s+=t
        if abs(t)<mp.mpf(10)**(-50) and k>10:break
    return s
tau=mp.mpf("0.1");q=mp.e**(-tau);p=q*q;q3=q**3;y=mp.mpf("0.37")
print("Phi(y)             =",mp.nstr(Phi(y,p,q3),20))
print("0phi1(-;q3;p,p*y)  =",mp.nstr(basic_0phi1(q3,p*y,p),20))
print("diff =",mp.nstr(Phi(y,p,q3)-basic_0phi1(q3,p*y,p),4))
print()
print("=> Phi(y) = 0phi1(-; q3=p^{3/2}; p, p*y).  Sigma's inner kernel is a 0phi1 (q-Bessel).")
print("   Confluence: 0phi1(-;b;p,z) -> 0F1(;nu+1; -X) as p->1 (the classical Bessel limit).")
