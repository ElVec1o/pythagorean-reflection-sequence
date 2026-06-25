#!/usr/bin/env python3
# Identify Sigma with Hahn-Exton q-Bessel; derive q-integral (Jackson-sum) form.  Optimized/cached.
import mpmath as mp
mp.mp.dps = 40

def make(tau):
    q = mp.e**(-tau); p = q*q
    return q, p

def Sigma_direct(tau, K=300):
    q,p = make(tau)
    s = mp.mpf(0); term = 2*q  # k=0: num=2q, den=(p;p)_1 (..)_0 = (1-p)
    # build iteratively via ratio u_{k+1}/u_k = -2(1-q) q^{2k+3}/[(1-q^{2k+4})(1-q^{2k+3})]
    u = 2*q/(1-p)
    s = u
    for k in range(K):
        u *= -2*(1-q)*q**(2*k+3)/((1-q**(2*k+4))*(1-q**(2*k+3)))
        s += u
        if abs(u) < mp.mpf(10)**(-50) and k>20: break
    return s

def Phi(y, p, q3, K=300):
    # Phi(y)=sum_k (-1)^k p^{k(k+1)/2} y^k/[(p;p)_k (p^{3/2};p)_k]; build iteratively.
    # term_{k+1}/term_k = (-1) p^{k+1} y /[(1-p^{k+1})(1-q3 p^k)]
    s = mp.mpf(1); term = mp.mpf(1)
    for k in range(K):
        term *= -p**(k+1)*y/((1-p**(k+1))*(1-q3*p**k))
        s += term
        if abs(term) < mp.mpf(10)**(-50) and k>10: break
    return s

tau = mp.mpf("0.1"); q,p = make(tau); q3 = q**3; z2 = 2*q*(1-q)
Sd = Sigma_direct(tau)
# Jackson sum: Sigma = 2q sum_{j>=0} p^j Phi(p^j z2).  p^j decays; stop when p^j tiny.
Jmax = int(mp.ceil(60/(-mp.log10(p)))) + 5
Sj = 2*q*mp.fsum([p**j * Phi(p**j*z2, p, q3) for j in range(Jmax)])
print(f"tau={mp.nstr(tau,3)}  Jmax={Jmax}")
print("Sigma direct      =", mp.nstr(Sd,22))
print("Sigma Jackson-sum =", mp.nstr(Sj,22))
print("diff =", mp.nstr(Sd-Sj,5))
print()
# Confirm at another tau
for tt in [mp.mpf("0.3"), mp.mpf("0.03")]:
    q,p = make(tt); q3=q**3; z2=2*q*(1-q)
    Sd = Sigma_direct(tt); Jmax=int(mp.ceil(60/(-mp.log10(p))))+5
    Sj = 2*q*mp.fsum([p**j*Phi(p**j*z2,p,q3) for j in range(Jmax)])
    print(f"tau={mp.nstr(tt,3):>7}: direct={mp.nstr(Sd,16)}  jackson={mp.nstr(Sj,16)}  diff={mp.nstr(Sd-Sj,4)}")
