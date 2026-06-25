#!/usr/bin/env python3
# ROUTE D3.3 setup: define Sigma, verify confluence Sigma -> 1-cos w, and
# set up generating function G(W,tau) = sum_k W^k u_k with
#   u_k = 2q (-2(1-q))^k q^{k^2+2k} / [ (q^2;q^2)_{k+1} (q^3;q^2)_k ]
# where W absorbs the (w^2 tau/2)-scaling so that the confluence limit is clean.
import mpmath as mp
mp.mp.dps = 40

def qpoch(a, p, n):
    # (a;p)_n = prod_{i=0}^{n-1} (1 - a p^i)
    r = mp.mpf(1)
    ai = a
    for i in range(n):
        r *= (1 - ai)
        ai *= p
    return r

def sigma_terms(tau, K):
    q = mp.e**(-tau)
    terms = []
    for k in range(K+1):
        num = 2*q * (-2*(1-q))**k * q**(k*k + 2*k)
        den = qpoch(q*q, q*q, k+1) * qpoch(q**3, q*q, k)
        terms.append(num/den)
    return terms

def Sigma(tau, K=400):
    return mp.fsum(sigma_terms(tau, K))

# Confluence check: with w = sqrt(2/tau), Sigma -> 1 - cos w
for tau in [mp.mpf("0.2"), mp.mpf("0.05"), mp.mpf("0.01"), mp.mpf("0.002")]:
    w = mp.sqrt(2/tau)
    S = Sigma(tau)
    target = 1 - mp.cos(w)
    print(f"tau={mp.nstr(tau,4):>8}  w={mp.nstr(w,6):>10}  Sigma={mp.nstr(S,12):>16}  1-cosw={mp.nstr(target,12):>16}  diff={mp.nstr(S-target,4)}")

print()
# Term ratio check: u_{k+1}/u_k = -2(1-q) q^{2k+3} / [(1-q^{2k+4})(1-q^{2k+3})]
tau = mp.mpf("0.1"); q = mp.e**(-tau)
t = sigma_terms(tau, 10)
for k in range(8):
    ratio = t[k+1]/t[k]
    pred = -2*(1-q)*q**(2*k+3) / ((1-q**(2*k+4))*(1-q**(2*k+3)))
    print(f"k={k}  ratio={mp.nstr(ratio,10):>16}  pred={mp.nstr(pred,10):>16}  ok={mp.nstr(ratio-pred,3)}")
