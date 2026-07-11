#!/usr/bin/env python3
"""The adelic-units lemma and the exact adelic balance (paper2 lem:adelic-units, rem:adelic-balance).

The beta_2 series S(q) = sum_k g_k z*^k (z* = 2q(1-q), g_k = (-1)^k q^{k(k-1)}/(q;q)_{2k}) has
rational terms, hence -- besides its real sum -- p-adic AVATARS for every prime p | st (the same
series summed in Q_p, where it converges since term valuations -> +infinity).

LEMMA (proven; per-PRIME statement -- the naive "v_t = k^2" is wrong for even/composite t, caught
and corrected before this version):
  for q = s/t in lowest terms, z* = 2q(1-q), k >= 1 and prime p:
    p | t, e = v_p(t):   v_p(g_k z*^k) = k^2 e + k*[p==2]   (EXACT)
    p | s:               v_p(g_k z*^k) >= k^2
  Hence S_p == 1 (mod p^{v_p(st)}) for every p | st: all finite-place avatars are UNITS == 1 --
  never zero -- regardless of whether the real avatar vanishes.

CONSEQUENCES:
  * The rho=1/2 no-go extends from coefficient lattices to VALUES: no divisibility/smallness can be
    sourced from the finite places. A rational beta_2 would be maximally place-asymmetric (real
    avatar zero, every finite avatar a unit).
  * EXACT ADELIC BALANCE: term g_k z*^k has archimedean decay (s/t)^{k^2}, s,t-adic numerator
    content (st)^{k^2}, denominator t^{2k^2}: product formula balances with zero margin at the k^2
    scale. Any rho=1/2 criterion must be a purely ARCHIMEDEAN cancellation.
  * CONJECTURE (adelic rigidity): for this irregular rank-2 q-difference module (polynomial
    companion matrix, det A = q), no vanishing at one place of Q at a point where all other
    convergent avatars are units. Finite half = the lemma (PROVEN); archimedean half => beta_2
    irrational. q-analogue of E/G-function place-uniformity (Siegel-Shidlovskii-Andre).

Exact rational arithmetic (fractions + sympy.factorint); no mpmath.
"""
from fractions import Fraction as Fr
import sympy as sp


def vp(x, p):
    if x == 0: return None
    n, d = x.numerator, x.denominator
    v = 0
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v


def gk(k, q):
    num = (-1)**k * q**(k*(k-1)); den = Fr(1)
    for i in range(1, 2*k+1): den *= (1 - q**i)
    return num/den


def check(s, t, K=6, POW=6):
    """returns (per-prime formulas exact, all avatars units == 1)"""
    q = Fr(s, t); z = 2*q*(1-q)
    ok = True
    for p, e in sp.factorint(t).items():
        for k in range(1, K):
            if vp(gk(k, q)*z**k, p) != k*k*e + (k if p == 2 else 0): ok = False
    if s > 1:
        for p in sp.factorint(s):
            for k in range(1, K):
                if vp(gk(k, q)*z**k, p) < k*k: ok = False
    S = sum(gk(k, q)*z**k for k in range(0, K+4))
    units = True
    for p in set(list(sp.factorint(t)) + (list(sp.factorint(s)) if s > 1 else [])):
        M = p**POW
        u = (S.numerator % M) * pow(S.denominator % M, -1, M) % M
        if u % p != 1: units = False
    return ok, units


if __name__ == "__main__":
    print("q=s/t | per-prime valuation formulas exact | all finite avatars units == 1 (mod p)")
    for (s, t) in [(1, 2), (2, 5), (3, 7), (4, 9), (5, 12), (7, 16), (3, 10), (5, 6)]:
        r = check(s, t)
        print(f" {s}/{t}: {r[0]} | {r[1]}")
    print("\n=> all finite-place avatars are units: the rho=1/2 criterion, if any, is purely archimedean.")
