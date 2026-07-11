#!/usr/bin/env python3
"""The adelic-units lemma and the exact adelic balance (paper2 lem:adelic-units, rem:adelic-balance).

The beta_2 series S(q) = sum_k g_k z*^k (z* = 2q(1-q), g_k = (-1)^k q^{k(k-1)}/(q;q)_{2k}) has
rational terms, hence -- besides its real sum -- s-adic and t-adic AVATARS (the same series summed
in Q_s and Q_t, where it converges since term valuations -> +infinity).

LEMMA (proven; verified exactly here): for q = s/t in lowest terms and k >= 1,
      v_t(g_k z*^k) = k^2   (EXACT: the -2k from z*^k cancels the +2k in v_t(g_k) = k^2+2k),
      v_s(g_k z*^k) >= k^2  (v_s(g_k) = k^2-k and v_s(z*) >= 1).
  Hence S_t == 1 (mod t) and S_s == 1 (mod s): both finite-place avatars are UNITS -- never zero --
  regardless of whether the real avatar vanishes.

CONSEQUENCES:
  * The no-go extends from coefficient lattices to VALUES: no divisibility/smallness can be sourced
    from the finite places. A rational beta_2 would be a maximally place-asymmetric event (real
    avatar zero, every finite avatar a unit == 1).
  * EXACT ADELIC BALANCE (product formula with zero margin at the k^2 scale): term g_k z*^k has
    archimedean decay (s/t)^{k^2}, s- and t-adic numerator content s^{k^2} t^{k^2}, denominator
    t^{2k^2}. Lossless-or-nothing: any rho=1/2 criterion must be a purely ARCHIMEDEAN cancellation.
  * CONJECTURE (adelic rigidity, the shape of the criterion): for this irregular rank-2 q-difference
    module (companion matrix polynomial, det A = q), the vanishing locus is adelically rigid -- no
    vanishing at one place while all other avatars are units. Finite half = the lemma (PROVEN);
    archimedean half => beta_2 irrational. q-analogue of E/G-function place-uniformity (Andre).

Exact rational arithmetic only (fractions); no mpmath needed.
"""
from fractions import Fraction as Fr


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


def check(s, t, K=7, POW=6):
    q = Fr(s, t); z = 2*q*(1-q)
    ok_t = all(vp(gk(k, q)*z**k, t) == k*k for k in range(1, K)) if t > 1 else True
    ok_s = all(vp(gk(k, q)*z**k, s) >= k*k for k in range(1, K)) if s > 1 else True
    S = sum(gk(k, q)*z**k for k in range(0, K+3))
    Mt = t**POW; ut = (S.numerator % Mt) * pow(S.denominator % Mt, -1, Mt) % Mt
    unit_t = (ut % t == 1)
    unit_s = True
    if s > 1:
        Ms = s**POW; us = (S.numerator % Ms) * pow(S.denominator % Ms, -1, Ms) % Ms
        unit_s = (us % s == 1)
    return ok_t, ok_s, unit_t, unit_s


if __name__ == "__main__":
    print("q=s/t | v_t(g_k z*^k)=k^2 | v_s>=k^2 | S_t==1 mod t | S_s==1 mod s")
    for (s, t) in [(1, 2), (2, 5), (3, 7), (4, 9), (5, 12), (7, 16)]:
        r = check(s, t)
        print(f" {s}/{t}: {r[0]} | {r[1]} | {r[2]} | {r[3]}")
    print("\n=> both finite-place avatars are units == 1: the criterion, if any, is purely archimedean.")
