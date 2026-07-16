#!/usr/bin/env python3
"""Apery-miracle test (paper2 rem:qSS addendum): NO denominator miracle.

Apery's zeta(3) proof works because the true denominators (d_n^3) are exponentially smaller
than the naive clearing. Measured here for the beta_2 partial sums S_N(s/t): the reduced
denominator equals 96-100% of the naive Pi_{i<=2N}(t^i - s^i) in log size, ratio -> 1 as N
grows (exact rational arithmetic). Cancellation is O(N) boundary noise in an O(N^2) exponent.
The ledger's arithmetic is exactly its worst-case costing; the last classical "measured
miracle" door is shut.
"""
from fractions import Fraction as Fr
import math

def SN(N, s, t):
    q = Fr(s, t); z = 2*q*(1-q)
    S = Fr(0)
    for k in range(N+1):
        num = (-1)**k*q**(k*(k-1))*z**k
        den = Fr(1)
        for i in range(1, 2*k+1): den *= (1-q**i)
        S += num/den
    return S

if __name__ == "__main__":
    for (s, t) in [(1, 2), (2, 5)]:
        for N in [4, 8, 12]:
            val = SN(N, s, t)
            naive = 1
            for i in range(1, 2*N+1): naive *= abs(t**i-s**i)
            print(f"(s,t)=({s},{t}) N={N}: log den(S_N)/log naive = "
                  f"{math.log(val.denominator)/math.log(naive):.4f}")
