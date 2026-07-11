#!/usr/bin/env python3
"""Hankel determinants of the beta_2 moment sequence: cubic denominators => no escape from rho=1/2.

The one construction NOT covered by the rho=1/2 no-go ledger's lattice argument is a Hankel/resultant
determinant, where the (t^i - s^i) content might cancel and raise the arithmetic ratio. It does not.

THE HONEST QUANTITY. For irrationality the relevant size is the ARCHIMEDEAN log-height of the cleared
integer denominator (all primes). For g_k = (-1)^k q^{k(k-1)}/(q;q)_{2k} and q = s/t, the entries have
denominator prod_{i<=2k}(t^i - s^i) -- integers built from the PRIMITIVE PRIME DIVISORS of t^i - s^i
(NOT powers of t; e.g. at q=1/2 the denominators are products of factors of 2^i-1: 3,7,5,31,...).

MEASURED (exact, q=1/2, n=1..8): log2 |den(H_n)| = 8.3, 51.9, 148.8, 330.7, 621.5, 1027.7, 1594.9,
2345.7, i.e. ~ c n^3 with c ~ 4.5 (log2|den|/n^3 settles; /n^2 grows linearly). So the Hankel
determinant's denominator is CUBIC, one power worse than the already-losing quadratic remainder
q^{c n^2}: the natural cancellation object does not escape rho = 1/2, it deepens the deficit.

CAUTION (an earlier draft of this file was WRONG): the p-adic valuation v_t(H_n) = +n(n+1)(n+2) and
v_s(H_n) = +(n-1)n(n+1) are NUMERATOR content (t, s divide the numerator after clearing the q-Pochhammer
denominators) -- a red herring for the height. The height lives at the OTHER primes (dividing t^i-s^i),
and it is cubic. Both facts are recorded below; only the archimedean one bears on rho.

Also (symbolic, n<=3): den(H_n) is a product of cyclotomic polynomials Phi_d(q), but the NUMERATOR is a
non-cyclotomic "Hankel polynomial" (H_3's numerator has degree 68, coefficients up to 1793). The moment
sequence g_k is arithmetically GENERIC -- no miraculous q-Hankel product evaluation to exploit.

This closes the last natural-object loophole in paper2 prop:nogo. Exact arithmetic only.
"""
from fractions import Fraction as Fr
import math


def vp(x, p):
    if x == 0: return 10**9
    n, d = x.numerator, x.denominator
    v = 0
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v


def gk(k, q):
    num = (-1)**k * q**(k*(k-1)); den = Fr(1)
    for i in range(1, 2*k+1): den *= (1 - q**i)
    return num/den


def det(M):
    M = [row[:] for row in M]; n = len(M); s = Fr(1)
    for i in range(n):
        p = next((r for r in range(i, n) if M[r][i] != 0), None)
        if p is None: return Fr(0)
        if p != i: M[i], M[p] = M[p], M[i]; s = -s
        for r in range(i+1, n):
            f = M[r][i] / M[i][i]
            for c in range(i, n): M[r][c] -= f * M[i][c]
    d = s
    for i in range(n): d *= M[i][i]
    return d


def Hankel(n, q):
    return det([[gk(i+j, q) for j in range(n+1)] for i in range(n+1)])


if __name__ == "__main__":
    print("ARCHIMEDEAN height of den(H_n) at q=1/2 (the quantity that bears on rho):")
    print("  n | log2|den(H_n)| | /n^2 (grows) | /n^3 (settles ~4.5 = CUBIC)")
    for n in range(1, 9):
        H = Hankel(n, Fr(1, 2))
        ld = math.log2(H.denominator) if H.denominator > 1 else 0.0
        print(f"  {n} | {ld:9.2f} | {ld/n**2:6.2f} | {ld/n**3:6.3f}")
    print("\np-adic NUMERATOR content (a curiosity, NOT the height): v_t(H_n)=n(n+1)(n+2), v_s=(n-1)n(n+1):")
    for (s, t) in [(2, 5), (3, 7)]:
        row = []
        for n in range(1, 6):
            H = Hankel(n, Fr(s, t))
            row.append((n, vp(H, t), vp(H, s)))
        print(f"  q={s}/{t}: " + "  ".join(f"n={n}:v_t={vt},v_s={vs}" for n, vt, vs in row))
    print("\n=> den(H_n) archimedean ~ 2^{4.5 n^3} (CUBIC): the Hankel object deepens the rho=1/2 deficit. No escape.")
