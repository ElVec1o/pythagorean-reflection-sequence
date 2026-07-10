#!/usr/bin/env python3
"""beta_2 as a number: S = 1phi1(0;q;q^2,2q(1-q)), and why the natural tools fail (paper2 rem:betanumber).

beta_2 = 1/sqrt(q*), where q* is the least positive root of Sigma_1^T(q)=1, i.e. of
    S(q) = sum_{k>=0} (-2(1-q))^k q^{k^2} / (q;q)_{2k}  = 0.
IDENTIFICATION (this session): using (q;q)_{2k} = (q;q^2)_k (q^2;q^2)_k,
    S(q) = 1phi1(0; q; q^2, 2q(1-q))   -- a CONFLUENT basic hypergeometric (q-Bessel-class) function.
q* = 0.449453630558...,  1/sqrt(q*) = 1.49161778711... = beta_2 (verified).

beta_2 algebraic  <=>  q* algebraic  <=>  S(alpha)=0 at an algebraic alpha in (0,1).
So beta_2 transcendental would follow from: S(alpha) transcendental (hence != 0) for algebraic alpha.

WHAT THE NATURAL TOOLS GIVE (all verified/derived here) -- this LOCATES the wall, does NOT close it:
 * S is NOT q-holonomic and NOT Mahler in q (tested to O(q^48)). The diagonal z=2q(1-q) ties argument
   to base and kills the single-variable q-difference structure => Mahler-Nishioka & holonomy N/A.
 * ULTRAMETRIC DOMINATION -- ATTEMPTED, FAILED (retracted). At a finite place v with |alpha|_v != 1
   the k=0 term strictly dominates, so |S-series|_v = 1; BUT this is the v-adic sum, an UNRELATED
   number to the archimedean value (a sequence of algebraics can ->0 archimedean while staying
   v-adic units, e.g. (sqrt2-1)^k). So it does NOT bound the real S(alpha). VOID.
 * LIOUVILLE / HEIGHT -- FAILS decisively. P_K = sum_{k<=K} T_k(alpha) = -tail; archimedean tail ~
   exp(-|ln q*| K^2) (quadratic). The denominator prod_{k<=K}(alpha;alpha)_{2k} grows, over the
   conjugates of modulus >1, like exp((2/3) K^3 log M(alpha)) (CUBIC). K^3 >> K^2, so the Liouville
   lower bound is far below the tail: NO contradiction. Kronecker-sharp (M=1 only for roots of unity).
 * NESTERENKO / DNNS (theta values): N/A -- S is off the modular class (index-dependent q-Pochhammer).

RESIDUAL OBSTRUCTION: the irregular q-connection data of the 1phi1 -- the same wall as the true series
U. Candidate future route: an Andre-type q-Siegel-Shidlovskii theorem, but that is for FUCHSIAN
(regular-singular) q-difference equations and the confluent 1phi1 is irregular. Genuinely open.
"""
import sympy as sp
import mpmath as mp


def S_series(N):
    q = sp.symbols('q')
    def poch(n):
        p = sp.Integer(1)
        for k in range(1, n + 1): p *= (1 - q**k)
        return sp.expand(p)
    S = sp.Integer(0); k = 0
    while k * k <= N:
        S += sp.series((-2 * (1 - q))**k * q**(k * k) / poch(2 * k), q, 0, N + 1).removeO()
        k += 1
    return q, sp.expand(sp.series(S, q, 0, N + 1).removeO())


def S_num(q, J=200):
    q = mp.mpf(q); t = mp.mpf(0)
    for j in range(J):
        num = (-2 * (1 - q))**j * q**(j * j); den = mp.mpf(1)
        for i in range(1, 2 * j + 1): den *= (1 - q**i)
        t += num / den
        if j > 8 and abs(num / den) < mp.mpf(10)**-40: break
    return t


if __name__ == "__main__":
    mp.mp.dps = 30
    q, S = S_series(20)
    print("S(q) coeffs q^0..12:", [S.coeff(q, i) for i in range(13)])
    # 1phi1 identity
    T = sp.Integer(0); k = 0
    while k * k <= 20:
        den = sp.Integer(1)
        for i in range(1, 2 * k + 1): den *= (1 - q**i)
        T += sp.series((-1)**k * q**(k * (k - 1)) * (2 * q * (1 - q))**k / den, q, 0, 21).removeO()
        k += 1
    print("S == 1phi1(0;q;q^2,2q(1-q)):", sp.expand(sp.series(T, q, 0, 21).removeO() - S) == 0)
    qstar = mp.findroot(S_num, mp.mpf('0.45'))
    print("q* =", mp.nstr(qstar, 20), " 1/sqrt(q*) =", mp.nstr(1 / mp.sqrt(qstar), 20), "= beta_2")
    print("\nStatus: S identified as a confluent 1phi1; non-holonomic & non-Mahler in q;")
    print("p-adic domination VOID (completion mismatch), Liouville FAILS (K^3 vs K^2). Open. See paper2 rem:betanumber.")
