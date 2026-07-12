#!/usr/bin/env python3
"""Effective non-rationality of q* (paper2 prop:effective) -- fully certified.

THEOREM (unconditional). The least positive root q* of S(q) = sum_k (-1)^k q^{k(k-1)} (2q(1-q))^k
/ (q;q)_{2k} admits NO rational representation s/t with t <= 10^191. Hence beta_2 = 1/sqrt(q*),
if rational u/v in lowest terms, requires u > 10^95.

Certification chain (all interval arithmetic = mpmath.iv, outward rounding; tails bounded by
(q;q)_{2k} >= (1-2q)/(1-q) > 0 for q < 1/2 and term ratio < 1/2 past truncation):
  (i)   S > 0 on [0, 0.40]            (400 certified chunks);
  (ii)  S' <= -1 on [0.40, 0.46]      (600 certified chunks) => at most one zero there;
  (iii) S(a) > 0 > S(b) certified for a = 385-digit truncation of q*, b = a + 2e-385
        => q* in [a,b], width 2e-385;
  (iv)  the Stern-Brocot minimal fraction s0/t0 in [a,b] has t0 >= 10^192 (exact rational
        comparison) and certified S(s0/t0) != 0. Farey: any m/n in [a,b] with n <= 10^191
        and m/n != s0/t0 would satisfy |m/n - s0/t0| >= 1/(n t0) >= 10^-384 > b-a. So no
        rational with denominator <= 10^191 lies in [a,b]; in particular none equals q*.

This does NOT prove irrationality (no finite computation can); it is the maximal unconditional
Diophantine content extractable by certified computation, and the first such statement for beta_2.
"""
import mpmath as mp
from fractions import Fraction as Fr

iv = mp.iv


def S_iv(num, den, K=38, dps=440):
    """certified enclosure of S(num/den), 0 < num/den < 1/2"""
    iv.dps = dps
    q = iv.mpf(num)/iv.mpf(den)
    z = 2*q*(1-q)
    tot = iv.mpf(0); poch = iv.mpf(1)
    for k in range(K):
        if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
        tot += iv.mpf((-1)**k)*q**(k*(k-1))*z**k/poch
    c0 = (1-2*q)/(1-q)
    tail = 2*q**(K*(K-1))*z**K/c0
    return tot + iv.mpf([-1, 1])*abs(tail)


def S_iv_wide(lo, hi, K=40, dps=60):
    iv.dps = dps
    q = iv.mpf([lo, hi])
    z = 2*q*(1-q)
    tot = iv.mpf(0); poch = iv.mpf(1)
    for k in range(K):
        if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
        tot += iv.mpf((-1)**k)*q**(k*(k-1))*z**k/poch
    c0 = (1-2*iv.mpf(hi))/(1-iv.mpf(hi))
    tail = 2*iv.mpf(hi)**(K*(K-1))*(2*iv.mpf(hi))**K/c0
    return tot + iv.mpf([-1, 1])*abs(tail)


def Sp_iv(lo, hi, K=40, dps=60):
    """certified enclosure of S'(q) on [lo,hi] (term-by-term logarithmic weights)"""
    iv.dps = dps
    q = iv.mpf([lo, hi])
    z = 2*q*(1-q)
    tot = iv.mpf(0); poch = iv.mpf(1); E = iv.mpf(0)
    for k in range(K):
        if k > 0:
            poch *= (1-q**(2*k-1))*(1-q**(2*k))
            E += (2*k-1)*q**(2*k-2)/(1-q**(2*k-1)) + (2*k)*q**(2*k-1)/(1-q**(2*k))
        t_k = iv.mpf((-1)**k)*q**(k*(k-1))*z**k/poch
        D_k = iv.mpf(k*(k-1))/q + iv.mpf(k)*(1-2*q)/(q*(1-q)) + E
        tot += t_k*D_k
    hiq = iv.mpf(hi)
    c0 = (1-2*hiq)/(1-hiq)
    tail = 2*hiq**(K*(K-1))*(2*hiq)**K*10*K*K/c0
    return tot + iv.mpf([-1, 1])*abs(tail)


def min_denom_rational(lo, hi):
    """the rational with smallest denominator in [lo,hi] (continued-fraction algorithm)"""
    la, lb = lo, hi
    cf = []
    while True:
        fa = la.numerator // la.denominator
        fb = lb.numerator // lb.denominator
        if fa != fb:
            cf.append(min(fa, fb)+1)
            break
        cf.append(fa)
        fra = la - fa
        if fra == 0: break
        la, lb = 1/(lb-fb), 1/fra
    n, d = 1, 0
    for x in reversed(cf):
        n, d = x*n + d, n
    return Fr(n, d)


if __name__ == "__main__":
    # (i) S > 0 on [0, 0.40]
    ok1 = all(S_iv_wide(repr(0.001*j), repr(0.001*(j+1))) > 0 for j in range(400))
    print("(i)   S > 0 on [0,0.40]:", ok1)
    # (ii) S' <= -1 on [0.40, 0.46]
    ok2 = all(Sp_iv(repr(0.40+0.06*j/600), repr(0.40+0.06*(j+1)/600)) < -1 for j in range(600))
    print("(ii)  S' <= -1 on [0.40,0.46]:", ok2)
    # (iii) certified bracket at width 2e-385
    mp.mp.dps = 420
    def S_f(q, K=60):
        t = mp.mpf(0); poch = mp.mpf(1)
        for k in range(K):
            if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
            term = mp.mpf((-1)**k)*q**(k*(k-1))*(2*q*(1-q))**k/poch
            t += term
            if k > 10 and abs(term) < mp.mpf(10)**-430: break
        return t
    qg = mp.findroot(S_f, mp.mpf('0.4494536305589480461255458'))
    D = 385
    a = Fr(int(mp.nstr(qg, 400, strip_zeros=False).split('.')[1][:D]), 10**D)
    b = a + Fr(2, 10**D)
    Sa = S_iv(a.numerator, a.denominator); Sb = S_iv(b.numerator, b.denominator)
    ok3 = (Sa > 0) and (Sb < 0)
    print("(iii) S(a) > 0 > S(b) certified (width 2e-385):", bool(ok3))
    # (iv) Farey exclusion
    s0 = min_denom_rational(a, b)
    inside = a <= s0 <= b
    t0_digits = len(str(s0.denominator))
    S0 = S_iv(s0.numerator, s0.denominator)
    excl = not (S0.a <= 0 <= S0.b)
    print(f"(iv)  s0/t0 in [a,b]: {inside}; t0 has {t0_digits} digits (>=193 needed); S(s0)!=0: {excl}")
    if ok1 and ok2 and ok3 and inside and t0_digits >= 193 and excl:
        print("\nTHEOREM: q* has no rational representation with denominator <= 10^191;")
        print("         beta_2 = u/v (lowest terms) requires u > 10^95.")
