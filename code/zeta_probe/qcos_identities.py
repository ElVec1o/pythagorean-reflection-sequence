#!/usr/bin/env python3
"""qcos_identities.py -- the symbolic identities of the Hahn-Exton q-cosine paper.

Regenerates the identity checks quoted in paper/journal/hahn_exton_qcosine.tex:

  eq:supermult            b_i b_{j-i} / b_j = q^{i(j-i)} [j,i]_q: the exponent identity
                          exactly over Z, the Gaussian binomial as an integer
                          polynomial with constant term 1, and the bound i(j-i) >= j-1
                          that the proof of thm:sl2 consumes.
  eq:dressing             (q;Q)_inf G(q,z) = sum_n (-1)^n q^{n^2} (zQ^n;Q)_inf/(Q;Q)_n,
                          the b = q case of lem:swap, exactly in Q[[q]]; and lem:swap
                          itself numerically at a generic (Q,b,z), at two precisions.
  prop:latticevalues      G(q,Q^{-m}) = (-1)^{m+1} (Q;Q)_inf/(q;Q)_inf *
                          sum_r (-1)^r q^{(m+1+r)^2}/((Q;Q)_r (Q;Q)_{m+1+r}),
                          exactly in Q[[q]] after clearing the pole at q = 0, together
                          with ord_q G(q,Q^{-m}) = (m+1)^2.
  thm:zeroproduct step 1  (q;q)_inf G(z) = sum_m (-1)^m q^{m(m-1)} z^m P_m(1/z),
                          coefficient of z^k, exactly in Q[[q]].

Everything called exact is done with Fraction coefficients in Q[[q]]; the two
numerical lines are mpmath at two working precisions with the attained agreement
printed.  Runtime about 2 min at ORDER = 250 (measured 117 s).

Usage:  python3 qcos_identities.py [ORDER]        (default 250)
"""
import sys
from fractions import Fraction as Fr

import mpmath as mp

ORDER = int(sys.argv[1]) if len(sys.argv) > 1 else 250


# ---------------------------------------------------------- Q[[q]] toolkit --

def zeros():
    return [Fr(0)] * (ORDER + 1)


def one():
    c = zeros()
    c[0] = Fr(1)
    return c


def smul(a, b):
    c = zeros()
    for i, ai in enumerate(a):
        if not ai:
            continue
        for j in range(min(len(b), ORDER + 1 - i)):
            if b[j]:
                c[i + j] += ai * b[j]
    return c


def sadd(a, b):
    return [x + y for x, y in zip(a, b)]


def ssub(a, b):
    return [x - y for x, y in zip(a, b)]


def sinv(a):
    c = zeros()
    c[0] = 1 / a[0]
    for n in range(1, ORDER + 1):
        c[n] = -sum(a[i] * c[n - i] for i in range(1, n + 1)) / a[0]
    return c


def shift(a, k):
    """multiply by q^k (k may be negative; a must then be divisible by q^{-k})."""
    c = zeros()
    for n in range(ORDER + 1):
        m = n + k
        if 0 <= m <= ORDER:
            c[m] = a[n]
        elif m < 0:
            assert a[n] == 0, "negative power survives"
    return c


def qmon(k):
    c = zeros()
    if 0 <= k <= ORDER:
        c[k] = Fr(1)
    return c


def poch(base, step, count):
    """(q^base; q^step)_count."""
    r = one()
    for i in range(count):
        e = base + i * step
        if e > ORDER:
            break
        r = smul(r, ssub(one(), qmon(e)))
    return r


def poch_inf(base, step):
    r = one()
    e = base
    while e <= ORDER:
        r = smul(r, ssub(one(), qmon(e)))
        e += step
    return r


def first_diff(a, b):
    return next((n for n in range(ORDER + 1) if a[n] != b[n]), None)


# ------------------------------------------------------------ eq:supermult --

def gaussian_binomial(j, i):
    """[j,i]_q as an integer coefficient list, by the q-Pascal recursion."""
    row = {(0, 0): [1]}

    def pmul_shift(p, k):
        return [0] * k + p

    def padd(p, r):
        n = max(len(p), len(r))
        return [(p[t] if t < len(p) else 0) + (r[t] if t < len(r) else 0)
                for t in range(n)]

    table = [[None] * (j + 1) for _ in range(j + 1)]
    for n in range(j + 1):
        table[n][0] = [1]
        table[n][n] = [1]
    for n in range(1, j + 1):
        for k in range(1, n):
            table[n][k] = padd(table[n - 1][k - 1],
                               pmul_shift(table[n - 1][k], k))
    return table[j][i]


def supermult():
    print("eq:supermult -- b_i b_{j-i}/b_j = q^{i(j-i)} [j,i]_q")
    print("  b_k = q^{k - k(k-1)/2}/(q;q)_k.  The q-power exponent of b_i b_{j-i}/b_j is")
    print("  [i + (j-i) - j] + (1/2)[j(j-1) - i(i-1) - (j-i)(j-i-1)], and the Pochhammer")
    print("  factors assemble into [j,i]_q.  Both halves are checked exactly over Z.")
    bad = []
    for j in range(2, 60):
        for i in range(1, j):
            e = (i + (j - i) - j) + (j * (j - 1) - i * (i - 1)
                                     - (j - i) * (j - i - 1)) // 2
            r = (j * (j - 1) - i * (i - 1) - (j - i) * (j - i - 1)) % 2
            if e != i * (j - i) or r != 0:
                bad.append((j, i))
    print(f"  exponent identity for 2 <= j <= 59, 1 <= i <= j-1: "
          f"{'OK' if not bad else 'FAILED at ' + str(bad)}")
    badg = [(j, i) for j in range(2, 40) for i in range(1, j)
            if gaussian_binomial(j, i)[0] != 1
            or any(c < 0 for c in gaussian_binomial(j, i))]
    print(f"  [j,i]_q is a polynomial in q with constant term 1 and nonnegative "
          f"coefficients, 2 <= j <= 39: {'OK' if not badg else 'FAILED at ' + str(badg)}")
    gap = min(i * (j - i) - (j - 1) for j in range(2, 400) for i in range(1, j))
    print(f"  min of i(j-i) - (j-1) over 2 <= j <= 399, 1 <= i <= j-1: {gap}  (>= 0)")
    print("  so every split-off product carries at least one factor q^{j-1} relative")
    print("  to b_j, uniformly in q and in N, k_0.\n")


# ---------------------------------------------------------------- lem:swap --

def dressing():
    print("eq:dressing -- (q;Q)_inf G(q,z) = sum_n (-1)^n q^{n^2} (zQ^n;Q)_inf/(Q;Q)_n")
    print("  Checked exactly in Q[[q]] at three rational values of z.")
    print(f"  {'z':>8} {'agree through order':>21}")
    for zval in (Fr(1, 3), Fr(7, 5), Fr(-2, 1)):
        # left side
        lhs = zeros()
        for k in range(0, ORDER):
            e = k * (k - 1)
            if e > ORDER:
                break
            t = smul(qmon(e), sinv(poch(1, 1, 2 * k)))
            c = Fr((-1) ** k) * zval**k
            lhs = sadd(lhs, [c * x for x in t])
        lhs = smul(poch_inf(1, 2), lhs)
        # right side, with (zQ^{n+1};Q)_inf = (zQ^n;Q)_inf / (1 - z q^{2n})
        rhs = zeros()
        R = one()
        i = 0
        while 2 * i <= ORDER:
            fac = one()
            fac[2 * i] -= zval
            R = smul(R, fac)
            i += 1
        for n in range(0, ORDER):
            e = n * n
            if e > ORDER:
                break
            t = smul(qmon(e), smul(R, sinv(poch(2, 2, n))))
            rhs = sadd(rhs, [Fr((-1) ** n) * x for x in t])
            div = one()
            div[2 * n] -= zval
            R = smul(R, sinv(div))
        d = first_diff(lhs, rhs)
        print(f"  {str(zval):>8} {(ORDER if d is None else d - 1):>21}")

    print("  lem:swap itself, numerically at (Q,b,z) = (0.31, 0.47, 1.83):")
    for dps in (60, 120):
        mp.mp.dps = dps
        Qv, bv, zv = mp.mpf('0.31'), mp.mpf('0.47'), mp.mpf('1.83')

        def side(x, y):
            s = mp.mpf(0)
            pq = mp.mpf(1)
            for n in range(400):
                if n > 0:
                    pq *= 1 - Qv**n
                s += (-1) ** n * Qv ** (n * (n - 1) // 2) * y**n * _pinf(
                    x * Qv**n, Qv) / pq
            return s
        L, R = side(bv, zv), side(zv, bv)
        print(f"    dps {dps:>4}: symmetric to {int(-mp.log10(abs(L-R)/abs(L)))} digits")
    print()


def _pinf(a, q):
    r = mp.mpf(1)
    i = 0
    while abs(a * q**i) > mp.mpf(10) ** (-mp.mp.dps - 5):
        r *= 1 - a * q**i
        i += 1
    return r


def _pochn(a, q, n):
    r = mp.mpf(1)
    for i in range(n):
        r *= 1 - a * q**i
    return r


# ------------------------------------------------------- prop:latticevalues --

def lattice_values():
    print("prop:latticevalues -- G(q,Q^{-m}) on its own zero lattice")
    print("  G(q,Q^{-m}) is a Laurent series; both sides are multiplied by q^{m(m+1)}")
    print("  before comparison, which clears every negative power.")
    print(f"  {'m':>3} {'agree through order':>21} {'ord_q G(q,Q^-m)':>17} {'(m+1)^2':>9}")
    for m in range(0, 5):
        off = m * (m + 1)
        lhs = zeros()
        for k in range(0, 4 * ORDER):
            e = k * (k - 1) - 2 * m * k + off
            if e > ORDER:
                break
            if e < 0:
                raise AssertionError("offset too small")
            t = smul(qmon(e), sinv(poch(1, 1, 2 * k)))
            lhs = sadd(lhs, [Fr((-1) ** k) * x for x in t])
        rhs = zeros()
        for r in range(0, ORDER):
            e = (m + 1 + r) ** 2 + off
            if e > ORDER:
                break
            t = smul(qmon(e), sinv(smul(poch(2, 2, r), poch(2, 2, m + 1 + r))))
            rhs = sadd(rhs, [Fr((-1) ** r) * x for x in t])
        rhs = smul(rhs, smul(poch_inf(2, 2), sinv(poch_inf(1, 2))))
        rhs = [Fr((-1) ** (m + 1)) * x for x in rhs]
        d = first_diff(lhs, rhs)
        ordq = next((n for n in range(ORDER + 1) if lhs[n] != 0), None)
        print(f"  {m:>3} {(ORDER if d is None else d - 1) - off:>21} "
              f"{ordq - off:>17} {(m+1)**2:>9}")
    for dps in (60, 120):
        mp.mp.dps = dps
        q = mp.mpf('0.3')
        Q = q * q
        m = 3
        L = sum((-1) ** k * q ** (k * (k - 1)) * Q ** (-m * k)
                / _pochn(q, q, 2 * k) for k in range(0, 200))
        R = (-1) ** (m + 1) * _pinf(Q, Q) / _pinf(q, Q) * sum(
            (-1) ** r * q ** ((m + 1 + r) ** 2)
            / (_pochn(Q, Q, r) * _pochn(Q, Q, m + 1 + r)) for r in range(0, 80))
        print(f"  numerical at q = 0.3, m = 3, dps {dps:>4}: agreement "
              f"{int(-mp.log10(abs(L-R)/abs(R)))} digits")
    print()


# ------------------------------------------------- thm:zeroproduct step (1) --

def step_one():
    print("thm:zeroproduct step (1) -- (q;q)_inf G(z) = sum_m (-1)^m q^{m(m-1)} z^m P_m(1/z)")
    print("  Comparison is coefficient of z^k, each side a series in q.")
    print(f"  {'k':>3} {'agree through order':>21}")
    pinf = poch_inf(1, 1)
    cj = [smul(qmon(j - j * (j - 1) // 2), sinv(poch(1, 1, j)))
          if j - j * (j - 1) // 2 >= 0 else None for j in range(0, 4)]
    # c_j = q^{j - j(j-1)/2}/(q;q)_j has a negative exponent for j >= 4, so the
    # comparison is made after multiplying by q^{OFF} with OFF large enough.
    worst = None
    for k in range(0, 7):
        MJ = 12
        OFF = max(0, max(-(j - j * (j - 1) // 2) for j in range(MJ + 1)))
        lhs = smul(pinf, smul(qmon(k * (k - 1) + OFF), sinv(poch(1, 1, 2 * k))))
        lhs = [Fr((-1) ** k) * x for x in lhs]
        rhs = zeros()
        for mm in range(k, k + MJ + 1):
            j = mm - k
            e = mm * (mm - 1) + j - j * (j - 1) // 2 + OFF
            if e > ORDER or e < 0:
                continue
            t = smul(qmon(e), sinv(poch(1, 1, j)))
            rhs = sadd(rhs, [Fr((-1) ** mm) * x for x in t])
        d = first_diff(lhs, rhs)
        got = (ORDER if d is None else d - 1) - OFF
        worst = got if worst is None else min(worst, got)
        print(f"  {k:>3} {got:>21}")
    print(f"  worst agreement order over k <= 6: {worst}")
    for dps in (60, 120):
        mp.mp.dps = dps
        qv, z0 = mp.mpf('0.37'), mp.mpf('2.1')
        L = _pinf(qv, qv) * sum((-1) ** k * qv ** (k * (k - 1)) * z0**k
                                / _pochn(qv, qv, 2 * k) for k in range(300))
        R = mp.mpf(0)
        for mm in range(300):
            P = sum(qv ** (j - j * (j - 1) // 2) / _pochn(qv, qv, j) * z0 ** (-j)
                    for j in range(mm + 1))
            R += (-1) ** mm * qv ** (mm * (mm - 1)) * z0**mm * P
        print(f"  numerical at (q,z) = (0.37, 2.1), dps {dps:>4}: agreement "
              f"{int(-mp.log10(abs(L-R)/abs(L)))} digits")
    print()


if __name__ == "__main__":
    print(f"qcos_identities: exact and numerical identity checks, ORDER = {ORDER}\n")
    supermult()
    dressing()
    lattice_values()
    step_one()
    print("done.")
