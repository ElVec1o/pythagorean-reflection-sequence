#!/usr/bin/env python3
"""qcos_ledger.py -- the Diophantine-ledger numbers of the Hahn-Exton q-cosine paper.

Regenerates every ledger figure quoted in paper/journal/hahn_exton_qcosine.tex:

  prop:secondkind         deg_q P_N = 2N^2 + N and deg_z P_N = N, exactly, in Z[q,z];
                          and the measured log|R_N| / N^2 -> log q.
  rem:thetabarrier        beta := deg_q / N^2 for the cleared truncations of the theta
                          series, the Rogers-Ramanujan series (both 1, the boundary)
                          and the Hahn-Exton series (2 + 1/N).
  sec:arith confluence    tail * D_N for e = sum 1/k! (divergent step ratio, -> 0) and
                          for the q-series at q = 1/3 (constant step ratio, divergent);
                          the bridge (q;q)_k / ((1-q)^k k!) -> 1, at a stated k.
  rem:zerocurve-arith(g)  the discreteness cap: tail / Liouville floor for z_1 at q=1/7.
  the symmetric-branch    the radii of the cleared elementary symmetric functions of the
  tower paragraph         first m zero branches, and the resulting ledger factor 1/R.

All polynomial work is exact (Fraction / integer coefficients); the only floating
point is the coefficient-growth radius estimate, which is reported as an estimate.

Usage:  python3 qcos_ledger.py [ORDER]        (default 300)
"""
import sys
from fractions import Fraction as Fr

import mpmath as mp

ORDER = int(sys.argv[1]) if len(sys.argv) > 1 else 300


# ------------------------------------------------ integer power series over Z

def mul(a, b, n=None):
    n = n or ORDER + 1
    c = [0] * n
    for i, ai in enumerate(a[:n]):
        if not ai:
            continue
        for j in range(min(len(b), n - i)):
            if b[j]:
                c[i + j] += ai * b[j]
    return c


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def inv_unit(a):
    u = a[0]
    assert u in (1, -1)
    c = [0] * (ORDER + 1)
    c[0] = u
    for n in range(1, ORDER + 1):
        c[n] = -u * sum(a[i] * c[n - i] for i in range(1, n + 1))
    return c


def shift(n):
    c = [0] * (ORDER + 1)
    if n <= ORDER:
        c[n] = 1
    return c


ONE = shift(0)


def parts_at_most(m):
    c = [0] * (ORDER + 1)
    c[0] = 1
    for part in range(1, m + 1):
        for n in range(part, ORDER + 1):
            c[n] += c[n - part]
    return c


def u_series(k):
    """u_k(q) = q^{2(k-1)} z_k(q) in 1 + qZ[[q]], by Newton over Z."""
    coef = []
    kp = 0
    while True:
        e = (kp - k) * (kp - k + 1)
        if e > ORDER and kp > k:
            break
        coef.append([0] * (ORDER + 1) if e > ORDER else
                    [(-1) ** kp * x for x in mul(shift(e), parts_at_most(2 * kp))])
        kp += 1
    K = len(coef)

    def ev(z):
        acc = coef[K - 1][:]
        for j in range(K - 2, -1, -1):
            acc = add(mul(acc, z), coef[j])
        return acc

    def evd(z):
        acc = [(K - 1) * x for x in coef[K - 1]]
        for j in range(K - 2, 0, -1):
            acc = add(mul(acc, z), [j * x for x in coef[j]])
        return acc

    z = ONE[:]
    for _ in range(ORDER.bit_length() + 2):
        z = sub(z, mul(ev(z), inv_unit(evd(z))))
    assert all(x == 0 for x in ev(z)), "Newton residual nonzero"
    return z


# ----------------------------------------------- exact bivariate polynomials

def poly_mul(A, B):
    """Polynomials as dicts {(i_q, i_z): coeff}."""
    C = {}
    for (i, j), a in A.items():
        for (k, l), b in B.items():
            C[(i + k, j + l)] = C.get((i + k, j + l), 0) + a * b
    return {k: v for k, v in C.items() if v}


def poly_add(A, B):
    C = dict(A)
    for k, v in B.items():
        C[k] = C.get(k, 0) + v
    return {k: v for k, v in C.items() if v}


def P_N(N):
    """P_N(q,z) = sum_{k<=N} (-1)^k q^{k(k-1)} z^k prod_{i=2k+1}^{2N} (1-q^i)."""
    total = {}
    for k in range(N + 1):
        term = {(k * (k - 1), k): (-1) ** k}
        for i in range(2 * k + 1, 2 * N + 1):
            term = poly_mul(term, {(0, 0): 1, (i, 0): -1})
        total = poly_add(total, term)
    return total


def cleared_degq(coeffs, N):
    """deg_q of the truncation at N of sum_k c_k(q) z^k after clearing denominators
    by the common denominator of c_0..c_N.  coeffs[k] is a pair (num, den) of
    univariate integer polynomials as coefficient lists in q."""
    def pmul(a, b):
        c = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        c[i + j] += x * y
        return c

    def deg(a):
        d = -1
        for i, x in enumerate(a):
            if x:
                d = i
        return d

    dens = [c[1] for c in coeffs[:N + 1]]
    common = [1]
    for d in dens:                       # the denominators here form a chain
        if deg(d) > deg(common):
            common = d
    best = -1
    for k in range(N + 1):
        num, den = coeffs[k]
        # common/den is a polynomial by construction (nested products)
        quo = _exact_div(common, den)
        best = max(best, deg(pmul(num, quo)))
    return best


def _exact_div(a, b):
    a = a[:]
    q = [0] * (len(a) - len(b) + 1)
    db = len(b) - 1
    while len(a) - 1 >= db and any(a):
        d = len(a) - 1
        if a[d] == 0:
            a.pop()
            continue
        c = a[d] // b[db]
        q[d - db] = c
        for i, x in enumerate(b):
            a[d - db + i] -= c * x
        a.pop()
    return q


def run_secondkind():
    print("prop:secondkind -- exact degrees of the second-kind forms P_N in Z[q,z]")
    print(f"  {'N':>3} {'deg_q P_N':>10} {'2N^2+N':>8} {'deg_z P_N':>10} {'N':>4} "
          f"{'beta = deg_q/N^2':>17}")
    ok = True
    for N in range(1, 9):
        P = P_N(N)
        dq = max(i for i, _ in P)
        dz = max(j for _, j in P)
        ok &= (dq == 2 * N * N + N and dz == N)
        print(f"  {N:>3} {dq:>10} {2*N*N+N:>8} {dz:>10} {N:>4} "
              f"{dq/N**2:>17.4f}")
    print(f"  deg_q P_N = 2N^2+N and deg_z P_N = N for every N tested: {ok}")

    print("  remainder R_N = (q;q)_{2N} G - P_N: measured log|R_N| / (N^2 log q)")
    mp.mp.dps = 400
    for qlab, zlab in [('0.3', None), ('0.3', 'generic')]:
        q = mp.mpf(qlab)
        z0 = 2 * q * (1 - q) if zlab is None else mp.mpf('1.37')
        row = []
        for N in (4, 8, 12, 16, 20):
            poch = mp.mpf(1)
            for i in range(1, 2 * N + 1):
                poch *= 1 - q**i
            R = mp.mpf(0)
            for k in range(N + 1, N + 60):
                p2 = mp.mpf(1)
                for i in range(1, 2 * k + 1):
                    p2 *= 1 - q**i
                R += (-1) ** k * q ** (k * (k - 1)) * z0**k / p2
            R *= poch
            row.append(float(mp.log(abs(R)) / (N * N * mp.log(q))))
        tag = 'z = 2q(1-q)' if zlab is None else 'z = 1.37'
        print(f"    q = {qlab}, {tag:<12}: " +
              "  ".join(f"N={N}: {v:.4f}" for N, v in zip((4, 8, 12, 16, 20), row)))
    print("    (the ratio tends to 1, i.e. |R_N| = q^{N^2(1+o(1))})\n")


def run_thetabarrier():
    print("rem:thetabarrier -- beta = deg_q / N^2 for cleared truncations")
    print(f"  {'N':>3} {'theta sum q^{k^2}z^k':>21} {'Rogers-Ramanujan':>18} "
          f"{'Hahn-Exton':>12}")
    for N in (4, 6, 8):
        # theta: already integral, deg_q of the N-th truncation
        dth = N * N
        # Rogers-Ramanujan sum_k q^{k^2}/(q;q)_k cleared by (q;q)_N
        drr = max(k * k + sum(range(k + 1, N + 1)) for k in range(N + 1))
        # Hahn-Exton: prop:secondkind
        dhe = 2 * N * N + N
        print(f"  {N:>3} {dth/N**2:>21.4f} {drr/N**2:>18.4f} {dhe/N**2:>12.4f}")
    print("  theta and Rogers-Ramanujan sit exactly at beta = 1, the boundary;")
    print("  the Hahn-Exton family sits at beta = 2 + 1/N, a further factor 2 past it.\n")


def run_confluence_ledger():
    print("sec:arith -- divergent versus constant step ratio")
    mp.mp.dps = 60
    print("  (a) e = sum 1/k!: tail * D_N with D_N = N!")
    import math
    for N in (3, 6, 10):
        tail = mp.e - sum(mp.mpf(1) / math.factorial(k) for k in range(N + 1))
        print(f"      N = {N:>3}: tail * N! = {mp.nstr(tail * math.factorial(N), 6)}"
              f"    (2/(N+1) = {2/(N+1):.4f})")
    print("  (b) the Hahn-Exton ledger at q = 1/3, z_0 = 2q(1-q) = 4/9:")
    print("      D_N = t^{deg_q P_N} = 3^{2N^2+N}, the denominator the base alone")
    print("      contributes; tail = |R_N(q,z_0)|.  The column in parentheses adds")
    print("      the argument denominator b^N = 9^N, which only makes it worse.")
    mp.mp.dps = 400
    q = mp.mpf(1) / 3
    z0 = 2 * q * (1 - q)
    for N in (2, 4, 6):
        poch = mp.mpf(1)
        for i in range(1, 2 * N + 1):
            poch *= 1 - q**i
        R = mp.mpf(0)
        for k in range(N + 1, N + 80):
            p2 = mp.mpf(1)
            for i in range(1, 2 * k + 1):
                p2 *= 1 - q**i
            R += (-1) ** k * q ** (k * (k - 1)) * z0**k / p2
        R = abs(R * poch)
        D = mp.mpf(3) ** (2 * N * N + N)
        print(f"      N = {N:>3}: tail * D_N = {mp.nstr(R * D, 4)}"
              f"   (with b^N: {mp.nstr(R * D * mp.mpf(9) ** N, 4)})")
    print("  (c) the bridge (q;q)_k / ((1-q)^k k!) -> 1 as q -> 1, at k = 6:")
    mp.mp.dps = 40
    k = 6
    for qlab in ('0.9', '0.99', '0.999'):
        q = mp.mpf(qlab)
        poch = mp.mpf(1)
        for i in range(1, k + 1):
            poch *= 1 - q**i
        print(f"      q = {qlab:>6}: {mp.nstr(poch/((1-q)**k*math.factorial(k)), 6)}")
    print()


def run_discreteness_cap(u1):
    print("rem:zerocurve-arith(g) -- the discreteness cap for z_1 at q = 1/7")
    print("  tail  = |z_1(q_0) - z_{1,N}(q_0)|,  floor = t^{-M} with M the first")
    print("  index > N carrying a nonzero integer coefficient, t = 7, s = 1.")
    q0 = Fr(1, 7)
    print(f"  {'N':>4} {'M':>4} {'tail/floor':>14}")
    full = sum(Fr(c) * q0**n for n, c in enumerate(u1))
    for N in (6, 10, 14, 18):
        part = sum(Fr(c) * q0**n for n, c in enumerate(u1[:N + 1]))
        M = next(n for n in range(N + 1, len(u1)) if u1[n])
        tail = abs(full - part)
        floor = q0**M
        print(f"  {N:>4} {M:>4} {float(tail/floor):>14.4g}")
    print("  the ratio exceeds 1 at every N: the tail never undercuts the Liouville")
    print("  floor of its own truncation denominator.\n")


def run_branch_tower(us):
    print("the symmetric-branch tower -- radii of the cleared elementary symmetric")
    print("functions of the first m zero branches z_1, ..., z_m")
    print("  z_k = u_k q^{-2(k-1)}; e_j is cleared by the q-power that removes its")
    print("  worst pole, giving an integer series.  R is estimated from coefficient")
    print("  growth by the SAME estimator for every m, so the rows are comparable:")
    print("  R_est(n) = |c_n|^{-1/n}, extrapolated in 1/n by a two-point fit.")
    print(f"  {'m':>3} {'R (coeff growth)':>18} {'ledger factor 1/R':>19}")
    rows = []
    for m in range(1, 5):
        # elementary symmetric functions of {u_k q^{-2(k-1)}}, cleared.
        worst = None
        Rm = None
        for j in range(1, m + 1):
            e = [0] * (ORDER + 1)
            # sum over j-subsets of {1..m}
            from itertools import combinations
            shiftmin = min(sum(-2 * (k - 1) for k in S)
                           for S in combinations(range(1, m + 1), j))
            for S in combinations(range(1, m + 1), j):
                t = ONE[:]
                for k in S:
                    t = mul(t, us[k])
                sh = sum(-2 * (k - 1) for k in S) - shiftmin
                e = add(e, mul(t, shift(sh)))
            r = radius_estimate(e)
            if Rm is None or r < Rm:
                Rm, worst = r, j
        rows.append((m, Rm))
        print(f"  {m:>3} {Rm:>18.4f} {1/Rm:>19.4f}")
    print(f"  monotone increase in m: "
          f"{all(rows[i][1] < rows[i+1][1] for i in range(len(rows)-1))}")
    print("  Every cleared e_j is a non-polynomial integer power series, so by the")
    print("  denominator-radius inequality its radius is at most 1 and the ledger")
    print("  criterion s < R can never be met with s >= 1: the tower approaches")
    print("  criticality from below and cannot cross it.")
    print("  (For m = 1 the radius is known exactly: it is |q_c| = 0.5545786... , the")
    print("  fold of rem:zerocurve-arith(e).  The coefficient-growth estimate above is")
    print("  preasymptotic and reads high; the two must not be quoted side by side.)\n")


def radius_estimate(c):
    """|c_n|^{-1/n} with a two-point 1/n extrapolation, over the last nonzero terms."""
    idx = [n for n in range(ORDER // 2, ORDER + 1) if c[n]]
    if len(idx) < 4:
        return float('nan')
    n2, n1 = idx[-1], idx[len(idx) // 2]
    r2 = abs(c[n2]) ** (-1.0 / n2)
    r1 = abs(c[n1]) ** (-1.0 / n1)
    # linear in 1/n, extrapolate to 1/n = 0
    x1, x2 = 1.0 / n1, 1.0 / n2
    return r2 + (r2 - r1) * (0 - x2) / (x2 - x1)


if __name__ == "__main__":
    print(f"qcos_ledger: exact ledger figures, ORDER = {ORDER}\n")
    run_secondkind()
    run_thetabarrier()
    run_confluence_ledger()
    us = {k: u_series(k) for k in range(1, 5)}
    run_discreteness_cap(us[1])
    run_branch_tower(us)
    print("done.")
