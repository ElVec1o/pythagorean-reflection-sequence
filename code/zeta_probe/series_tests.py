#!/usr/bin/env python3
"""Exact complexity tests on the 43 known terms of A396406.

Rigorously decides (over Q, exact arithmetic):
  (1) no constant-coefficient linear recurrence of order <= 17  -> not rational
      with denominator degree <= 17;
  (2) no holonomic (polynomial-coefficient) recurrence with order+degree <= 8
      -> not low-complexity D-finite (in particular not low-degree algebraic);
  (3) beta_2 ~ 1.4996 by Aitken acceleration of consecutive ratios.

These are the hard facts behind Proposition (growth-series complexity) and
Conjecture (context-free growth) in the paper.
"""
from fractions import Fraction as F

U = [1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,
     17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,
     1697179,2554961,3848384,5777651,8679441,13031206,19574659,29338781,
     43997388,65932461,98849591,147969934]
N = len(U)


def find_linear(u, r):
    M = [[F(u[r + e - 1 - i]) for i in range(r)] + [F(u[r + e])] for e in range(r)]
    rk = 0
    for col in range(r):
        piv = next((i for i in range(rk, r) if M[i][col] != 0), None)
        if piv is None:
            return None
        M[rk], M[piv] = M[piv], M[rk]
        pv = M[rk][col]
        M[rk] = [x / pv for x in M[rk]]
        for i in range(r):
            if i != rk and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        rk += 1
    c = [M[i][r] for i in range(r)]
    if all(sum(c[i] * u[n - 1 - i] for i in range(r)) == u[n] for n in range(r, N)):
        return c
    return None


def nullspace(rows):
    M = [r[:] for r in rows]
    nr, nc = len(M), len(M[0])
    piv = []
    r = 0
    for c in range(nc):
        p = next((i for i in range(r, nr) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(nc) if c not in piv]
    out = []
    for fc in free:
        v = [F(0)] * nc
        v[fc] = F(1)
        for ri, pc in enumerate(piv):
            v[pc] = -M[ri][fc]
        out.append(v)
    return out


def find_holonomic(u, r, d):
    eqs = []
    for n in range(r, N):
        row = []
        for i in range(r + 1):
            for e in range(d + 1):
                row.append(F(u[n - i]) * F(n) ** e)
        eqs.append(row)
    if len(eqs) < (r + 1) * (d + 1):
        return None
    for v in nullspace(eqs):
        ok = all(
            sum(sum(v[i * (d + 1) + e] * F(n) ** e for e in range(d + 1)) * u[n - i]
                for i in range(r + 1)) == 0
            for n in range(r, N)
        )
        if ok and any(v[e] != 0 for e in range(d + 1)):
            return v
    return None


def aitken(s):
    return [(s[i + 2] * s[i] - s[i + 1] ** 2) / (s[i + 2] - 2 * s[i + 1] + s[i])
            for i in range(len(s) - 2) if (s[i + 2] - 2 * s[i + 1] + s[i]) != 0]


if __name__ == "__main__":
    print(f"terms: {N}")
    hit = next((r for r in range(1, 18) if find_linear(U, r)), None)
    print("linear recurrence order <= 17:", "ORDER %d" % hit if hit else "NONE")
    hh = next(((r, d) for tot in range(2, 9) for r in range(1, tot)
               for d in [tot - r] if find_holonomic(U, r, d)), None)
    print("holonomic order+deg <= 8:", hh if hh else "NONE")
    rat = [U[n + 1] / U[n] for n in range(N - 1)]
    a2 = aitken(aitken(rat))
    print(f"beta_2 ~ {float(a2[-1]):.6f}")
