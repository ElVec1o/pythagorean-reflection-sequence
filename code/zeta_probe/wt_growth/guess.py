#!/usr/bin/env python3
"""Exclusion / guessing tests for a finite integer sequence a_0..a_{N-1}.
Pure modular linear algebra (no enumeration). Full rank mod a prime P implies
full rank over Q, so every 'EXCLUDED' verdict is a proof about the N given terms.
A 'FIT' is only a candidate (kernel exists; must be checked out of sample).

usage: guess.py file [col]   (file: lines 'd u_d ...', '#' comments)
"""
import sys
P = (1 << 61) - 1

def rank_mod(rows, ncols):
    M = [[x % P for x in r] for r in rows]
    rk = 0
    for c in range(ncols):
        piv = None
        for i in range(rk, len(M)):
            if M[i][c]:
                piv = i; break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], P - 2, P)
        M[rk] = [x * inv % P for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]
                M[i] = [(x - f * y) % P for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk

def polymul_trunc(a, b, N):
    out = [0] * N
    for i, x in enumerate(a[:N]):
        if x:
            for j, y in enumerate(b[:N - i]):
                out[i + j] = (out[i + j] + x * y) % P
    return out

def rational_excluded(a, num, den):
    N = len(a)
    rows = []
    for n in range(num + 1, N):
        rows.append([a[n - j] if n - j >= 0 else 0 for j in range(den + 1)])
    if len(rows) < den + 1:
        return None
    return rank_mod(rows, den + 1) == den + 1

def algebraic_excluded(a, k, m):
    """sum_{i=0..k} P_i(x) f^i = 0, deg P_i <= m, checked on x^0..x^{N-1}."""
    N = len(a)
    powers = [[1] + [0] * (N - 1)]
    for i in range(1, k + 1):
        powers.append(polymul_trunc(powers[-1], a, N))
    ncols = (k + 1) * (m + 1)
    if N < ncols + 2:
        return None
    rows = []
    for n in range(N):
        row = []
        for i in range(k + 1):
            for s in range(m + 1):
                row.append(powers[i][n - s] if n - s >= 0 else 0)
        rows.append(row)
    return rank_mod(rows, ncols) == ncols

def dfinite_excluded(a, r, m):
    """P-recurrence sum_{i=0..r} Q_i(n) a_{n-i} = 0, deg Q_i <= m, for n >= r."""
    N = len(a)
    ncols = (r + 1) * (m + 1)
    rows = []
    for n in range(r, N):
        row = []
        for i in range(r + 1):
            for s in range(m + 1):
                row.append(pow(n, s, P) * a[n - i])
        rows.append(row)
    if len(rows) < ncols + 2:
        return None
    return rank_mod(rows, ncols) == ncols

def load(fn, col=1):
    a = []
    for line in open(fn):
        if line.startswith('#') or not line.strip():
            continue
        t = line.split()
        if len(t) == 1:
            a.append(int(t[0]))
        else:
            a.append(int(t[col]))
    return a

if __name__ == "__main__":
    a = load(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    N = len(a)
    print(f"N={N} terms")
    dmax = -1
    for d in range(0, N):
        r = rational_excluded(a, d, d)
        if r is None: break
        if r: dmax = d
        else:
            print(f"  rational type ({d},{d}) NOT excluded (kernel exists)"); break
    print(f"  rational: every type (d,d) with d <= {dmax} EXCLUDED")
    best = []
    for k in range(1, 7):
        mm = -1
        for m in range(0, 60):
            r = algebraic_excluded(a, k, m)
            if r is None: break
            if r: mm = m
            else: break
        best.append((k, mm))
    print("  algebraic: (deg_f, max excluded deg_x):", best)
    best = []
    for rr in range(1, 12):
        mm = -1
        for m in range(0, 60):
            r = dfinite_excluded(a, rr, m)
            if r is None: break
            if r: mm = m
            else: break
        best.append((rr, mm))
    print("  P-recurrence: (order, max excluded poly degree):", best)
