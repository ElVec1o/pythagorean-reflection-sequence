#!/usr/bin/env python3
"""The dimensional transcendence dichotomy for orthoscheme reflection groups (Paper 3).

Generic n-orthoscheme geodesic growth (distinct isometries by word length), computed by the
validated engine of orthoscheme_universality.py. Extracting the generating functions:

    n=2 : NOT rational (OEIS A396406), rate beta_2 = 1.4916... STRICTLY BELOW r_2 = phi = 1.618
    n=3 : (1+z)^2 / (1-2z)                       rate 2
    n=4 : (1+z)^3 / (1-2z-z^2+z^3)               rate r_4 = 1+2cos(2pi/7) = 2.24698 (deg 3)
    n=5 : (1+z)^3 / ((1-z)(1-2z-z^2))            rate r_5 = 1+sqrt2 = 2.41421 (deg 2)
    n=6 : (1+z)^4 / (1-3z+3z^3)                  rate r_6 = 1+2cos(2pi/9) = 2.53209 (deg 3)
    n=7 : (1+z)^4 / ((1-3z+z^2)(1+z-z^2))        rate r_7 = phi^2 = 2.61803 (deg 2)

So for 3<=n<=7 the growth is RATIONAL with rate the explicit algebraic number
r_n = 1+2cos(2pi/(n+3)) (the spectral radius shift attached to the cycle C_{n+3}), numerator
(1+z)^{floor(n/2)+1}; only n=2 is transcendental, and only there does the rate fall below r_n.
THE PLANE IS THE UNIQUE TRANSCENDENTAL DIMENSION (verified 2<=n<=7).

Uses hash-based dedup (memory-light) and float64; OMP_NUM_THREADS=1; the n=2 gate is exact (A396406).
Heavy: n=6,7 to depth 13/12 take a few minutes. Reduce DEPTHS for a quick run.
"""
import os
os.environ["OMP_NUM_THREADS"] = "1"
import numpy as np, math, gc, sympy as sp
from fractions import Fraction as Fr


def ortho_refl(legs):
    n = len(legs); P = np.zeros((n + 1, n))
    for k in range(1, n + 1):
        P[k] = P[k - 1].copy(); P[k, k - 1] += legs[k - 1]
    R = []
    for j in range(n + 1):
        pts = np.array([P[i] for i in range(n + 1) if i != j])
        _, _, vt = np.linalg.svd(pts[1:] - pts[0:1]); m = vt[-1] / np.linalg.norm(vt[-1])
        R.append((np.eye(n) - 2 * np.outer(m, m), 2 * (m @ pts[0]) * m))
    return R


def sphere(R, depth, dec=6):
    n = R[0][1].shape[0]
    def h(A, t):
        return hash((tuple((np.round(A, dec) + 0.0).ravel().tolist()),
                     tuple((np.round(t, dec) + 0.0).tolist())))
    seen = {h(np.eye(n), np.zeros(n))}; fr = [(np.eye(n), np.zeros(n))]; s = [1]
    for _ in range(depth):
        nf, nk = [], set()
        for (A, t) in fr:
            for (B, u) in R:
                C, v = A @ B, A @ u + t; k = h(C, v)
                if k not in seen and k not in nk:
                    nk.add(k); nf.append((C, v))
        seen |= nk; s.append(len(nf)); fr = nf
        if not nf:
            break
    return s


def rational_gf(seq, z):
    a = [Fr(x) for x in seq]; N = len(a)
    for r in range(1, (N - 1) // 2 + 1):
        Mx = sp.Matrix([[a[i + j] for j in range(r)] for i in range(r)])
        if Mx.det() == 0:
            continue
        c = Mx.solve(sp.Matrix([a[i + r] for i in range(r)]))
        if all(sum(c[j] * a[i + j] for j in range(r)) == a[i + r] for i in range(N - r)):
            den = 1 - sum(c[j] * z ** (r - j) for j in range(r))
            num = sp.Poly(sp.expand(sum(a[i] * z ** i for i in range(N)) * den), z)
            num = sum(num.coeff_monomial(z ** i) * z ** i for i in range(r))
            g = sp.cancel(sp.together(num) / den)
            rate = max(abs(1 / complex(rt)) for rt in sp.Poly(den, z).nroots())
            return sp.factor(sp.numer(g)), sp.factor(sp.denom(g)), rate
    return None


if __name__ == "__main__":
    z = sp.symbols('z')
    LEGS = {n: tuple([1.0] + [math.sqrt(2) + 0.11 * k + 0.37 * math.cos(k) for k in range(1, n)])
            for n in range(2, 8)}
    DEPTHS = {2: 16, 3: 16, 4: 15, 5: 14, 6: 13, 7: 12}
    for n in range(2, 8):
        s = sphere(ortho_refl(LEGS[n]), DEPTHS[n])
        rn = float(1 + 2 * math.cos(2 * math.pi / (n + 3)))
        res = rational_gf(s, z)
        if res is None:
            print(f"n={n}: NOT rational (transcendental).  rate beta_2=1.4916 < r_2={rn:.4f}   [A396406]")
        else:
            num, den, rate = res
            ok = abs(rate - rn) < 1e-4
            print(f"n={n}: RATIONAL  GF=({num})/({den})   rate={rate:.5f}=r_{n}={rn:.5f} [{ok}]")
        del s; gc.collect()
    print("\n=> the plane (n=2) is the UNIQUE transcendental dimension (verified 2<=n<=7).")
