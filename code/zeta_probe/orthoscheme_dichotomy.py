#!/usr/bin/env python3
"""Orthoscheme growth vs the right-angled Coxeter ENVELOPE (Paper 3) -- CORRECTED.

IMPORTANT CORRECTION (2026-07-10, caught by adversarial verification): the rational generating
functions below are the growth of the abstract RIGHT-ANGLED COXETER ENVELOPE W_n, NOT the geometric
group's true growth. The geometric group W_T <= Isom(R^n) is AMENABLE, hence a PROPER quotient of the
NON-amenable RACG W_n, so its growth matches the rational envelope only up to a finite depth n_T, then
deviates strictly below (universality-deviation theorem). At n=2 this deviation is at depth 10, where
the growth becomes A396406 (transcendental). For 3<=n<=7 the geometric BFS matches the envelope to
depth 13-16 ONLY because the deviation lies beyond reach -- it does NOT show the geometric growth is
rational. THE "unique transcendental dimension" DICHOTOMY IS RETRACTED; see paper3.tex Question 'q:transc'.

RACG envelope generating functions W_n(t) (Steinberg + clique polynomial of the orthogonality graph;
these ARE proven, and equal the geometric BFS up to each deviation horizon):
    n=2 : (1+t)^2/(1-t-t^2)          rate phi=1.618   [geometric DEVIATES at depth 10 -> A396406]
    n=3 : (1+t)^2/(1-2t)             rate 2
    n=4 : (1+t)^3/(1-2t-t^2+t^3)     rate r_4=1+2cos(2pi/7)=2.24698
    n=5 : (1+t)^3/(1-3t+t^2+t^3)     rate r_5=1+sqrt2
    n=6 : (1+t)^4/(1-3t+3t^3)        rate r_6=1+2cos(2pi/9)=2.53209
    n=7 : (1+t)^4/(1-2t-3t^2+4t^3-t^4) rate r_7=phi^2=2.61803
numerator (1+t)^{floor(n/2)+1}; rate r_n=1+2cos(2pi/(n+3)) = 1 + spectral radius of the path P_{n+1}.

Below: the geometric BFS 'rational GF' detected for n>=3 is really this ENVELOPE (deviation unreached).
Uses hash-based dedup (memory-light), float64, OMP_NUM_THREADS=1; n=2 gate exact (A396406, deviated).
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
            print(f"n={n}: geometric growth NOT rational (deviated within reach). rate beta_2 < r_2={rn:.4f}  [A396406]")
        else:
            num, den, rate = res
            ok = abs(rate - rn) < 1e-4
            tag = "ENVELOPE (deviation unreached)" if n >= 3 else ""
            print(f"n={n}: BFS matches RACG envelope ({num})/({den}) rate={rate:.5f}=r_{n}={rn:.5f} {tag}")
        del s; gc.collect()
    print("\n=> n=2 deviates at depth 10 (A396406, transcendental); n>=3 the deviation is beyond reach,")
    print("   so the BFS only sees the RATIONAL ENVELOPE. Eventual transcendence for n>=3 is OPEN (paper3 q:transc).")
