#!/usr/bin/env python3
"""Post-processing for zeta_toy_growth (small arithmetic only, no enumeration).

1. Z wr Z growth series in {a, t} from the length formula
     l(n, k) = ||n||_1 + 2(R - L) - |k|,  [L, R] = hull(supp n u {0, k}),
   summed exactly as a truncated power series; then fitted/factored with sympy.
2. First deviation n_toy of each toy sequence from Z wr Z, and the deficits.
3. Calibration: BS(1,2) (lin_c1e2.txt) is rational (Collins-Edjvet-Gill), but a blind
   fit needs total degree ~27; after dividing out the known dominant factor
   1 - z - 2z^3 the fit is found and factored.
4. guess.py exclusions for every sequence.
usage: python3 analysis.py      (run inside runs/)
"""
import sys
sys.path.insert(0, '../../wt_growth')
import guess
import sympy as sp

N = 30
def mul(p, q):
    r = [0] * N
    for i, x in enumerate(p):
        if x:
            for j, y in enumerate(q[:N - i]):
                r[i + j] += x * y
    return r

def zwrz():
    A = [1] + [2] * (N - 1)   # sum_m z^|m|
    B = [0] + [2] * (N - 1)   # m != 0
    powA = [[1] + [0] * (N - 1)]
    for _ in range(N + 2):
        powA.append(mul(powA[-1], A))
    G = [0] * N
    for L in range(-N, 1):
        for R in range(0, N + 1):
            for k in range(L, R + 1):
                e = 2 * (R - L) - abs(k)
                if e >= N:
                    continue
                if L == R:
                    w = A[:]
                else:
                    wl = A if L in (0, k) else B
                    wr = A if R in (0, k) else B
                    w = mul(mul(wl, wr), powA[R - L - 1])
                for n in range(N - e):
                    G[n + e] += w[n]
    return G

def fit(a, num, D):
    z = sp.symbols('z')
    M = sp.Matrix([[a[n - j] if n - j >= 0 else 0 for j in range(D + 1)] for n in range(num + 1, len(a))])
    ns = M.nullspace()
    if len(ns) != 1:
        return None
    q = ns[0] / ns[0][0]
    Q = sp.expand(sum(q[j] * z**j for j in range(D + 1)))
    Q = sp.expand(Q * sp.lcm([sp.fraction(x)[1] for x in q]))
    P = sp.expand(sum(a[n] * z**n for n in range(len(a))) * Q)
    P = sum(P.coeff(z, n) * z**n for n in range(num + 1))
    return sp.factor(sp.cancel(P / Q))

if __name__ == "__main__":
    G = zwrz()
    print("Z wr Z spheres:", G)
    print("Z wr Z series:", fit(G, 8, 8))
    for f in ['seq_c5e6', 'seq_c2e1', 'lin_c1e2', 'lin_c1e3', 'lin_c2e3']:
        a = guess.load(f + '.txt', 1)
        d = next((n for n in range(min(len(a), N)) if a[n] != G[n]), None)
        print(f, "first deviation from Z wr Z at n =", d, "deficits", [G[n] - a[n] for n in range(d, min(len(a), N, d + 6))])
    a = guess.load('lin_c1e2.txt', 1)
    b = [sum(p * a[n - j] for j, p in enumerate([1, -1, 0, -2]) if n - j >= 0) for n in range(len(a))]
    print("BS(1,2) * (1 - z - 2z^3) =", fit(b, 14, 10), " (so BS(1,2) = this / (1 - z - 2z^3))")
