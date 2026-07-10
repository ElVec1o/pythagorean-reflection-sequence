#!/usr/bin/env python3
"""Route D / D2 wall: the travel x theta factorization of V = F(q,1), and why it does not close.

Extends theta_telescope.py. The catalytic block satisfies the first-order q-difference equation
    F(q,t) = E(t) + D(t) F(q, q^2 t),   D(t) = 2q(q-1)t/[(1-qt)(1-q^2 t)],
    E(t) = 2qt/(1-qt) * (1 + F(q,q)).
Telescoping factors (1+F(q,q)) out of every term, giving the EXACT product

        F(q,1) = A(q) * Theta(q),     A(q) := 1 + F(q,q),
        Theta(q) = sum_{k>=0} alpha_k(1) * 2 q^{2k+1}/(1-q^{2k+1}),
                   alpha_k(1) = [2q(q-1)]^k q^{k(k-1)} / (q;q)_{2k}    (theta q^{k(k-1)} factor).

Since V is a rational assembly of these blocks, V transcendental/Q(x) reduces to F(q,1)
transcendental/Q(q). The clean hope: F(q,1) = algebraic * transcendental. This script tests it.

FINDINGS (exact integer q-series to q^60, exact-arithmetic tests -- float SVD gives false positives):
  * factorization F(q,1) = A*Theta verified exactly.
  * RADII split: A carries the travel/beta_2 singularity (radius ~0.67, coeff ratio -> beta_2=1.4916);
    Theta is the radius-~1 theta factor.
  * BOTH A and Theta are TRANSCENDENTAL over Q(q) (no algebraic relation to degree (dy<=3,dx<=8)).
    => the "algebraic * transcendental" closure FAILS: A is not algebraic.
  * BOTH A and Theta are NON-HOLONOMIC (not D-finite).
    => the fallback "A holonomic (finitely many singularities) => A*Theta inherits Theta's natural
       boundary at |q|=1 => transcendental" ALSO fails: A has its OWN theta natural boundary, which
       can interfere with Theta's.
CONCLUSION (honest): the factorization reduces V-transcendence to the ALGEBRAIC INDEPENDENCE of the
  explicit travel factor A=1+F(q,q) and theta factor Theta -- both non-holonomic transcendentals. This
  is the SAME theta/connection-data wall of route-D/lem:cos, now pinned to a concrete statement. NOT closed.
"""
import sympy as sp
from fractions import Fraction as Fr

M = 60
def zeros(): return [0]*(M+1)
def shift(a, s):
    r = zeros()
    for i in range(M+1):
        if i+s <= M: r[i+s] = a[i]
    return r
def add(*xs):
    r = zeros()
    for a in xs:
        for i in range(M+1): r[i] += a[i]
    return r

# solve eq:sections (integer q-series)
F = {s: zeros() for s in range(1, M+1)}
for _ in range(M+3):
    nF = {}
    for s in range(1, M+1):
        t1 = zeros()
        if s <= M: t1[s] = 2
        S2 = zeros()
        for sp_ in range(s, M+1): S2 = add(S2, shift(F[sp_], sp_))
        S3 = zeros()
        for sp_ in range(1, s): S3 = add(S3, F[sp_])
        nF[s] = add(t1, shift([2*c for c in S2], s), shift([2*c for c in S3], 2*s))
    F = nF
Fq1 = add(*[F[s] for s in range(1, M+1)])
Fqq = add(*[shift(F[s], s) for s in range(1, M+1)])
A = Fqq[:]; A[0] += 1

def series_div(num, den):
    r = zeros(); d0 = Fr(den[0])
    for n in range(M+1):
        r[n] = (Fr(num[n]) - sum(Fr(den[k])*r[n-k] for k in range(1, n+1))) / d0
    return r
Theta = series_div([Fr(c) for c in Fq1], [Fr(c) for c in A])


def _fit_null(cols, M):
    need = len(cols); N = need + 6
    Am = sp.Matrix([[cols[c][row] for c in range(need)] for row in range(N+1)])
    for vec in Am.nullspace():
        if all(sum(vec[c]*cols[c][row] for c in range(need)) == 0 for row in range(M+1)):
            return True
    return False

def is_algebraic(a, dy, dx):
    a = [Fr(x) for x in a]
    pw = [[Fr(1)] + [Fr(0)]*M]
    for _ in range(dy):
        pw.append([sum(pw[-1][k]*a[n-k] for k in range(n+1)) for n in range(M+1)])
    cols = []
    for i in range(dy+1):
        for j in range(dx+1):
            cols.append([pw[i][n-j] if n-j >= 0 else Fr(0) for n in range(M+1)])
    return _fit_null(cols, M)

def is_holonomic(a, order, deg):
    a = [Fr(x) for x in a]
    def dq(s): return [(n+1)*s[n+1] if n+1 <= M else Fr(0) for n in range(M+1)]
    ders = [a[:]]
    for _ in range(order): ders.append(dq(ders[-1]))
    cols = []
    for r in range(order+1):
        for j in range(deg+1):
            cols.append([ders[r][n-j] if n-j >= 0 else Fr(0) for n in range(M+1)])
    return _fit_null(cols, M)


if __name__ == "__main__":
    prod = [sum(Fr(A[k])*Theta[n-k] for k in range(n+1)) for n in range(M+1)]
    print("F(q,1) == (1+F(q,q)) * Theta :", all(prod[n] == Fr(Fq1[n]) for n in range(M+1)))
    Th = [int(x) if x.denominator == 1 else x for x in Theta]
    print("\nalgebraic over Q(q)? (exact, to q^%d)" % M)
    for nm, s in [("A=1+F(q,q)", A), ("Theta", Th), ("F(q,1)", Fq1)]:
        alg = any(is_algebraic(s, dy, dx) for dy in range(1, 4) for dx in range(1, 9)
                  if (dy+1)*(dx+1)+8 < M)
        print(f"  {nm:12s}: {'ALGEBRAIC' if alg else 'transcendental (no relation)'}")
    print("\nholonomic (D-finite)?  (the closure discriminator)")
    for nm, s in [("A=1+F(q,q)", [int(x) for x in A]), ("Theta", Th), ("F(q,1)", Fq1)]:
        hol = any(is_holonomic(s, o, d) for o in range(1, 5) for d in range(1, 7)
                  if (o+1)*(d+1)+8 < M)
        print(f"  {nm:12s}: {'holonomic' if hol else 'NON-holonomic'}")
    print("\n=> both factors non-holonomic transcendental; closure needs algebraic independence of A,Theta. NOT closed.")
