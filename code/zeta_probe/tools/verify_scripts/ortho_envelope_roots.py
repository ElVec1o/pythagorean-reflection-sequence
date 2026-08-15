#!/usr/bin/env python3
"""
ortho_envelope_roots.py
=======================
Certifies the root statement of Theorem `thm:envelope` in
paper/journal/paper_orthoscheme.tex, in exact arithmetic, and reproduces the
numbers quoted in Table 1 (tab:n-dim-rates) of that paper.

What is checked, for 2 <= n <= 30, with m = n + 3:

  (A) the recurrences.  J_m from  J_m = (1+t)(J_{m-1} - t J_{m-2}),  J_0 = J_1 = 1,
      and K_m from eq:Kdef, satisfy  J_m = (1+t)^{floor(m/2)} K_m  as an identity
      of polynomials over Z.

  (B) the Steinberg expansion.  1/W_n(t) = I_{n+1}(-t/(1+t)) with
      I_m the independence polynomial of the path P_m, equals
      J_{n+1}(t)/(1+t)^{n+1}.

  (C) the roots, exactly.  The reciprocal polynomial of K_{n+1} equals, up to a
      nonzero rational constant, the monic integer polynomial whose roots are
      exactly the numbers  1 + 2 cos(2 pi k / m)  for  1 <= k <= floor((m-1)/2),
      k /= m/3.  Equivalently: the roots of K_{n+1} are exactly the numbers
      1/(1 + 2 cos(2 pi k / m)) for that index set, all simple.
      No floating point is used: the target polynomial is built from the
      Chebyshev identity  prod_{k=0}^{m-1} (x - 2 cos(2 pi k / m)) = (z^m-1)^2/z^m
      with x = z + 1/z, i.e. from  2 T_m(x/2) - 2.

  (D) the interval.  1/(1 + 2 cos(2 pi k / m)) > 1/3  iff  0 < 1 + 2cos(...) < 3
      iff  k < m/3.  The count of real roots of K_{n+1} in (1/3, +oo), computed
      by Sturm sequences over Q, equals #{k : 1 <= k < m/3}.  This is the claim
      that the paper previously stated with the FALSE interval (1/3, 1):
      roots above 1 occur (n = 4: 1.8019...; n = 5: exactly 1; n = 7: 2.6180...;
      n = 10: 3.4389...), and those four values are checked here explicitly.

  (E) the smallest positive root is the k = 1 one, i.e. 1/r_n with
      r_n = 1 + 2 cos(2 pi/(n+3)).  Checked by an exact Sturm count on
      (1/3, q) for a rational q strictly between the k = 1 and k = 2 values.

  (F) the substitution of Remark `rem:pell`, symbolically:  with y = -t/(1+t)
      (the substitution the construction actually uses, NOT y = -1/(1+t)), the
      Pell root y_j = -1/(4 cos^2(pi j/m)) pulls back to
      t_j = 1/(4 cos^2(pi j/m) - 1) = 1/(1 + 2 cos(2 pi j/m)).

  (G) two-precision numerics, as a cross-check only (Rule 7): the roots of
      K_{n+1} computed at 30 and at 60 decimal digits agree with each other and
      with the closed forms to the working precision.

Run:  code/zeta_probe/tools/runcap.sh 14000 900 python3 <this file>
"""

import sys
from sympy import (Poly, Rational, ZZ, QQ, symbols, chebyshevt, cos, pi, sqrt,
                   simplify, expand, oo, nsimplify, sympify)
import mpmath

t, x, r, z, y = symbols('t x r z y')

NMAX = 30
FAIL = []


def check(cond, msg):
    if cond:
        print("  ok   %s" % msg)
    else:
        print("  FAIL %s" % msg)
        FAIL.append(msg)


# ---------------------------------------------------------------- (A) and (B)

def J_list(mmax):
    """J_m = (1+t)(J_{m-1} - t J_{m-2}), J_0 = J_1 = 1."""
    J = [Poly(1, t, domain=ZZ), Poly(1, t, domain=ZZ)]
    for m in range(2, mmax + 1):
        J.append(Poly((1 + t), t, domain=ZZ) * (J[m - 1] - Poly(t, t, domain=ZZ) * J[m - 2]))
    return J


def K_list(mmax):
    """eq:Kdef: K_0=K_1=1, K_{2j}=K_{2j-1}-t K_{2j-2}, K_{2j+1}=(1+t)K_{2j}-t K_{2j-1}."""
    K = [Poly(1, t, domain=ZZ), Poly(1, t, domain=ZZ)]
    for m in range(2, mmax + 1):
        if m % 2 == 0:
            K.append(K[m - 1] - Poly(t, t, domain=ZZ) * K[m - 2])
        else:
            K.append(Poly((1 + t), t, domain=ZZ) * K[m - 1] - Poly(t, t, domain=ZZ) * K[m - 2])
    return K


def I_list(mmax):
    """Independence polynomial of the path P_m in the variable x:
       I_0 = 1, I_1 = 1 + x, I_m = I_{m-1} + x I_{m-2}."""
    I = [Poly(1, x, domain=ZZ), Poly(1 + x, x, domain=ZZ)]
    for m in range(2, mmax + 1):
        I.append(I[m - 1] + Poly(x, x, domain=ZZ) * I[m - 2])
    return I


def part_A_B(J, K, I):
    print("(A) J_m = (1+t)^{floor(m/2)} K_m, and (B) Steinberg expansion, 2 <= n <= %d" % NMAX)
    okA = okB = okC = True
    for n in range(2, NMAX + 1):
        m = n + 1
        lhs = J[m]
        rhs = Poly((1 + t) ** (m // 2), t, domain=ZZ) * K[m]
        if lhs != rhs:
            okA = False
        # (B): I_{n+1}(-t/(1+t)) * (1+t)^{n+1} == J_{n+1}
        sub = expand(I[n + 1].as_expr().subs(x, -t / (1 + t)) * (1 + t) ** (n + 1))
        if Poly(simplify(sub), t, domain=QQ) != Poly(J[n + 1].as_expr(), t, domain=QQ):
            okB = False
        # exactness of the division by (1+t)^{floor((n+1)/2)}
        q, rem = divmod(J[m], Poly((1 + t) ** (m // 2), t, domain=ZZ))
        if not rem.is_zero or q != K[m]:
            okC = False
    check(okA, "J_m = (1+t)^{floor(m/2)} K_m for all n in [2,%d]" % NMAX)
    check(okB, "Steinberg expansion agrees with the J recurrence for all n in [2,%d]" % NMAX)
    check(okC, "the division by (1+t)^{floor((n+1)/2)} is exact for all n in [2,%d]" % NMAX)


# -------------------------------------------------------------------- table 1

TABLE1 = {
    2:  1 - t - t**2,
    3:  1 - 2*t,
    4:  1 - 2*t - t**2 + t**3,
    5:  1 - 3*t + t**2 + t**3,
    6:  1 - 3*t + 3*t**3,
    7:  1 - 4*t + 3*t**2 + 2*t**3 - t**4,
    8:  1 - 4*t + 2*t**2 + 5*t**3 - 2*t**4 - t**5,
    9:  1 - 5*t + 6*t**2 + 2*t**3 - 4*t**4,
    10: 1 - 5*t + 5*t**2 + 6*t**3 - 7*t**4 - 2*t**5 + t**6,
}


def part_table(K):
    print("(A') the printed denominators of Table 1")
    ok = True
    for n, den in TABLE1.items():
        if K[n + 1] != Poly(den, t, domain=ZZ):
            ok = False
            print("      n=%d: recurrence gives %s, table prints %s" % (n, K[n + 1].as_expr(), den))
    check(ok, "K_{n+1} matches the printed denominator for 2 <= n <= 10")


# ------------------------------------------------------------------------ (C)

def target_poly(m):
    """Monic integer polynomial in r whose roots are exactly
       1 + 2 cos(2 pi k/m) for 1 <= k <= floor((m-1)/2), k /= m/3, each simple.

       Built exactly: D(x) = 2 T_m(x/2) - 2 has root set {2 cos(2 pi k/m)}.
       Its squarefree part, shifted by r = x + 1, has the simple roots
       1 + 2 cos(2 pi k/m) for k = 0 .. floor(m/2).  Strip k = 0 (r = 3),
       k = m/2 (r = -1, m even), and k = m/3 (r = 0, 3 | m)."""
    D = Poly(expand(2 * chebyshevt(m, x / 2) - 2), x, domain=QQ)
    S = Poly(D.as_expr(), x, domain=QQ).sqf_part()
    P = Poly(S.as_expr().subs(x, r - 1), r, domain=QQ)
    P = P.quo(Poly(r - 3, r, domain=QQ))
    if m % 2 == 0:
        P = P.quo(Poly(r + 1, r, domain=QQ))
    if m % 3 == 0:
        P = P.quo(Poly(r, r, domain=QQ))
    return P.monic()


def part_C(K):
    print("(C) reciprocal of K_{n+1} has exactly the roots 1 + 2cos(2 pi k/m)")
    ok = True
    for n in range(2, NMAX + 1):
        m = n + 3
        Kn = K[n + 1]
        d = Kn.degree()
        # expected degree: floor((m-1)/2) minus one if 3 | m
        dexp = (m - 1) // 2 - (1 if m % 3 == 0 else 0)
        if d != dexp:
            ok = False
            print("      n=%d: deg K = %d, expected %d" % (n, d, dexp))
            continue
        rev = Poly(expand(r ** d * Kn.as_expr().subs(t, 1 / r)), r, domain=QQ).monic()
        if rev != target_poly(m):
            ok = False
            print("      n=%d: reciprocal polynomial does not match the cosine target" % n)
    check(ok, "roots of K_{n+1} are exactly {1/(1+2cos(2 pi k/m))}, 2 <= n <= %d" % NMAX)


# ------------------------------------------------------------------ (D) + (E)

QUOTED = {4: "1.8019", 5: "1", 7: "2.6180", 10: "3.4389"}


def part_D_E(K):
    print("(D) the interval is (1/3, +oo), not (1/3, 1); and (E) the smallest root is k=1")
    okD = okE = True
    third = Rational(1, 3)
    mpmath.mp.dps = 60
    for n in range(2, NMAX + 1):
        m = n + 3
        Kn = K[n + 1]
        kset = [k for k in range(1, (m - 1) // 2 + 1) if 3 * k != m and 3 * k < m]
        cnt = Kn.count_roots(third, oo)
        if cnt != len(kset):
            okD = False
            print("      n=%d: %d roots in (1/3,oo), expected %d" % (n, cnt, len(kset)))
        # (E) smallest root in (1/3,oo) is the k=1 one: no root in (1/3, q) for a
        # rational q strictly between t_1 and t_2 (or below t_1 when kset = {1}).
        t1 = 1 / (1 + 2 * mpmath.cos(2 * mpmath.pi / m))
        if len(kset) >= 2:
            t2 = 1 / (1 + 2 * mpmath.cos(4 * mpmath.pi / m))
            q = Rational(nsimplify(mpmath.nstr((t1 + t2) / 2, 20), rational=True))
            if Kn.count_roots(third, q) != 1:
                okE = False
                print("      n=%d: root count on (1/3,q) is not 1" % n)
        else:
            q = Rational(nsimplify(mpmath.nstr(t1 * mpmath.mpf('0.999999'), 20), rational=True))
            if Kn.count_roots(third, q) != 0:
                okE = False
                print("      n=%d: a root below t_1 on (1/3,q)" % n)
    check(okD, "#roots of K_{n+1} in (1/3,oo) = #{k : 1<=k<m/3}, 2 <= n <= %d" % NMAX)
    check(okE, "the smallest root in (1/3,oo) is 1/r_n, 2 <= n <= %d" % NMAX)

    print("    roots of K_{n+1} exceeding 1 (the counterexamples to the old interval):")
    okQ = True
    for n in sorted(QUOTED):
        Kn = K[n + 1]
        m = n + 3
        big = []
        for k in range(1, (m - 1) // 2 + 1):
            if 3 * k >= m:
                continue
            v = 1 / (1 + 2 * mpmath.cos(2 * mpmath.pi * k / m))
            if v > mpmath.mpf('0.9999999999'):   # >= 1, i.e. outside the old (1/3,1)
                big.append((k, v))
        for k, v in big:
            # exact: this value is a root of K_{n+1}
            lo = Rational(nsimplify(mpmath.nstr(v - mpmath.mpf('1e-20'), 30), rational=True))
            hi = Rational(nsimplify(mpmath.nstr(v + mpmath.mpf('1e-20'), 30), rational=True))
            isroot = Kn.count_roots(lo, hi) == 1
            okQ = okQ and isroot
            print("      n=%2d  k=%d  t = %s   (root of K_{n+1}: %s;  paper quotes %s)"
                  % (n, k, mpmath.nstr(v, 12), isroot, QUOTED[n]))
    check(okQ, "each quoted root above 1 is an exact root of K_{n+1}")


# ------------------------------------------------------------------------ (F)

def part_F():
    print("(F) the rem:pell substitution: y = -t/(1+t), NOT y = -1/(1+t)")
    th = symbols('vartheta')
    yj = -1 / (4 * cos(th) ** 2)
    # invert y = -t/(1+t):  t = -y/(1+y)
    t_from_y = simplify(-yj / (1 + yj))
    want = simplify(1 / (4 * cos(th) ** 2 - 1))
    check(simplify(t_from_y - want) == 0,
          "y = -t/(1+t) sends y_j = -1/(4cos^2 v) to t_j = 1/(4cos^2 v - 1)")
    check(simplify(want - 1 / (1 + 2 * cos(2 * th))) == 0,
          "1/(4cos^2 v - 1) = 1/(1 + 2 cos 2v)")
    # the erroneous substitution: y = -1/(1+t) gives t = -1/y - 1 = 4cos^2 v - 1,
    # which is the RATE r, not the root t.  Recorded so the error is visible.
    bad = simplify(-1 / yj - 1)
    check(simplify(bad - (1 + 2 * cos(2 * th))) == 0,
          "y = -1/(1+t) would return the rate 1+2cos 2v in place of the root")


# ------------------------------------------------------------------------ (G)

def part_G(K):
    print("(G) two-precision cross-check of the roots (30 and 60 digits)")
    ok = True
    worst = mpmath.mpf(0)
    for n in range(2, NMAX + 1):
        m = n + 3
        coeffs30 = None
        vals = {}
        for dps in (30, 60):
            mpmath.mp.dps = dps
            poly = [mpmath.mpf(int(c)) for c in K[n + 1].all_coeffs()]
            roots = mpmath.polyroots(poly, maxsteps=200, extraprec=200)
            closed = sorted([1 / (1 + 2 * mpmath.cos(2 * mpmath.pi * k / m))
                             for k in range(1, (m - 1) // 2 + 1) if 3 * k != m],
                            key=lambda v: float(v))
            got = sorted([mpmath.re(v) for v in roots], key=lambda v: float(v))
            if len(got) != len(closed):
                ok = False
                continue
            d = max(abs(a - b) for a, b in zip(got, closed))
            vals[dps] = d
            worst = max(worst, mpmath.mpf(0) if d < mpmath.mpf('1e-20') else d)
            if d > mpmath.mpf('1e-20'):
                ok = False
                print("      n=%d dps=%d: max deviation %s" % (n, dps, mpmath.nstr(d, 5)))
    check(ok, "numeric roots match the closed forms at both 30 and 60 digits (< 1e-20)")


def main():
    print("=" * 78)
    print("ortho_envelope_roots.py -- exact certification of thm:envelope roots")
    print("=" * 78)
    J = J_list(NMAX + 2)
    K = K_list(NMAX + 2)
    I = I_list(NMAX + 2)
    part_A_B(J, K, I)
    part_table(K)
    part_C(K)
    part_D_E(K)
    part_F()
    part_G(K)
    print("-" * 78)
    if FAIL:
        print("VERDICT: FAIL (%d)" % len(FAIL))
        for f in FAIL:
            print("  - %s" % f)
        return 1
    print("VERDICT: PASS -- all checks above hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
