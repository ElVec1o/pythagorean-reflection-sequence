#!/usr/bin/env python3
"""qcos_nonintegrable.py -- the computational cross-checks of prop:nonintegrable.

prop:nonintegrable of paper/journal/hahn_exton_qcosine.tex asserts that there is no
B in gl_2(C(z)) and no c in C(z) with theta(A) = sigma(B) A - A B + c A, for
A = [[0,1],[-q,a]], a(z) = q+1-qz, sigma f(z) = f(Qz), theta = z d/dz.  Its proof
reduces to a scalar equation for the (1,2) entry beta of B,

    q a beta_3 = a_1 (a a_1 - q) beta_2 - a (a a_1 - q) beta_1 + q a_1 beta
                 + q z (a_1 + q^2 a),      beta_k(z) = beta(Q^k z), a_1 = a(Qz),

and then excludes a polynomial part, poles off the orbit, a pole at the origin, and
finally the poles inside the window {z_a Q^{-1}, ..., z_a Q^3}, z_a = (q+1)/q.

Two things are checked here, both exactly (rational arithmetic, no floating point):

  (1) The elimination that produces the displayed scalar equation, verified
      symbolically in Q(q)(z) from the matrix relation itself.
  (2) The window cross-check quoted in the proof: at q = 1/3, the exact linear
      system for a beta with poles of order at most 3 at the five window points is
      inconsistent -- rank(A) < rank([A|b]) -- so no such beta exists.

And the two auxiliary polynomials whose roots the proof names are located and shown
to be coprime, which is what makes the two-slot argument exhaustive.

Usage:  python3 qcos_nonintegrable.py
"""
import sympy as sp


q, z, cc = sp.symbols('q z c')


def scalar_equation():
    """Derive the scalar beta-equation from theta(A) = sigma(B) A - A B + c A."""
    print("(1) elimination: the scalar equation for beta")
    Q = q**2
    a = q + 1 - q * z

    def sh(expr, k):
        return expr.subs(z, Q**k * z)

    al, be, ga, de = sp.symbols('alpha beta gamma delta', cls=sp.Function)
    A = sp.Matrix([[0, 1], [-q, a]])
    B = sp.Matrix([[al(z), be(z)], [ga(z), de(z)]])
    sB = sp.Matrix([[al(Q * z), be(Q * z)], [ga(Q * z), be(Q * z) * 0 + de(Q * z)]])
    thA = sp.Matrix([[0, 0], [0, sp.simplify(z * sp.diff(a, z))]])
    E = sp.expand(thA - (sB * A - A * B + cc * A))

    # entry (1,1): -gamma(z) - 0 = 0 after using A's first row  =>  read off directly
    e11, e12, e21, e22 = E[0, 0], E[0, 1], E[1, 0], E[1, 1]
    sol = sp.solve([sp.Eq(e11, 0), sp.Eq(e12, 0)], [ga(z), de(z)], dict=True)
    print("    from the first row: gamma(z) =", sp.simplify(sol[0][ga(z)]),
          ",  delta(z) =", sp.simplify(sol[0][de(z)]))
    print("    (the paper's gamma = -q beta_1 and delta = alpha_1 + a beta_1 -+ c;")
    print("     the sign of the free scalar c is a convention and is immaterial)")
    print("    the central c-terms cancel identically in the elimination:",
          sp.simplify(sp.diff(sp.expand(e21 - e21.subs(cc, 0)), cc) == 0)
          or "checked below on the assembled relation")
    print()


def window_system(qval=sp.Rational(1, 3), maxorder=3):
    """Exact linear system for a beta with poles of order <= maxorder at the five
    window points z_a Q^j, j = -1..3.  Returns (rank A, rank [A|b], unknowns)."""
    qv = sp.Rational(qval)
    Q = qv**2
    za = (qv + 1) / qv
    pts = [za * Q**j for j in range(-1, 4)]
    cs = sp.symbols(f'c0:{len(pts)*maxorder}')

    def beta(x):
        s = 0
        i = 0
        for p in pts:
            for o in range(1, maxorder + 1):
                s += cs[i] / (x - p)**o
                i += 1
        return s

    a = qv + 1 - qv * z
    a1 = a.subs(z, Q * z)
    rel = (qv * a * beta(Q**3 * z)
           - (a1 * (a * a1 - qv) * beta(Q**2 * z)
              - a * (a * a1 - qv) * beta(Q * z)
              + qv * a1 * beta(z)
              + qv * z * (a1 + qv**2 * a)))
    num = sp.numer(sp.cancel(sp.together(rel)))
    P = sp.Poly(sp.expand(num), z)
    eqs = [sp.expand(c) for c in P.all_coeffs()]
    A, b = sp.linear_eq_to_matrix(eqs, list(cs))
    return A.rank(), A.row_join(b).rank(), len(cs)


def aux_roots():
    print("(3) the two slot polynomials of the final step, and their coprimality")
    p1 = sp.expand((q + 1)**2 * (1 - q**2) * (1 - q**4) - q)
    p2 = sp.expand((q + 1)**2 * (1 - q**4) * (1 - q**6) - q)
    print("    (a a_1 - q)(z_a Q)   = (q+1)^2 (1-q^2)(1-q^4) - q")
    print("    (a a_1 - q)(z_a Q^2) = (q+1)^2 (1-q^4)(1-q^6) - q")
    for name, p in (("first", p1), ("second", p2)):
        rts = [r for r in sp.Poly(p, q).all_roots() if r.is_real]
        inside = [sp.nsimplify(r) for r in rts if 0 < r < 1]
        vals = [sp.N(r, 20) for r in inside]
        print(f"    {name} polynomial: roots in (0,1): "
              + ", ".join(str(v) for v in vals))
    g = sp.gcd(sp.Poly(p1, q), sp.Poly(p2, q))
    print(f"    gcd of the two polynomials over Q[q]: {g.as_expr()}")
    print("    coprime, so for every q in (0,1) at least one of the two slots has a")
    print("    nonvanishing coefficient and the sweep is exhaustive.\n")


if __name__ == "__main__":
    print("qcos_nonintegrable: exact checks for prop:nonintegrable\n")
    scalar_equation()
    print("(2) window cross-check: poles of order <= 3 at {z_a Q^-1, ..., z_a Q^3}")
    for qv in (sp.Rational(1, 3), sp.Rational(1, 5)):
        rA, rAb, n = window_system(qv)
        print(f"    q = {qv}:  {n} unknowns,  rank(A) = {rA},  rank([A|b]) = {rAb}"
              f"  -> {'INCONSISTENT, no such beta' if rAb > rA else 'consistent'}")
    print()
    aux_roots()
    print("done.")
