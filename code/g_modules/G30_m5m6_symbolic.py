#!/usr/bin/env python3
"""
Module G30 -- Symbolic closure of the (m,inf,inf) apex family for m = 5, 6
==========================================================================

G29 numerically discovered candidate rho-discovered relations for the
triangle Coxeter groups (5, inf, inf) (length 11) and (6, inf, inf)
(length 8).  Symbolic certification via sympy's `simplify(cos(pi/5))` /
`simplify(cos(pi/6))` timed out in G29.

Workaround.  Substitute the explicit surd values
    cos(pi/5) = (1 + sqrt 5)/4,    sin(pi/5) = sqrt(10 - 2 sqrt 5)/4,
    cos(pi/6) = sqrt 3 / 2,        sin(pi/6) = 1/2,
so the reflection matrices live in Q(a, b, sqrt 5) or Q(a, b, sqrt 3)
respectively, and sympy can verify rho(w_star) = id as a matrix
identity by polynomial arithmetic alone -- no trig simplification
required.

The candidate words are read directly from
G29_cb_class_search_results.json (the first collision class for each
diagram).  Construction of the affine realisation is the same as in
G29: mirror 0 = x-axis, mirror 1 through origin at apex angle pi/m,
mirror 2 = line through (a, 0) and (a + 1, b) with a, b > 0 free.

A "rho-discovered relation" between two distinct canonical words
A, B is checked by verifying that rho(A) and rho(B) coincide as
3x3 affine matrices entry-by-entry, after substituting the surds
and running sympy's polynomial-only simplifier
`sp.radsimp(sp.expand(.))`.
"""
from __future__ import annotations

import json
import os
import time
from typing import List, Tuple

import sympy as sp


# ---- surd values -----------------------------------------------------------

SQRT5 = sp.sqrt(5)
SQRT3 = sp.sqrt(3)


def cos_sin_for_m(m: int):
    """Return (cos(pi/m), sin(pi/m)) as surd-only sympy expressions for
    m in {5, 6}.  Raises ValueError otherwise."""
    if m == 5:
        c = (1 + SQRT5) / 4
        s = sp.sqrt(10 - 2 * SQRT5) / 4
        return c, s
    if m == 6:
        c = SQRT3 / 2
        s = sp.Rational(1, 2)
        return c, s
    raise ValueError(f"no surd table for m = {m}")


# ---- reflection-matrix machinery (same shape as G29) -----------------------


def reflection_matrix_sym(p1, p2):
    """Return the 6-tuple of nontrivial entries of the 3x3 affine
    reflection across the line through p1 and p2."""
    x1, y1 = p1
    x2, y2 = p2
    dx, dy = x2 - x1, y2 - y1
    nx, ny = -dy, dx
    L_sq = nx * nx + ny * ny
    n_dot_p1 = nx * x1 + ny * y1
    return (
        1 - 2 * nx * nx / L_sq,
        -2 * nx * ny / L_sq,
        2 * nx * n_dot_p1 / L_sq,
        -2 * nx * ny / L_sq,
        1 - 2 * ny * ny / L_sq,
        2 * ny * n_dot_p1 / L_sq,
    )


def matmul_sym(A, B):
    a00, a01, a02, a10, a11, a12 = A
    b00, b01, b02, b10, b11, b12 = B
    return (
        a00 * b00 + a01 * b10,
        a00 * b01 + a01 * b11,
        a00 * b02 + a01 * b12 + a02,
        a10 * b00 + a11 * b10,
        a10 * b01 + a11 * b11,
        a10 * b02 + a11 * b12 + a12,
    )


IDENT = tuple(sp.Integer(x) for x in (1, 0, 0, 0, 1, 0))


def apply_word(word, gens):
    m = IDENT
    for i in word:
        m = matmul_sym(gens[i], m)
    return m


# ---- realisation builder for (m, inf, inf) ---------------------------------


def build_gens_apex(m: int):
    """Return (gens, [a, b], surd) for the (m, inf, inf) realisation
    with mirror 0 = x-axis, mirror 1 through origin at angle pi/m
    given by surd values, mirror 2 = generic free line."""
    a = sp.Symbol("a", positive=True, real=True)
    b = sp.Symbol("b", positive=True, real=True)
    cos_pm, sin_pm = cos_sin_for_m(m)
    surd = SQRT5 if m == 5 else SQRT3

    L0 = ((sp.Integer(0), sp.Integer(0)), (sp.Integer(1), sp.Integer(0)))
    L1 = ((sp.Integer(0), sp.Integer(0)), (cos_pm, sin_pm))
    L2 = ((a, sp.Integer(0)), (a + 1, b))

    gens = [
        reflection_matrix_sym(*L0),
        reflection_matrix_sym(*L1),
        reflection_matrix_sym(*L2),
    ]
    return gens, [a, b], surd


# ---- verification ----------------------------------------------------------


def simplify_in_quadratic(expr, surd):
    """Simplify an expression in Q(a, b, surd) where surd^2 is a small
    integer.  We use polynomial expansion + radical cancellation; this
    avoids the expensive simplify(cos(pi/m)) call path.
    """
    e = sp.expand(expr)
    e = sp.radsimp(e)
    e = sp.simplify(e)  # final cleanup; cheap because everything is polynomial now
    return e


def verify_identity(word_A, word_B, m: int, verbose=True):
    """Check that rho(A) == rho(B) as matrices in Q(a, b, sqrt(.))."""
    gens, _, surd = build_gens_apex(m)
    MA = apply_word(tuple(word_A), gens)
    MB = apply_word(tuple(word_B), gens)
    all_ok = True
    for k, (eA, eB) in enumerate(zip(MA, MB)):
        diff = simplify_in_quadratic(eA - eB, surd)
        ok = (diff == 0)
        if not ok and verbose:
            print(f"  entry {k}: difference = {diff}")
        all_ok = all_ok and ok
    return all_ok


# ---- main ------------------------------------------------------------------


def main():
    print("=" * 78)
    print(" G30 -- m = 5, 6 symbolic closure via surd substitution")
    print("=" * 78)

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "G29_cb_class_search_results.json")) as f:
        g29 = json.load(f)

    # pick the candidate pair for m = 5 and m = 6
    def first_example_for(m_label):
        for r in g29["results"]:
            if str(r.get("labels", [None])[0]) == str(m_label):
                ex = r.get("examples", [])
                if ex:
                    return ex[0]
        return None

    summary = []
    for m in (5, 6):
        print(f"\n--- m = {m}: (m, inf, inf), surd ring Q(a, b, "
              f"sqrt {5 if m == 5 else 3}) ---")
        ex = first_example_for(m)
        if ex is None:
            print(f"  no candidate from G29 for m={m}; skipping")
            summary.append({"m": m, "verified": False, "reason": "no candidate"})
            continue
        words = ex["words"][:2]
        wA, wB = words[0], words[1]
        print(f"  word A = {wA}")
        print(f"  word B = {wB}")
        t0 = time.time()
        ok = verify_identity(wA, wB, m)
        dt = round(time.time() - t0, 2)
        print(f"  symbolic verify: {'PASS' if ok else 'FAIL'}   "
              f"(time {dt}s)")
        summary.append({
            "m": m,
            "labels": [m, "inf", "inf"],
            "ring": f"Q(a, b, sqrt {5 if m == 5 else 3})",
            "length": len(wA),
            "word_A": wA,
            "word_B": wB,
            "verified": bool(ok),
            "time_s": dt,
        })

    out_path = os.path.join(here, "G30_m5m6_symbolic_results.json")
    with open(out_path, "w") as f:
        json.dump({"summary": summary}, f, indent=2)
    print(f"\nWritten: {out_path}")

    all_ok = all(s.get("verified") for s in summary)
    print(f"\nOVERALL: {'ALL PASS' if all_ok else 'FAIL'}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
