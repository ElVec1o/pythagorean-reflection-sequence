#!/usr/bin/env python3
"""Exact verification of suspected collision pairs exported by certify38.

Each line of the pairs file holds two symbolic elements
    eps delta k n e1 c1 ... en cn | eps delta k n ...
A pair is a TRUE collision for the triangle (x, y) iff the two translation
polynomials agree at zeta = (x + yi)/(x - yi), evaluated in exact rational
arithmetic over Q(i) (Fractions; no overflow, no probability).

Usage: python3 exact_check.py certify38_state/pairs_d38_X_Y.txt
"""
import sys
from fractions import Fraction as F


def gmul(u, v):
    return (u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0])


def main(path):
    lines = open(path).read().strip().split("\n")
    hdr = lines[0].split()
    x = int(hdr[1].split("=")[1])
    y = int(hdr[2].split("=")[1])
    n2 = x * x + y * y
    zeta = (F(x * x - y * y, n2), F(2 * x * y, n2))  # (x+yi)/(x-yi)
    zinv = (zeta[0], -zeta[1])  # |zeta| = 1

    def parse(tokens):
        eps, delta, k, n = int(tokens[0]), int(tokens[1]), int(tokens[2]), int(tokens[3])
        terms = [(int(tokens[4 + 2 * i]), int(tokens[5 + 2 * i])) for i in range(n)]
        return eps, delta, k, terms

    def eval_poly(terms):
        # cache powers
        v = (F(0), F(0))
        for e, c in terms:
            p = (F(1), F(0))
            base = zeta if e >= 0 else zinv
            for _ in range(abs(e)):
                p = gmul(p, base)
            v = (v[0] + c * p[0], v[1] + c * p[1])
        return v

    true_pairs, false_pairs = 0, 0
    merged = {}
    for ln in lines[1:]:
        if not ln.strip():
            continue
        left, right = ln.split("|")
        e1 = parse(left.split())
        e2 = parse(right.split())
        assert (e1[0], e1[1], e1[2]) == (e2[0], e2[1], e2[2]), "linear parts differ?!"
        v1, v2 = eval_poly(e1[3]), eval_poly(e2[3])
        if v1 == v2:
            true_pairs += 1
            key = (e1[0], e1[1], e1[2], tuple(sorted(v1)))
            merged.setdefault(key, set()).update([tuple(e1[3]), tuple(e2[3])])
        else:
            false_pairs += 1
    print(f"file: {path}  triangle ({x},{y})")
    print(f"  exact TRUE collisions : {true_pairs} pairs")
    print(f"  modular accidents     : {false_pairs} pairs (refuted exactly)")
    if merged:
        deficit = sum(len(s) - 1 for s in merged.values())
        print(f"  distinct merged groups: {len(merged)}  ->  exact ball deficit {deficit}")
        print("  VERDICT: REAL deviation at depth <= ball depth for this shape.")
    else:
        print("  VERDICT: NO real collision — shape is CLEAN at this depth.")


if __name__ == "__main__":
    main(sys.argv[1])
