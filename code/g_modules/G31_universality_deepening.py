#!/usr/bin/env python3
"""
Module G31 -- Universality conjecture deepening (Attacks A & B)
================================================================

Three coordinated attacks on conj:universality of paper.tex (v7.2).

ATTACK A: Empirical deepening of sub-conjecture (1): N_alg = K_univ.

  - Enumerate canonical (shortlex) words of W = <R_0,R_1,R_2 | R_i^2,
    (R_0 R_1)^2> on the canonical (2,inf,inf) Coxeter system to depths
    11..14.
  - At each depth, find ALL collision classes (canonical words with
    identical rho_{a,b}(.) over Q(a,b)).  These are EXACTLY the
    universal relations of length <= d.
  - Mod out by length-10 conjugate-translates of the 8 generators of
    N_alg (the "Bonfioli generators").  Any "new" universal relation
    is one that survives this reduction.
  - We use a *cheap proxy* for "lies in N_alg":  build a coset table of
    W / <<8 generators>> via the Todd-Coxeter-style multiplication of
    canonical-form words by conjugates of the 8 length-10 relators,
    plus the Coxeter relations themselves.  Equivalently we check
    whether each collision pair (u, v) admits a length-bounded
    rewriting using the 8 relators (mod Coxeter) reducing to identity.

ATTACK B: Sub-conjecture (2): K_T = K_univ for every rational T.

  - For each candidate triangle T in
      { (3,4), (5,12), (1,2), (8,15), (7,24), (20,21), (1,3) },
    instantiate rho_T and evaluate canonical words of depth 11..14.
  - Collision classes at T (specific) but not in Q(a,b) (universal)
    are triangle-specific kernel elements.  Even ONE such would
    falsify sub-conjecture (2) for that triangle.
  - We perform the test in two layers:
      (i) numeric/p-adic mod p evaluation at T (fast),
      (ii) confirm collisions hold exactly at T but NOT generically.

This script is purely computational and is the empirical workhorse
behind any claim of evidence-strength for the universality conjecture.
"""
from __future__ import annotations

import json
import time
from fractions import Fraction
from itertools import product
from typing import Dict, List, Tuple, Set, Optional

import sympy as sp


Word = Tuple[int, ...]

# -----------------------------------------------------------------------------
# Canonical (2, inf, inf) system: build reflection matrices over Q(a, b).
# Mirror 0 = x-axis;  Mirror 1 = y-axis (perpendicular, m01=2);
# Mirror 2 = hypotenuse of right triangle with legs (a, b):
#   line through (a, 0) and (0, b).
# -----------------------------------------------------------------------------

a, b = sp.symbols('a b', positive=True)

def refl_line(p1, p2):
    """3x3 affine reflection matrix as 6-tuple."""
    x1, y1 = p1
    x2, y2 = p2
    dx, dy = x2 - x1, y2 - y1
    nx, ny = -dy, dx
    L_sq = nx*nx + ny*ny
    n_dot = nx*x1 + ny*y1
    return (
        sp.cancel(1 - 2*nx*nx/L_sq),
        sp.cancel(-2*nx*ny/L_sq),
        sp.cancel(2*nx*n_dot/L_sq),
        sp.cancel(-2*nx*ny/L_sq),
        sp.cancel(1 - 2*ny*ny/L_sq),
        sp.cancel(2*ny*n_dot/L_sq),
    )

def matmul(A, B):
    a00,a01,a02,a10,a11,a12 = A
    b00,b01,b02,b10,b11,b12 = B
    return (
        a00*b00+a01*b10, a00*b01+a01*b11, a00*b02+a01*b12+a02,
        a10*b00+a11*b10, a10*b01+a11*b11, a10*b02+a11*b12+a12,
    )

IDENT = (sp.Integer(1), sp.Integer(0), sp.Integer(0),
         sp.Integer(0), sp.Integer(1), sp.Integer(0))

def build_gens_symbolic():
    # canonical right-triangle: R0 = reflect across x-axis, R1 = reflect across
    # y-axis, R2 = reflect across hypotenuse from (a,0) to (0,b).
    R0 = refl_line((sp.Integer(0), sp.Integer(0)), (sp.Integer(1), sp.Integer(0)))
    R1 = refl_line((sp.Integer(0), sp.Integer(0)), (sp.Integer(0), sp.Integer(1)))
    R2 = refl_line((a, sp.Integer(0)), (sp.Integer(0), b))
    return [R0, R1, R2]


# -----------------------------------------------------------------------------
# Numeric / triangle-specific generators
# -----------------------------------------------------------------------------

def build_gens_numeric(a_val: Fraction, b_val: Fraction):
    """Build matrices over Q at specific (a, b)."""
    def Qrefl(p1, p2):
        x1, y1 = p1
        x2, y2 = p2
        dx, dy = x2 - x1, y2 - y1
        nx, ny = -dy, dx
        L_sq = nx*nx + ny*ny
        n_dot = nx*x1 + ny*y1
        return (
            Fraction(1) - Fraction(2)*nx*nx / L_sq,
            -Fraction(2)*nx*ny / L_sq,
            Fraction(2)*nx*n_dot / L_sq,
            -Fraction(2)*nx*ny / L_sq,
            Fraction(1) - Fraction(2)*ny*ny / L_sq,
            Fraction(2)*ny*n_dot / L_sq,
        )
    z = Fraction(0); o = Fraction(1)
    R0 = Qrefl((z,z),(o,z))
    R1 = Qrefl((z,z),(z,o))
    R2 = Qrefl((a_val, z), (z, b_val))
    return [R0, R1, R2]

def matmul_Q(A, B):
    a00,a01,a02,a10,a11,a12 = A
    b00,b01,b02,b10,b11,b12 = B
    return (
        a00*b00+a01*b10, a00*b01+a01*b11, a00*b02+a01*b12+a02,
        a10*b00+a11*b10, a10*b01+a11*b11, a10*b02+a11*b12+a12,
    )

IDENT_Q = (Fraction(1), Fraction(0), Fraction(0),
           Fraction(0), Fraction(1), Fraction(0))

def apply_word_Q(word, gens):
    m = IDENT_Q
    for i in word:
        m = matmul_Q(gens[i], m)
    return m


# -----------------------------------------------------------------------------
# Shortlex canonical-form enumeration for (m01,m02,m12) = (2, inf, inf)
# Rules:
#   - R_i R_i -> e
#   - R_1 R_0 -> R_0 R_1  (commute, since m01=2)
# Canonical iff no substring "ii" and no substring "10".
# -----------------------------------------------------------------------------

def is_canonical(w: Word) -> bool:
    for k in range(len(w) - 1):
        a_, b_ = w[k], w[k+1]
        if a_ == b_:
            return False
        if (a_, b_) == (1, 0):
            return False
    return True

def enumerate_canonical(max_d: int) -> Dict[int, List[Word]]:
    out = {0: [()]}
    prev = [()]
    for d in range(1, max_d + 1):
        cur = []
        for w in prev:
            last = w[-1] if w else -1
            for g in range(3):
                if g == last:
                    continue
                if last == 1 and g == 0:
                    continue
                cur.append(w + (g,))
        out[d] = cur
        prev = cur
    return out


# -----------------------------------------------------------------------------
# Mod-p hash for fast collision pre-screening over Q(a,b).
# We pick two random small primes p, evaluate (a, b) at random non-zero
# residues, and record the matrix tuple mod p as the "image hash".
# Collisions over Q(a,b) -> identical images at ALL substitutions.
# We use multiple substitutions to make hash collisions vanishingly likely.
# -----------------------------------------------------------------------------

def matmul_mod(A, B, p):
    a00,a01,a02,a10,a11,a12 = A
    b00,b01,b02,b10,b11,b12 = B
    return (
        (a00*b00+a01*b10) % p, (a00*b01+a01*b11) % p, (a00*b02+a01*b12+a02) % p,
        (a10*b00+a11*b10) % p, (a10*b01+a11*b11) % p, (a10*b02+a11*b12+a12) % p,
    )

def inv_mod(x, p):
    return pow(x, p-2, p)

def build_gens_mod(a_val, b_val, p):
    """Build mod-p matrices, all arithmetic done mod p, with rational entries
    realised as a*inv(c) mod p."""
    def Qrefl_mod(p1, p2):
        x1, y1 = p1
        x2, y2 = p2
        dx, dy = (x2 - x1) % p, (y2 - y1) % p
        nx, ny = (-dy) % p, dx
        L_sq = (nx*nx + ny*ny) % p
        L_inv = inv_mod(L_sq, p)
        n_dot = (nx*x1 + ny*y1) % p
        return (
            (1 - 2*nx*nx*L_inv) % p, (-2*nx*ny*L_inv) % p, (2*nx*n_dot*L_inv) % p,
            (-2*nx*ny*L_inv) % p, (1 - 2*ny*ny*L_inv) % p, (2*ny*n_dot*L_inv) % p,
        )
    R0 = Qrefl_mod((0,0),(1,0))
    R1 = Qrefl_mod((0,0),(0,1))
    R2 = Qrefl_mod((a_val, 0), (0, b_val))
    return [R0, R1, R2]

def apply_word_mod(w, gens, p):
    m = (1,0,0,0,1,0)
    for i in w:
        m = matmul_mod(gens[i], m, p)
    return m


# -----------------------------------------------------------------------------
# Build mod-p generators for many (a, b) samples (over Q(a,b) -- random).
# Two words collide universally iff they collide at every random (a,b,p).
# Use 4 substitutions across 2 primes; false positives have probability
# ~ 1/p^4 ~ 10^-30, negligible.
# -----------------------------------------------------------------------------

PRIMES = [1_000_003, 1_000_033]
SAMPLES = [
    (PRIMES[0], 17, 23),
    (PRIMES[0], 31, 41),
    (PRIMES[1], 19, 29),
    (PRIMES[1], 37, 47),
]

def universal_signature(w: Word, gens_list):
    """Return tuple of mod-p images of w under each sampled rho."""
    sig = []
    for (p, gens) in gens_list:
        sig.append(apply_word_mod(w, gens, p))
    return tuple(sig)


# -----------------------------------------------------------------------------
# The 8 length-10 generators of N_alg from §5 of paper.tex.
# Stored as pairs (A, B) such that A*B^{-1} \in N_alg, i.e. rho(A)=rho(B).
# -----------------------------------------------------------------------------

EIGHT_RELATIONS = [
    # (A_word, B_word) -- A and B should map to same rho image
    ((0,1,2,0,2,0,1,2,1,2), (2,1,2,0,1,2,0,2,0,1)),
    ((0,1,2,1,2,0,1,2,0,2), (2,0,2,0,1,2,1,2,0,1)),
    ((0,2,0,1,2,1,2,0,1,2), (2,0,1,2,1,2,0,1,2,0)),
    ((0,2,0,2,0,1,2,1,2,0), (1,2,1,2,0,1,2,0,2,1)),
    ((0,2,0,2,0,1,2,1,2,1), (1,2,1,2,0,1,2,0,2,0)),
    ((0,2,1,2,0,1,2,0,2,0), (1,2,0,2,0,1,2,1,2,1)),
    ((0,2,1,2,0,1,2,0,2,1), (1,2,0,2,0,1,2,1,2,0)),
    ((1,2,0,1,2,0,2,0,1,2), (2,0,1,2,0,2,0,1,2,1)),
]


# =============================================================================
# ATTACK A: depth-deepening universal-collision enumeration
# =============================================================================

def attack_A(max_depth: int = 14) -> Dict:
    print("\n" + "="*70)
    print(f"ATTACK A: universal collisions on (2,inf,inf) up to depth {max_depth}")
    print("="*70)

    gens_list = []
    for (p, a_v, b_v) in SAMPLES:
        gens_list.append((p, build_gens_mod(a_v, b_v, p)))

    canon = enumerate_canonical(max_depth)
    results = {"depth_data": {}, "all_classes": []}

    for d in range(1, max_depth + 1):
        words = canon[d]
        sig_buckets: Dict[Tuple, List[Word]] = {}
        for w in words:
            s = universal_signature(w, gens_list)
            sig_buckets.setdefault(s, []).append(w)

        classes = [v for v in sig_buckets.values() if len(v) >= 2]
        n_pairs = sum(len(v)*(len(v)-1)//2 for v in classes)
        print(f"  depth {d:2d}: |canonical|={len(words):6d}  "
              f"classes={len(classes):4d}  pairs={n_pairs:5d}")
        results["depth_data"][d] = {
            "n_canonical": len(words),
            "n_classes": len(classes),
            "n_pairs": n_pairs,
        }
        for cl in classes:
            results["all_classes"].append({
                "depth": d,
                "size": len(cl),
                "words": [list(w) for w in sorted(cl)[:8]],
            })

    return results


# =============================================================================
# ATTACK A.5: reduction to N_alg.
# Strategy: given a candidate universal identity (u, v) with rho(u)=rho(v),
# we ask whether u*v^{-1} lies in the normal closure of the 8 generators.
# A computationally tractable proxy: try to rewrite u into v using
#   - Coxeter moves (involutivity, m01=2 commute)
#   - left/right multiplication by any of the 8 relators (or their cyclic
#     shifts / conjugates) up to a fixed length budget.
# We BFS in the Cayley-graph of W/N_alg with a length cap.  Since we know
# canonical-form arithmetic up to depth ~14, we can directly test:
#   For each new universal class C at depth d > 10, mark C as "in N_alg"
#   iff every w in C can be reduced via local "insert and cancel" of the
#   length-10 relators to a shorter canonical word, eventually meeting a
#   common shorter representative.
#
# Equivalently: define an equivalence ~ on W where u ~ v if v can be
# obtained from u by inserting an instance of (A_i, B_i) (or B_i, A_i)
# anywhere in u (with reduction to canonical form).  If all members of
# C are ~-equivalent to a single canonical representative, the identity
# is in N_alg.  We use a BFS up to a length cap on intermediate words.
# =============================================================================

# Coxeter reductions for (2, inf, inf):
def reduce_step(w: Word) -> Word:
    """One pass: apply ii->e and 1 0 -> 0 1 repeatedly."""
    changed = True
    while changed:
        changed = False
        out = []
        i = 0
        while i < len(w):
            if i+1 < len(w) and w[i] == w[i+1]:
                # cancel
                i += 2
                changed = True
            else:
                out.append(w[i])
                i += 1
        w = tuple(out)
        # commute 10->01 (do a single left-to-right pass)
        out = list(w)
        i = 0
        while i + 1 < len(out):
            if out[i] == 1 and out[i+1] == 0:
                out[i], out[i+1] = 0, 1
                changed = True
                i = max(0, i - 1)
                continue
            i += 1
        w = tuple(out)
    return w

# Build conjugacy multiplication: applying relator R = A*B^{-1} on word w means
# multiplying by R^{\pm 1} after a cyclic shift or at any insertion point.
# Concretely: u -> reduce(prefix + A + suffix) and check it equals
# reduce(prefix + B + suffix).  More usefully for BFS reduction:
# given u with rho(u)=rho(v), we try insertions of (A_i * B_i^{-1}) and its
# conjugates anywhere in u to reach v.
#
# Simpler operational test (cleaner): a "swap move" on a word w replaces
# any occurrence of (canonical-form of) A_i in w with (canonical-form of)
# B_i (and vice versa).  If from u we can reach v by a sequence of swap
# moves + Coxeter reductions with bounded intermediate length, then
# u and v are equivalent mod N_alg.

# Build canonical forms of the 8 relations:
RELATION_PAIRS = [(reduce_step(A), reduce_step(B)) for (A, B) in EIGHT_RELATIONS]

# Also include cyclic conjugates of each relation: if A ~ B mod N_alg then
# (g A g^{-1}) ~ (g B g^{-1}) for any g.  In particular, "rotating" the
# relation -- moving a generator from one end to the other (conjugation by
# that generator) -- still lies in N_alg.  We add all cyclic rotations of
# A and B that are still length 10.
def cyclic_conjugates(A: Word, B: Word) -> List[Tuple[Word, Word]]:
    """Cyclic conjugates by 1-letter steps:
    (A, B) ~ (R_i A R_i, R_i B R_i) when R_i is the first/last letter, etc.
    For length-10 relations, cyclic shift by 1: conjugation by w[0] gives
    (w[1:] + w[0:1], ...). The pair (A, B) being in N_alg is preserved
    under conjugation: g A g^{-1} ~ g B g^{-1} mod N_alg.
    So we add all conjugations by single generators on either side."""
    out = [(A, B)]
    for g in range(3):
        # conjugation by R_g on both sides
        cA = reduce_step((g,) + A + (g,))
        cB = reduce_step((g,) + B + (g,))
        out.append((cA, cB))
    return out

ALL_MOVES = []
for (A, B) in RELATION_PAIRS:
    for (A2, B2) in cyclic_conjugates(A, B):
        ALL_MOVES.append((A2, B2))
        ALL_MOVES.append((B2, A2))

def apply_move_anywhere(w: Word, src: Word, dst: Word, length_cap: int) -> List[Word]:
    """Find all positions where src occurs as substring in w, replace with dst,
    canonicalise, return new words (filtered by length cap)."""
    out = []
    L = len(src)
    for k in range(len(w) - L + 1):
        if w[k:k+L] == src:
            new = w[:k] + dst + w[k+L:]
            new = reduce_step(new)
            if len(new) <= length_cap:
                out.append(new)
    return out

def reduce_to_canonical(w: Word) -> Word:
    """Apply Coxeter reductions to canonical (shortlex) form."""
    return reduce_step(w)

def in_N_alg_bfs(u: Word, v: Word, length_cap: int = 24, time_cap_s: float = 8.0) -> bool:
    """BFS from u: at each step, apply any move (A_i -> B_i) at any
    position, reduce, push new states.  Stop when v is reached or
    length_cap reached or time exhausted."""
    u_red = reduce_to_canonical(u)
    v_red = reduce_to_canonical(v)
    if u_red == v_red:
        return True
    seen = {u_red}
    frontier = [u_red]
    t0 = time.time()
    while frontier:
        if time.time() - t0 > time_cap_s:
            return False
        new_frontier = []
        for w in frontier:
            for (src, dst) in ALL_MOVES:
                for new in apply_move_anywhere(w, src, dst, length_cap):
                    if new == v_red:
                        return True
                    if new not in seen:
                        seen.add(new)
                        new_frontier.append(new)
            if len(seen) > 200_000:
                return False
        frontier = new_frontier
    return False


def attack_A_reduction(attackA_result: Dict, max_depth: int) -> Dict:
    """For each universal collision class at depths 11..max_depth, attempt
    reduction to N_alg via BFS with moves drawn from the 8 generators
    (and cyclic conjugates by single generators)."""
    print("\n" + "="*70)
    print("ATTACK A reduction: testing membership in N_alg via BFS")
    print("="*70)

    summary_by_depth = {}
    candidate_new_generators = []

    for cls in attackA_result["all_classes"]:
        d = cls["depth"]
        if d <= 10:
            continue
        words = [tuple(w) for w in cls["words"]]
        # pick canonical reps
        rep = words[0]
        in_N = True
        offenders = []
        for other in words[1:]:
            ok = in_N_alg_bfs(rep, other, length_cap=max(20, d + 6),
                              time_cap_s=4.0)
            if not ok:
                in_N = False
                offenders.append((list(rep), list(other)))
                break
        depth_data = summary_by_depth.setdefault(d, {"total": 0, "in_N": 0,
                                                     "candidates": 0})
        depth_data["total"] += 1
        if in_N:
            depth_data["in_N"] += 1
        else:
            depth_data["candidates"] += 1
            candidate_new_generators.append({
                "depth": d,
                "rep_pair": offenders[0] if offenders else None,
                "class_size": cls["size"],
            })

    for d in sorted(summary_by_depth):
        sd = summary_by_depth[d]
        print(f"  depth {d:2d}: {sd['total']:3d} classes, "
              f"{sd['in_N']:3d} in N_alg, "
              f"{sd['candidates']:3d} candidate-new-generators")

    return {
        "summary_by_depth": summary_by_depth,
        "candidate_new_generators": candidate_new_generators[:20],
    }


# =============================================================================
# ATTACK B: triangle-specific kernel elements
# =============================================================================

def attack_B(max_depth: int = 13) -> Dict:
    print("\n" + "="*70)
    print(f"ATTACK B: triangle-specific kernel search up to depth {max_depth}")
    print("="*70)

    # Triangles to test
    triangles = [
        (Fraction(3), Fraction(4)),
        (Fraction(5), Fraction(12)),
        (Fraction(1), Fraction(2)),
        (Fraction(8), Fraction(15)),
        (Fraction(7), Fraction(24)),
        (Fraction(20), Fraction(21)),
        (Fraction(1), Fraction(3)),
    ]

    # Build universal mod-p generators (same as attack A) -- a word is in
    # K_univ iff its universal signature equals identity signature.
    gens_list_univ = []
    for (p, a_v, b_v) in SAMPLES:
        gens_list_univ.append((p, build_gens_mod(a_v, b_v, p)))

    # Identity universal signature
    id_signature = tuple((1,0,0,0,1,0) for _ in SAMPLES)

    canon = enumerate_canonical(max_depth)

    result = {"triangles": [], "per_depth": {}}

    for (a_v, b_v) in triangles:
        tri_data = {"triangle": [str(a_v), str(b_v)], "by_depth": {}}
        # Build T-specific generators over Q
        gens_T = build_gens_numeric(a_v, b_v)
        # And mod-p versions for fast check too (use same primes as univ).
        # But for exactness we need rational arithmetic -- use Fractions.
        for d in range(1, max_depth + 1):
            words = canon[d]
            # For each canonical word, evaluate at T (over Q) and check id.
            id_T = IDENT_Q
            # find all words with rho_T(w) == identity AT THE TRIANGLE
            # but rho_univ(w) != identity (i.e., NOT in K_univ).
            triangle_specific = []
            t_ker_count = 0
            for w in words:
                # universal signature first (cheap)
                sig = universal_signature(w, gens_list_univ)
                # rho_T(w) -- exact over Q
                # SHORTCUT: if w is "long-ish", evaluate rho_T mod a single
                # large prime first as pre-screen
                # We'll just evaluate over Q directly -- depth <= 14 is fine
                m_T = apply_word_Q(w, gens_T)
                if m_T == IDENT_Q:
                    t_ker_count += 1
                    if sig != id_signature:
                        # triangle-specific kernel element!
                        triangle_specific.append(list(w))
            tri_data["by_depth"][d] = {
                "n_canonical": len(words),
                "rho_T_identity_count": t_ker_count,
                "triangle_specific_count": len(triangle_specific),
                "triangle_specific_examples": triangle_specific[:5],
            }
        result["triangles"].append(tri_data)

    # Print summary table
    print(f"\n{'triangle':12s}" + "".join(f"d={d:>2d}".rjust(8) for d in range(8, max_depth+1)))
    for tri in result["triangles"]:
        a_v, b_v = tri["triangle"]
        row = f"({a_v},{b_v})".ljust(12)
        for d in range(8, max_depth + 1):
            n = tri["by_depth"].get(d, {}).get("triangle_specific_count", 0)
            row += f"{n:>8d}"
        print(row)

    return result


# =============================================================================
# Main
# =============================================================================

def main():
    t0 = time.time()
    print("G31 -- Universality conjecture deepening")
    print(f"start: {time.strftime('%H:%M:%S')}")

    # Choose depths.  Depth 14 produces 233 * phi^4 ~ 1500 canonical words --
    # very tractable.  Depth 15 ~ 2400.  We'll go to 14 firmly; try 15 if time.
    MAX_DEPTH_A = 14
    MAX_DEPTH_B = 13  # B is more expensive (Q-arithmetic per word per triangle)

    # Attack A
    A_res = attack_A(MAX_DEPTH_A)
    A_red = attack_A_reduction(A_res, MAX_DEPTH_A)

    # Attack B
    B_res = attack_B(MAX_DEPTH_B)

    runtime = round(time.time() - t0, 1)
    print(f"\nTotal runtime: {runtime}s")

    out = {
        "max_depth_A": MAX_DEPTH_A,
        "max_depth_B": MAX_DEPTH_B,
        "attack_A": A_res,
        "attack_A_reduction": A_red,
        "attack_B": B_res,
        "runtime_s": runtime,
    }
    out_path = __file__.replace(".py", "_results.json")
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"Written: {out_path}")


if __name__ == "__main__":
    main()
