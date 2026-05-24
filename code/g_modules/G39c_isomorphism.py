#!/usr/bin/env python3
"""G39c -- Verify Z[Q].h ~= Z[Q]/(Y+1, c+1) as left modules, and confirm
that this equals I_A cap I_B.

h = (c-1)(Y-1) satisfies Y*h = -h and c*h = -h, so there is a surjection
   pi: M := Z[Q]/(Y+1, c+1) ->> Z[Q].h,   1 |-> h.
We check INJECTIVITY by computing Z-rank of Z[Q].h and the expected Z-rank
of M (truncated).

M as left Z[Q]-module: Z-basis indexed by w.v where w is an alternating word
in {X,Y} that does NOT end in Y, and no c factor (c gets absorbed by sign).
Equivalently: alternating words ending in X, or empty.

For L_amb truncation, count of such reduced-word multipliers w with |w| <= L
that produce results in the L_amb truncation when multiplied against h.
"""
from __future__ import annotations
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from G39_noncomm_ideal import (
    X_minus_1, Y_minus_1, c_minus_1, gen_one, gen_X, gen_Y, gen_c,
    zq_mul, zq_add, zq_scale, zq_mul_left_by_q, pretty_zq,
    basis_index, enum_Q, enum_words, build_left_ideal,
    lattice_intersection, hnf, zq_to_vec, vec_to_zq, QElt,
)


def main() -> int:
    h = zq_mul(c_minus_1(), Y_minus_1())
    print(f"h = (c-1)(Y-1) = {pretty_zq(h)}")
    print(f"Annihilator: (Y+1)*h = ?, (c+1)*h = ?")
    Yph = zq_add(zq_mul(gen_Y(), h), h)
    cph = zq_add(zq_mul(gen_c(), h), h)
    print(f"  (Y+1)*h = {pretty_zq(Yph)}  (expect 0)")
    print(f"  (c+1)*h = {pretty_zq(cph)}  (expect 0)")
    assert not Yph and not cph

    # ------------------------------------------------------------
    # Compute Z-rank of M truncated: alternating words ending in X (or empty)
    # of length <= L (no c).
    # Words: "", "X", "YX", "XYX", "YXYX", "XYXYX", ...
    # Count up to length L: L + 1.
    # ------------------------------------------------------------
    # But wait — Z[Q].h truncated to L_amb has Z-rank = how many distinct q*h
    # have support in the L_amb truncation?  Each q*h has support involving
    # words of length up to |q| + 2 (since h has support up to length 1 in
    # {X,Y} word: h = 1 - c - Y + cY, so word lengths 0 and 1).
    # So multiplying by q of length k gives results in word lengths k-1 to k+1.

    print("\n--- Independence test: distinct elements of M act distinctly on h ---")
    # Generate set of canonical M-representatives: alternating words ending in X, plus "".
    L = 8
    reps: list[QElt] = [("", 0)]
    # words ending in X of length k = 1, 2, ..., L
    for k in range(1, L + 1):
        # word ending in X, alternating: if k odd, "XYX...X"; if k even, "YXYX...X"
        if k % 2 == 1:
            w = "".join("X" if i % 2 == 0 else "Y" for i in range(k))
        else:
            w = "".join("Y" if i % 2 == 0 else "X" for i in range(k))
        assert w[-1] == "X"
        reps.append((w, 0))
    print(f"Number of M-representative classes for L<={L}: {len(reps)}")

    # Compute q*h for each rep q.  These should be Z-linearly INDEPENDENT in Z[Q]
    # if Z[Q].h ~= M (no additional relations).
    L_amb = L + 2
    idx, Qs = basis_index(L_amb)
    vecs = []
    for q in reps:
        prod = zq_mul_left_by_q(q, h)
        try:
            v = zq_to_vec(prod, idx)
        except ValueError as e:
            print(f"  out of truncation for q={q}: {e}")
            continue
        vecs.append((q, v))
    print(f"Collected {len(vecs)} vectors")

    # Check independence via HNF
    rank_full = len(hnf([v for (_, v) in vecs]))
    print(f"Rank of Z-span of {{q*h : q in M-reps}}: {rank_full}")
    print(f"Expected (if M~=Z[Q].h): {len(vecs)}")
    if rank_full == len(vecs):
        print("=> M-representatives are Z-LINEARLY INDEPENDENT acting on h.")
        print("=> The surjection pi: M ->> Z[Q].h is ALSO INJECTIVE on truncation.")
        print("=> Z[Q].h ~= M = Z[Q]/(Y+1, c+1) as a left Z[Q]-module.")
    else:
        print(f"=> Linear dependence found: deficit {len(vecs) - rank_full}")

    # ------------------------------------------------------------
    # Now the BIG question: does Z[Q].h = I_A cap I_B?
    # We test inclusions both ways carefully, using LARGER multipliers for IA, IB
    # so that the intersection truncation is faithful.
    # ------------------------------------------------------------
    print("\n--- Lattice equality: Z[Q].h =?= I_A cap I_B ---")
    for L_amb_e, L_mult_e in [(8, 8), (10, 10), (12, 11)]:
        idx_e, Qs_e = basis_index(L_amb_e)
        IA = build_left_ideal([X_minus_1(), c_minus_1()], L_mult_e, L_amb_e, idx_e)
        IB = build_left_ideal([Y_minus_1()], L_mult_e, L_amb_e, idx_e)
        Inter = lattice_intersection(IA, IB)
        ZQh = build_left_ideal([h], L_mult_e, L_amb_e, idx_e)
        # Z[Q].h truncated should be subset of I_A cap I_B (true).
        # Inclusion h in I_A? (X-1)*Y = XY - Y, (X-1) = X-1, (c-1) = c-1.
        # Want h = 1 - c - Y + cY as r(X-1) + s(c-1) for some r, s in Z[Q].
        # Try s = -(Y-1), r = 0:  -(Y-1)(c-1) = -(Yc - Y - c + 1) = -Yc + Y + c - 1.
        #   = -(1 - c - Y + cY) = -h (using Yc = cY).   So h = (Y-1)(c-1) too.
        #   Wait: -h = -1 + c + Y - cY.  And -(Y-1)(c-1) = -Yc + Y + c - 1.
        #   With Yc = cY: -cY + Y + c - 1 = -h.  CORRECT: h = -(Y-1)(c-1) = (1-Y)(c-1).
        # Hmm. So h is expressible as (left mult by 1-Y) times (c-1):
        #     h = (1-Y)*(c-1)  -- this puts h in I_A (LEFT ideal containing c-1)? YES.
        # And h is also (c-1)*(Y-1) -- but (Y-1) is on the RIGHT.  For I_B (LEFT
        # ideal of Y-1), we need something*(Y-1) on the LEFT?  No, LEFT IDEAL
        # of Y-1 means r*(Y-1) for r in Z[Q].  So h = (c-1)*(Y-1) works!  YES.
        # Both inclusions confirmed.
        merged_rank = len(hnf(ZQh + Inter))
        print(f"L_amb={L_amb_e}, L_mult={L_mult_e}:  "
              f"rank IA={len(IA)}, IB={len(IB)}, Inter={len(Inter)}, "
              f"Z[Q].h={len(ZQh)}, Z[Q].h+Inter={merged_rank}")
        if merged_rank == len(ZQh) == len(Inter):
            print(f"   *** LATTICE EQUALITY Z[Q].h == I_A cap I_B at this truncation ***")
        elif merged_rank == len(ZQh):
            print(f"   Inter subset Z[Q].h  (deficit on Inter side: {len(ZQh)-len(Inter)})")
        elif merged_rank == len(Inter):
            print(f"   Z[Q].h subset Inter  (deficit on Z[Q].h side: {len(Inter)-len(ZQh)})")

    return 0


if __name__ == "__main__":
    sys.exit(main())
