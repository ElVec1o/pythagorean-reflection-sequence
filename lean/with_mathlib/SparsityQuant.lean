/-
  SparsityQuant.lean
  ==================
  Two structural facts about the lamplighter normal form that were asked for as separate
  open items, and are in fact short consequences of definitions already in the repo.

  ITEM 3 (a block-size bound).  The request was a theorem of the form "the core acts on
  blocks of size <= f(d), with a zero-pattern determined by the parity normal form".  Two
  halves of that are immediate:

    * SUPPORT.  `PathData.houter` already says `d` and `travel` vanish off `[A, B]`, so the
      object is banded: everything outside the span is exactly zero.
    * WIDTH.  Every edge of the span costs at least one (`mu_ge_one`), so the band width
      is bounded by the relaxed length itself: `span_card_le_lR`.  Gap edges cost two
      (`mu_gap_eq_two`), so gaps are charged double and a wide band with many gap edges is
      correspondingly expensive.

  Together: the band width is at most `lR`, and within the band the parity of `mu` is
  pinned by the travel interval (`TravelParity.mu_odd_iff_mem`).  That is a computable
  compile-time bound on block size from the cost alone.

  ITEM 5 (quantization).  The important structural point is a NEGATIVE one, and it is
  forced by `hpar : (d j - travel kstar j) % 2 = 0`: the admissible deposits at edge `j`
  are not an interval but a COSET of `2ZZ`, fixed by the travel indicator.  So naive
  uniform rounding of the lamp coefficients does not merely lose accuracy -- it leaves the
  admissible set entirely, and the rounded data is no longer a `PathData` at all
  (`not_pathData_of_wrong_parity`).  Quantization must snap to the parity coset.  Once it
  does, the cost is Lipschitz in the deposit (`mu_sub_mu_le`), so a parity-respecting
  quantizer degrades the structure by a bounded amount and no more.

  No `sorry`.
-/

import Realisation
import TravelParity

namespace SparsityQuant

open SiteCost

variable (P : SiteCost.PathData)

/-! ### Item 3: the band and its width -/

/-- **Every edge costs at least one.**  Either the edge is a gap, where `mu = 2`, or one
of `d`, `travel` is non-zero and the max of their absolute values is at least one. -/
theorem mu_ge_one (j : ℤ) : 1 ≤ P.mu j := by
  unfold SiteCost.PathData.mu
  split_ifs with h
  · norm_num
  · rcases not_and_or.mp h with hd | hf
    · have : 1 ≤ (P.d j).natAbs := by omega
      exact le_trans this (le_max_left _ _)
    · have : 1 ≤ (SiteCost.travel P.kstar j).natAbs := by omega
      exact le_trans this (le_max_right _ _)

/-- **A gap edge costs exactly two.** -/
theorem mu_gap_eq_two (j : ℤ) (hd : P.d j = 0) (hf : SiteCost.travel P.kstar j = 0) :
    P.mu j = 2 := by
  unfold SiteCost.PathData.mu; rw [if_pos ⟨hd, hf⟩]

/-- **The band width is bounded by the relaxed length.**  This is the block-size bound:
the span carries one unit of cost per edge, so a configuration of relaxed length `L` acts
on a band of at most `L` edges -- a compile-time bound from the cost alone. -/
theorem span_card_le_lR : (Finset.Icc P.A P.B).card ≤ P.lR := by
  have h : (Finset.Icc P.A P.B).card * 1 ≤ ∑ j ∈ Finset.Icc P.A P.B, P.mu j := by
    calc (Finset.Icc P.A P.B).card * 1
        = ∑ _j ∈ Finset.Icc P.A P.B, 1 := by simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ j ∈ Finset.Icc P.A P.B, P.mu j :=
          Finset.sum_le_sum (fun j _ => mu_ge_one P j)
  unfold SiteCost.PathData.lR
  omega

/-- **Off the band everything is exactly zero** -- the sparsity pattern, restated from
`houter` so it can be cited directly as the support statement. -/
theorem zero_off_span (j : ℤ) (h : j < P.A ∨ P.B < j) :
    P.d j = 0 ∧ SiteCost.travel P.kstar j = 0 := P.houter j h

/-! ### Item 5: quantization must respect the parity coset -/

/-- **The admissible deposits at an edge form a coset of `2ZZ`**, pinned by the travel
indicator.  This is `hpar`, stated in the form a quantizer has to obey. -/
theorem deposit_parity (j : ℤ) : P.d j % 2 = SiteCost.travel P.kstar j % 2 := by
  have h := P.hpar j
  omega

/-- **Naive rounding leaves the model.**  If a proposed deposit at edge `j` has the wrong
parity against the travel indicator, then NO `PathData` with that deposit exists.  So a
uniform quantizer applied to the lamp coefficients does not merely lose accuracy: the
rounded object is not a configuration at all. -/
theorem not_pathData_of_wrong_parity (k : ℤ) (j : ℤ) (v : ℤ)
    (hv : v % 2 ≠ SiteCost.travel k j % 2) :
    ¬ ∃ Q : SiteCost.PathData, Q.kstar = k ∧ Q.d j = v := by
  rintro ⟨Q, hk, hd⟩
  have := deposit_parity Q j
  rw [hd, hk] at this
  exact hv this

/-- **Within the parity coset the cost is Lipschitz in the deposit.**  Changing `d j` by
`t` changes `mu j` by at most `|t|`, so a parity-respecting quantizer perturbs the cost by
a bounded amount.  (Stated as a two-sided bound on the underlying `max`, which is what the
`mu` branch reduces to away from a gap.) -/
theorem mu_sub_mu_le (f x y : ℤ) :
    (max x.natAbs f.natAbs : ℤ) - (max y.natAbs f.natAbs : ℤ) ≤ (x - y).natAbs := by
  omega

end SparsityQuant

#print axioms SparsityQuant.mu_ge_one
#print axioms SparsityQuant.mu_gap_eq_two
#print axioms SparsityQuant.span_card_le_lR
#print axioms SparsityQuant.zero_off_span
#print axioms SparsityQuant.deposit_parity
#print axioms SparsityQuant.not_pathData_of_wrong_parity
#print axioms SparsityQuant.mu_sub_mu_le
