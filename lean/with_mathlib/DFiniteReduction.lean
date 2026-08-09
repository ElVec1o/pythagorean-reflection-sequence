/-
  DFiniteReduction.lean
  =====================
  Paper "extra", Proposition `prop:no-dfinite`: the reduction of the 52-pair search grid to
  its six maximal pairs.

  A D-finite recurrence of order k with coefficient polynomials of degree m is a nonzero
  family (c_{j,t}) with

      sum_{j <= k} sum_{t <= m} c_{j,t} n^t u_{n-j} = 0    for every n with k <= n <= 42.

  The grid searched by the proposition is the 52 pairs (k, m) with 1 <= k <= 9, m <= 7 and
  (k+1)(m+1) < 43 - k.  Checking all 52 is unnecessary.  If (k, m) <= (k', m') componentwise
  then a nonzero (k, m)-recurrence yields a nonzero (k', m')-recurrence, by padding the
  coefficient family with zeros.  Two facts make the padding work:

    * the ansatz grows, since polynomials of degree <= m have degree <= m' and the indices
      j <= k are among the j <= k';
    * the CONSTRAINTS SHRINK, since the (k', m') equations run over k' <= n <= 42 and, as
      k <= k', that range is contained in the range k <= n <= 42 of the (k, m) equations.

  So non-existence at (k', m') implies non-existence at (k, m), and it suffices to certify
  the maximal pairs.  The grid has exactly six:

      (3,7), (4,6), (5,5), (6,4), (7,3), (9,2),

  and `grid_covered` below checks by kernel evaluation that every one of the 52 is dominated
  by one of them.  The reduction cuts the certificate data by a factor of eight and the
  verification work from 52 rank certificates to 6.

  WHAT THIS FILE DOES AND DOES NOT DO.  The reduction is proved here in full and
  unconditionally.  The six base cases are NOT discharged here: their rank certificates are
  generated and self-checked by `code/zeta_probe/tools/nodfinite`, and importing them into
  Lean needs the step from a modular left inverse to `det M /= 0` over the integers, which is
  not in this file.  Proposition `prop:no-dfinite` is therefore reduced, not yet closed, and
  the paper says so.
-/

import Mathlib

namespace DFiniteReduction

open Finset

/-! ### The sequence -/

/-- A396406, `u_0, ..., u_42`.  The last four terms are recorded in
    `code/data/u_terms_43.txt`, with their provenance. -/
def uList : List Int :=
  [1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066, 3203, 4971, 7574,
   11543, 17683, 27108, 41067, 62263, 94622, 143881, 217101, 327832, 495443, 749195, 1127236,
   1697179, 2554961, 3848384, 5777651, 8679441, 13031206, 19574659, 29338781, 43997388,
   65932461, 98849591, 147969934]

def u (n : Nat) : Int := uList.getD n 0

/-! ### The search grid and its maximal elements -/

/-- The over-determination condition of the proposition. -/
def onGrid (k m : Nat) : Bool :=
  decide (1 ≤ k) && decide (k ≤ 9) && decide (m ≤ 7) && decide ((k + 1) * (m + 1) < 43 - k)

/-- The six maximal pairs. -/
def maximalPairs : List (Nat × Nat) := [(3, 7), (4, 6), (5, 5), (6, 4), (7, 3), (9, 2)]

theorem grid_size :
    ((List.range 10).flatMap (fun k => (List.range 8).map (fun m => (k, m)))).countP
      (fun p => onGrid p.1 p.2) = 52 := by decide

/-- **Every grid pair is dominated by a maximal one.** -/
theorem grid_covered :
    ∀ k, k < 10 → ∀ m, m < 8 → onGrid k m = true →
      maximalPairs.any (fun p => decide (k ≤ p.1) && decide (m ≤ p.2)) = true := by decide

/-- Each maximal pair is itself on the grid. -/
theorem maximal_on_grid : maximalPairs.all (fun p => onGrid p.1 p.2) = true := by decide

/-! ### Recurrences -/

/-- `c` is a coefficient family for an order-`k`, degree-`m` recurrence satisfied on the
    available terms. -/
def Sol (k m : Nat) (c : Nat → Nat → Rat) : Prop :=
  ∀ n, k ≤ n → n ≤ 42 →
    ∑ j ∈ range (k + 1), ∑ t ∈ range (m + 1),
      c j t * (n : Rat) ^ t * ((u (n - j) : Int) : Rat) = 0

/-- `c` is not the zero family, within the `(k, m)` box. -/
def Nz (k m : Nat) (c : Nat → Nat → Rat) : Prop :=
  ∃ j ∈ range (k + 1), ∃ t ∈ range (m + 1), c j t ≠ 0

/-- Zero-padding of a coefficient family outside the `(k, m)` box. -/
def pad (k m : Nat) (c : Nat → Nat → Rat) : Nat → Nat → Rat :=
  fun j t => if j < k + 1 ∧ t < m + 1 then c j t else 0

/-- The padded family agrees with `c` inside the box. -/
theorem pad_inside {k m j t : Nat} (c : Nat → Nat → Rat)
    (hj : j < k + 1) (ht : t < m + 1) : pad k m c j t = c j t := by
  simp [pad, hj, ht]

/-- **The padded family solves the larger system.**  The inner sums collapse to the smaller
    box because the padding vanishes outside it, and the outer range of `n` is smaller, so the
    original equations cover it. -/
theorem pad_sol {k k' m m' : Nat} (hk : k ≤ k') (hm : m ≤ m')
    {c : Nat → Nat → Rat} (hc : Sol k m c) : Sol k' m' (pad k m c) := by
  intro n hn hn42
  have hkn : k ≤ n := le_trans hk hn
  have hsub_k : range (k + 1) ⊆ range (k' + 1) := by
    intro j hj; simp only [mem_range] at hj ⊢; omega
  have hsub_m : range (m + 1) ⊆ range (m' + 1) := by
    intro t ht; simp only [mem_range] at ht ⊢; omega
  have inner : ∀ j : Nat,
      ∑ t ∈ range (m' + 1), pad k m c j t * (n : Rat) ^ t * ((u (n - j) : Int) : Rat)
        = ∑ t ∈ range (m + 1), pad k m c j t * (n : Rat) ^ t * ((u (n - j) : Int) : Rat) := by
    intro j
    refine (Finset.sum_subset hsub_m ?_).symm
    intro t _ htn
    simp only [mem_range, not_lt] at htn
    have h0 : pad k m c j t = 0 := by
      unfold pad
      have hno : ¬ (j < k + 1 ∧ t < m + 1) := by omega
      rw [if_neg hno]
    rw [h0]; ring
  rw [Finset.sum_congr rfl (fun j _ => inner j)]
  have outer :
      ∑ j ∈ range (k' + 1), ∑ t ∈ range (m + 1),
          pad k m c j t * (n : Rat) ^ t * ((u (n - j) : Int) : Rat)
        = ∑ j ∈ range (k + 1), ∑ t ∈ range (m + 1),
            pad k m c j t * (n : Rat) ^ t * ((u (n - j) : Int) : Rat) := by
    refine (Finset.sum_subset hsub_k ?_).symm
    intro j _ hjn
    simp only [mem_range, not_lt] at hjn
    refine Finset.sum_eq_zero (fun t _ => ?_)
    have h0 : pad k m c j t = 0 := by
      unfold pad
      have hno : ¬ (j < k + 1 ∧ t < m + 1) := by omega
      rw [if_neg hno]
    rw [h0]; ring
  rw [outer, ← hc n hkn hn42]
  refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun t ht => ?_))
  simp only [mem_range] at hj ht
  rw [pad_inside c hj ht]

/-- **The padded family is still nonzero.** -/
theorem pad_nz {k k' m m' : Nat} (hk : k ≤ k') (hm : m ≤ m')
    {c : Nat → Nat → Rat} (hc : Nz k m c) : Nz k' m' (pad k m c) := by
  obtain ⟨j, hj, t, ht, hne⟩ := hc
  simp only [mem_range] at hj ht
  refine ⟨j, by simp only [mem_range]; omega, t, by simp only [mem_range]; omega, ?_⟩
  rw [pad_inside c hj ht]
  exact hne

/-- **The reduction.**  If no nontrivial recurrence exists at `(k', m')`, none exists at any
    `(k, m)` below it. -/
theorem no_sol_mono {k k' m m' : Nat} (hk : k ≤ k') (hm : m ≤ m')
    (h : ¬ ∃ c, Sol k' m' c ∧ Nz k' m' c) :
    ¬ ∃ c, Sol k m c ∧ Nz k m c := by
  rintro ⟨c, hsol, hnz⟩
  exact h ⟨pad k m c, pad_sol hk hm hsol, pad_nz hk hm hnz⟩

/-- **`prop:no-dfinite` reduced to six base cases.**  Granted non-existence at each maximal
    pair, no grid pair admits a nontrivial recurrence.  The hypothesis is exactly what the six
    rank certificates supply. -/
theorem no_dfinite_of_maximal
    (hmax : ∀ p ∈ maximalPairs, ¬ ∃ c, Sol p.1 p.2 c ∧ Nz p.1 p.2 c)
    (k m : Nat) (hk : k < 10) (hm : m < 8) (hgrid : onGrid k m = true) :
    ¬ ∃ c, Sol k m c ∧ Nz k m c := by
  have hcov := grid_covered k hk m hm hgrid
  rw [List.any_eq_true] at hcov
  obtain ⟨p, hp, hle⟩ := hcov
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hle
  exact no_sol_mono hle.1 hle.2 (hmax p hp)

/-! ### Axiom audit (Rule 5) -/

#print axioms grid_size
#print axioms grid_covered
#print axioms maximal_on_grid
#print axioms pad_sol
#print axioms pad_nz
#print axioms no_sol_mono
#print axioms no_dfinite_of_maximal

end DFiniteReduction
