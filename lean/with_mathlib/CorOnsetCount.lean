/-
CorOnsetCount.lean
==================

The counting half of Corollary `cor:onset` of `paper/journal/paper4.tex`: "the stratum
carries `d^2-1` relations at depth `m+m/d`."

`RotationRelations.lean` proves `admissible_count : pairCount n n = (n-1)*(n-1)` by a
hand-rolled recursion on `Nat`, not as a `Finset.card`. `Bridge.lean`'s
`unique_finite_order` is a per-pair `iff`, not a count. Neither on its own gives the
sentence "exactly one of the `(n-1)^2` admissible pairs has finite order, so `(n-1)^2-1`
do not" -- that needs a `Finset`-cardinality argument bridging the two, which is built
here from scratch (independent of `pairCount`, so this is also a second, independent
count of the same combinatorial fact).

What this file does NOT do: connect "infinite order in the abstract group `W_m`" to an
actual geodesic/word-length coincidence in the reflection group. That translation step
(needed for the full statement of `cor:onset`) was not located in this development and is
not attempted here.

No `sorry`.
-/

import Bridge

namespace CoxeterTorsion

open RotationRelations

/-- The admissible index pairs `(a, j)` with `a, j < n`, as a `Finset`, matching
`RotationRelations.Admissible` exactly. -/
def admPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter (fun p => p.2 ≠ p.1 ∧ p.1 ≠ p.2 + 1)

theorem mem_admPairs {n a j : ℕ} : (a, j) ∈ admPairs n ↔ Admissible n a j := by
  unfold admPairs Admissible
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  tauto

/-- The two excluded diagonals, and their union with `admPairs n`, partition the full
square `range n ×ˢ range n`. -/
private def diagPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter (fun p => p.2 = p.1)

private def offPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 = p.2 + 1)

private theorem diagPairs_card (n : ℕ) : (diagPairs n).card = n := by
  rw [show diagPairs n = (Finset.range n).image (fun a => (a, a)) from ?_]
  · rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq .. |>.mp h).1)]
    exact Finset.card_range n
  · ext ⟨a, j⟩
    simp only [diagPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_image, Prod.ext_iff]
    constructor
    · rintro ⟨⟨ha, hj⟩, heq⟩; exact ⟨a, ha, rfl, heq.symm⟩
    · rintro ⟨a', ha', heq1, heq2⟩; omega

private theorem offPairs_card (n : ℕ) : (offPairs n).card = n - 1 := by
  rw [show offPairs n = (Finset.range (n - 1)).image (fun j => (j + 1, j)) from ?_]
  · rw [Finset.card_image_of_injective _ (fun a b h => by
      have h' := Prod.ext_iff.mp h; omega)]
    exact Finset.card_range (n - 1)
  · ext ⟨a, j⟩
    simp only [offPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_image, Prod.ext_iff]
    constructor
    · rintro ⟨⟨ha, hj⟩, heq⟩; exact ⟨j, by omega, heq.symm, rfl⟩
    · rintro ⟨j', hj', heq1, heq2⟩; omega

/-- **The admissible-pair count, as a `Finset.card`.** Independent of `pairCount`:
`admPairs n`, `diagPairs n` (`j = a`) and `offPairs n` (`a = j + 1`) partition the full
square `range n ×ˢ range n`, and the latter two are disjoint from each other
(`j = a` and `a = j + 1` together would force `a = a + 1`). -/
theorem admPairs_card (n : ℕ) : (admPairs n).card = (n - 1) * (n - 1) := by
  have hpart : admPairs n ∪ diagPairs n ∪ offPairs n = Finset.range n ×ˢ Finset.range n := by
    ext ⟨a, j⟩
    simp only [admPairs, diagPairs, offPairs, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range]
    tauto
  have hd1 : Disjoint (admPairs n) (diagPairs n) := by
    rw [Finset.disjoint_left]; rintro ⟨a, j⟩ h1 h2
    simp only [admPairs, diagPairs, Finset.mem_filter] at h1 h2; tauto
  have hd2 : Disjoint (admPairs n) (offPairs n) := by
    rw [Finset.disjoint_left]; rintro ⟨a, j⟩ h1 h2
    simp only [admPairs, offPairs, Finset.mem_filter] at h1 h2; tauto
  have hd3 : Disjoint (diagPairs n) (offPairs n) := by
    rw [Finset.disjoint_left]; rintro ⟨a, j⟩ h1 h2
    simp only [diagPairs, offPairs, Finset.mem_filter] at h1 h2; omega
  have hcard : (admPairs n).card + (diagPairs n).card + (offPairs n).card
      = (Finset.range n ×ˢ Finset.range n).card := by
    rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_union_left]; exact ⟨hd2, hd3⟩), hpart]
  rw [Finset.card_product, Finset.card_range, diagPairs_card,
    offPairs_card] at hcard
  rcases n with _ | n
  · simp_all
  · rcases n with _ | n
    · simp_all
    · simp only [Nat.succ_sub_one] at hcard ⊢
      have hexpand : (n + 1 + 1) * (n + 1 + 1) = (n + 1) * (n + 1) + (n + 2) + (n + 1) := by
        ring
      rw [hexpand] at hcard
      omega

open Classical in
noncomputable def infOrderPairs (m n : ℕ) : Finset (ℕ × ℕ) :=
  (admPairs n).filter (fun p => ¬ IsOfFinOrder (ev m (markBoth n p.1 p.2)))

/-- **The counting half of `cor:onset`.** Among the `(n-1)^2` admissible pairs of index
`n = c + 1` (`c` the stratum's `Theorem thm:rot` parameter, and `m` any modulus with
`n <= m`), exactly one -- `(a, j) = (0, n-1)` -- gives a word of finite order in
`W_m = D_m * C_2` (`Bridge.unique_finite_order`); the remaining `(n-1)^2 - 1` give
words of infinite order, i.e. genuine coincidences at the stratum's depth. This is the
count `d^2 - 1` of `cor:onset` with `d = n - 1`. Needs `n >= 2` (else `(0, n-1)` is not
itself admissible: at `n = 1` it is `(0, 0)`, excluded by `j != a`). -/
theorem infiniteOrder_count (m n : ℕ) (hnm : n ≤ m) (hn : 2 ≤ n) :
    (infOrderPairs m n).card = (n - 1) * (n - 1) - 1 := by
  have hmem : ((0, n - 1) : ℕ × ℕ) ∈ admPairs n := by
    rw [mem_admPairs]; refine ⟨by omega, by omega, by omega, by omega⟩
  have hfilt : infOrderPairs m n = admPairs n \ {((0, n - 1) : ℕ × ℕ)} := by
    unfold infOrderPairs
    ext ⟨a, j⟩
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨ham, hne⟩
      refine ⟨ham, fun h => hne ?_⟩
      rw [mem_admPairs] at ham
      exact (unique_finite_order m n a j hnm ham).mpr h
    · rintro ⟨ham, hne⟩
      rw [mem_admPairs] at ham
      refine ⟨mem_admPairs.mpr ham, fun hfin => hne ?_⟩
      exact (unique_finite_order m n a j hnm ham).mp hfin
  rw [hfilt, Finset.card_sdiff, Finset.singleton_inter_of_mem hmem, Finset.card_singleton,
    admPairs_card]

end CoxeterTorsion

-- Rule 5 axiom audit.
#print axioms CoxeterTorsion.admPairs_card
#print axioms CoxeterTorsion.infiniteOrder_count
