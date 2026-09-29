/-
M3SpanBounds.lean
=================
Formalises the structural bounds on `ATrue` and `BTrue` arising from the travel
range — the "containment half" of M3:lem:span from
`paper/journal/merged_novel_paper.tex`.

M3:lem:span states A = k₋ - ℓ, B = k₊ - 1 + r (where k₋ = min(0, kstar),
k₊ = max(0, kstar), ℓ = left chain length, r = right chain length).  The full
identity requires defining chain lengths; we formalise the weaker but
immediately provable BOUNDS:

  kstar > 0 → ATrue g ≤ 0  and  kstar - 1 ≤ BTrue g
  kstar < 0 → ATrue g ≤ kstar  and  -1 ≤ BTrue g

These follow purely from the fact that the travel range lies inside occTrue:
  kstar > 0 → {0, …, kstar - 1} ⊆ occTrue g
  kstar < 0 → {kstar, …, -1} ⊆ occTrue g

No sorry.
-/

import CorrectedSpan

namespace M3SpanBounds

open EltBridge SiteCost CorrectedSpan

variable (g : EltBridge.Elt)

/-! ## Travel values at the boundary indices of the travel range -/

theorem travel_pos_zero (kstar : ℤ) (hk : 0 < kstar) : travel kstar 0 = 1 := by
  unfold travel; split_ifs <;> omega

theorem travel_pos_pred (kstar : ℤ) (hk : 0 < kstar) : travel kstar (kstar - 1) = 1 := by
  unfold travel; split_ifs <;> omega

theorem travel_neg_neg_one (kstar : ℤ) (hk : kstar < 0) : travel kstar (-1) = -1 := by
  unfold travel; split_ifs <;> omega

theorem travel_neg_kstar_self (kstar : ℤ) (hk : kstar < 0) : travel kstar kstar = -1 := by
  unfold travel; split_ifs <;> omega

/-! ## If travel ≠ 0 at j then j ∈ occTrue -/

theorem mem_supp_of_travel_ne (j : ℤ) (h : SiteCost.travel g.kstar j ≠ 0) : j ∈ g.supp := by
  by_contra hj
  exact h (g.hsupp j hj).2

theorem mem_occTrue_of_travel_ne (j : ℤ) (h : SiteCost.travel g.kstar j ≠ 0) :
    j ∈ occTrue g := by
  unfold occTrue
  exact Finset.mem_filter.mpr ⟨mem_supp_of_travel_ne g j h, Or.inr h⟩

/-! ## For kstar > 0: 0 and kstar - 1 lie in occTrue -/

theorem zero_mem_occTrue_of_pos_kstar (hk : 0 < g.kstar) : 0 ∈ occTrue g :=
  mem_occTrue_of_travel_ne g 0 (by rw [travel_pos_zero g.kstar hk]; norm_num)

theorem pred_kstar_mem_occTrue_of_pos_kstar (hk : 0 < g.kstar) : g.kstar - 1 ∈ occTrue g :=
  mem_occTrue_of_travel_ne g (g.kstar - 1) (by rw [travel_pos_pred g.kstar hk]; norm_num)

/-! ## ATrue ≤ 0 and kstar - 1 ≤ BTrue when kstar > 0 -/

/-- M3:lem:span (lower bound): when kstar > 0, ATrue g ≤ 0. -/
theorem ATrue_le_zero_of_pos_kstar (hk : 0 < g.kstar) : ATrue g ≤ 0 := by
  have hmem : 0 ∈ occTrue g := zero_mem_occTrue_of_pos_kstar g hk
  have hne : (occTrue g).Nonempty := ⟨0, hmem⟩
  unfold ATrue; rw [dif_pos hne]
  exact min_le_left 0 _

/-- M3:lem:span (upper bound): when kstar > 0, kstar - 1 ≤ BTrue g. -/
theorem pred_kstar_le_BTrue_of_pos_kstar (hk : 0 < g.kstar) : g.kstar - 1 ≤ BTrue g := by
  have hmem₀ : 0 ∈ occTrue g := zero_mem_occTrue_of_pos_kstar g hk
  have hne : (occTrue g).Nonempty := ⟨0, hmem₀⟩
  have hmem₁ : g.kstar - 1 ∈ occTrue g := pred_kstar_mem_occTrue_of_pos_kstar g hk
  unfold BTrue; rw [dif_pos hne]
  calc g.kstar - 1
      ≤ (occTrue g).max' hne := Finset.le_max' _ _ hmem₁
    _ ≤ max (-1) ((occTrue g).max' hne) := le_max_right _ _

/-! ## For kstar < 0: kstar and -1 lie in occTrue -/

theorem kstar_mem_occTrue_of_neg_kstar (hk : g.kstar < 0) : g.kstar ∈ occTrue g :=
  mem_occTrue_of_travel_ne g g.kstar (by rw [travel_neg_kstar_self g.kstar hk]; norm_num)

theorem neg_one_mem_occTrue_of_neg_kstar (hk : g.kstar < 0) : -1 ∈ occTrue g :=
  mem_occTrue_of_travel_ne g (-1) (by rw [travel_neg_neg_one g.kstar hk]; norm_num)

/-! ## ATrue ≤ kstar and -1 ≤ BTrue when kstar < 0 -/

/-- M3:lem:span (lower bound): when kstar < 0, ATrue g ≤ kstar. -/
theorem ATrue_le_kstar_of_neg_kstar (hk : g.kstar < 0) : ATrue g ≤ g.kstar := by
  have hmem_n : -1 ∈ occTrue g := neg_one_mem_occTrue_of_neg_kstar g hk
  have hne : (occTrue g).Nonempty := ⟨-1, hmem_n⟩
  have hmem_k : g.kstar ∈ occTrue g := kstar_mem_occTrue_of_neg_kstar g hk
  unfold ATrue; rw [dif_pos hne]
  calc min 0 ((occTrue g).min' hne)
      ≤ (occTrue g).min' hne := min_le_right 0 _
    _ ≤ g.kstar := Finset.min'_le _ _ hmem_k

/-- M3:lem:span (upper bound): when kstar < 0, -1 ≤ BTrue g. -/
theorem neg_one_le_BTrue_of_neg_kstar (hk : g.kstar < 0) : (-1 : ℤ) ≤ BTrue g := by
  have hmem_n : -1 ∈ occTrue g := neg_one_mem_occTrue_of_neg_kstar g hk
  have hne : (occTrue g).Nonempty := ⟨-1, hmem_n⟩
  unfold BTrue; rw [dif_pos hne]
  exact le_max_left (-1) _

end M3SpanBounds

-- Rule 5 axiom audit.
#print axioms M3SpanBounds.ATrue_le_zero_of_pos_kstar
#print axioms M3SpanBounds.pred_kstar_le_BTrue_of_pos_kstar
#print axioms M3SpanBounds.ATrue_le_kstar_of_neg_kstar
#print axioms M3SpanBounds.neg_one_le_BTrue_of_neg_kstar
