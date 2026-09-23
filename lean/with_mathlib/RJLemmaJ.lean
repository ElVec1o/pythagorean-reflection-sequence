/-
  RJLemmaJ.lean -- room 62. Lemma J (junction cut characterisation) and the bulk-site
  cut rule, proved against the actual `SiteCost.PathData.cut` of Realisation.lean,
  plus the reduction of `CorrectedSpan.cTrue` for `kstar ≠ 0` to a count of sites
  satisfying the explicit characterisation.  No sorry, no native_decide.
-/
import CorrectedSpan

namespace RJLemmaJ
open SiteCost

variable (P : PathData)

/-- Fully unfolded form of `cut`. -/
theorem cut_unfold (s : ℤ) :
    P.cut s ↔
      (P.d (s - 1) - (if s = 0 then 1 else 0)
          + P.eps * (if P.delta then 0 else if s = P.kstar then 1 else 0) = 0 ∧
       P.d s - P.eps * (if P.delta then (if s = P.kstar then 1 else 0) else 0) = 0 ∧
       travel P.kstar (s - 1) + (if s = 0 then 1 else 0)
          - (if P.delta then 0 else if s = P.kstar then 1 else 0) = 0) := by
  unfold PathData.cut PathData.alphaAt PathData.betaAt PathData.PhiAt PathData.f
    PathData.vL PathData.vR PathData.vD vArr
  cases P.delta <;> by_cases h0 : s = 0 <;> by_cases hk : s = P.kstar <;> simp [h0, hk]

/-- Lemma J (a): site 0 is never cut when `kstar > 0`. -/
theorem J_site0_pos (hk : 0 < P.kstar) : ¬ P.cut 0 := by
  rw [cut_unfold]
  have h1 : (0:ℤ) ≠ P.kstar := by omega
  have ht : travel P.kstar (0 - 1) = 0 := by unfold travel; split_ifs <;> omega
  rintro ⟨-, -, h⟩
  rw [ht] at h
  cases P.delta <;> simp [h1] at h

/-- Lemma J (b): for `kstar < 0`, site 0 is cut iff `d(-1) = 1` and `d 0 = 0`. -/
theorem J_site0_neg (hk : P.kstar < 0) : P.cut 0 ↔ P.d (-1) = 1 ∧ P.d 0 = 0 := by
  rw [cut_unfold]
  have h1 : (0:ℤ) ≠ P.kstar := by omega
  have ht : travel P.kstar (0 - 1) = -1 := by unfold travel; split_ifs <;> omega
  rw [ht]
  cases P.delta <;> simp [h1] <;> omega

/-- Lemma J (c): for `kstar > 0`, site `kstar` is cut iff `delta = 0`,
`d(kstar-1) = -eps` and `d kstar = 0`. -/
theorem J_sitek_pos (hk : 0 < P.kstar) :
    P.cut P.kstar ↔ P.delta = false ∧ P.d (P.kstar - 1) = -P.eps ∧ P.d P.kstar = 0 := by
  rw [cut_unfold]
  have h1 : P.kstar ≠ 0 := by omega
  have ht : travel P.kstar (P.kstar - 1) = 1 := by unfold travel; split_ifs <;> omega
  rw [ht]
  cases P.delta <;> simp [h1] <;> omega

/-- Lemma J (d): for `kstar < 0`, site `kstar` is cut iff `delta = 1`,
`d kstar = eps` and `d(kstar-1) = 0`. -/
theorem J_sitek_neg (hk : P.kstar < 0) :
    P.cut P.kstar ↔ P.delta = true ∧ P.d P.kstar = P.eps ∧ P.d (P.kstar - 1) = 0 := by
  rw [cut_unfold]
  have h1 : P.kstar ≠ 0 := by omega
  have ht : travel P.kstar (P.kstar - 1) = 0 := by unfold travel; split_ifs <;> omega
  rw [ht]
  cases P.delta <;> simp [h1] <;> omega

/-- Bulk sites: for `s ∉ {0, kstar}`, `s` is cut iff `d(s-1) = d s = 0` and the site is
off-travel (`travel kstar (s-1) = 0`). -/
theorem bulk_cut (s : ℤ) (h0 : s ≠ 0) (hk : s ≠ P.kstar) :
    P.cut s ↔ P.d (s - 1) = 0 ∧ P.d s = 0 ∧ travel P.kstar (s - 1) = 0 := by
  rw [cut_unfold]
  cases P.delta <;> simp [h0, hk]

/-- Off-travel, stated explicitly: for `s ∉ {0, kstar}`, `travel kstar (s-1) = 0` iff
`s` lies outside the travel range (`s ∉ (0, kstar]` and `s ∉ (kstar, 0]`). -/
theorem offTravel_iff (s : ℤ) :
    travel P.kstar (s - 1) = 0 ↔ ¬ (0 < s ∧ s ≤ P.kstar) ∧ ¬ (P.kstar < s ∧ s ≤ 0) := by
  unfold travel
  by_cases h1 : 0 ≤ s - 1 ∧ s - 1 < P.kstar
  · rw [if_pos h1]; constructor
    · intro h; omega
    · rintro ⟨h, -⟩; exact absurd ⟨by omega, by omega⟩ h
  · rw [if_neg h1]
    by_cases h2 : P.kstar ≤ s - 1 ∧ s - 1 < 0
    · rw [if_pos h2]; constructor
      · intro h; omega
      · rintro ⟨-, h⟩; exact absurd ⟨by omega, by omega⟩ h
    · rw [if_neg h2]
      exact ⟨fun _ => ⟨fun h => h1 ⟨by omega, by omega⟩, fun h => h2 ⟨by omega, by omega⟩⟩,
        fun _ => rfl⟩

open Classical in
/-- The explicit characterisation (Lemma J + bulk rule), as a single predicate. -/
noncomputable def cutChar (s : ℤ) : Prop :=
  if s = 0 then
    (P.kstar < 0 ∧ P.d (-1) = 1 ∧ P.d 0 = 0)
      ∨ (P.kstar = 0 ∧ P.cut 0)
  else if s = P.kstar then
    (0 < P.kstar ∧ P.delta = false ∧ P.d (P.kstar - 1) = -P.eps ∧ P.d P.kstar = 0) ∨
    (P.kstar < 0 ∧ P.delta = true ∧ P.d P.kstar = P.eps ∧ P.d (P.kstar - 1) = 0)
  else
    P.d (s - 1) = 0 ∧ P.d s = 0 ∧ travel P.kstar (s - 1) = 0

theorem cut_iff_cutChar (s : ℤ) : P.cut s ↔ cutChar P s := by
  unfold cutChar
  by_cases h0 : s = 0
  · subst h0
    rw [if_pos rfl]
    rcases lt_trichotomy P.kstar 0 with hk | hk | hk
    · rw [J_site0_neg P hk]; constructor
      · intro h; exact Or.inl ⟨hk, h⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · omega
    · constructor
      · intro h; exact Or.inr ⟨hk, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · omega
        · exact h
    · constructor
      · intro h; exact absurd h (J_site0_pos P hk)
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega
  · rw [if_neg h0]
    by_cases hk : s = P.kstar
    · rw [if_pos hk]; subst hk
      rcases lt_or_gt_of_ne h0 with hn | hp
      · rw [J_sitek_neg P hn]; constructor
        · intro h; exact Or.inr ⟨hn, h⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · omega
          · exact h
      · rw [J_sitek_pos P hp]; constructor
        · intro h; exact Or.inl ⟨hp, h⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact h
          · omega
    · rw [if_neg hk]; exact bulk_cut P s h0 hk

open Classical in
/-- Corollary (finite form): for `kstar ≠ 0` the boundary shield never fires, and
`cTrue` is exactly the number of sites in the open corrected span `(ATrue, BTrue+1)`
satisfying the explicit characterisation `cutChar`. -/
theorem cTrue_eq_cutChar_count (g : EltBridge.Elt) (hk : g.kstar ≠ 0) :
    CorrectedSpan.cTrue g =
      ((Finset.Ioo (CorrectedSpan.ATrue g) (CorrectedSpan.BTrue g + 1)).filter
        (fun s => cutChar g.toPathData s)).card := by
  classical
  unfold CorrectedSpan.cTrue
  rw [if_neg (fun h => hk h.1.1), add_zero]
  congr 1
  exact Finset.filter_congr (fun s _ => cut_iff_cutChar _ s)

open Classical in
/-- Bulk-only corollary: for `kstar ≠ 0`, every counted cut outside `{0, kstar}` is a
site with zero deposits on both sides and off-travel -- i.e. an interior gap site. -/
theorem cTrue_bulk_part (g : EltBridge.Elt) (hk : g.kstar ≠ 0) :
    CorrectedSpan.cTrue g =
      ((Finset.Ioo (CorrectedSpan.ATrue g) (CorrectedSpan.BTrue g + 1)).filter
        (fun s => s ≠ 0 ∧ s ≠ g.kstar ∧ g.d (s-1) = 0 ∧ g.d s = 0 ∧
           travel g.kstar (s-1) = 0)).card
      + ((Finset.Ioo (CorrectedSpan.ATrue g) (CorrectedSpan.BTrue g + 1)).filter
        (fun s => (s = 0 ∨ s = g.kstar) ∧ g.toPathData.cut s)).card := by
  classical
  unfold CorrectedSpan.cTrue
  rw [if_neg (fun h => hk h.1.1), add_zero]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hs, hc⟩
      by_cases h : s = 0 ∨ s = g.kstar
      · exact Or.inr ⟨hs, h, hc⟩
      · push Not at h
        have := (bulk_cut g.toPathData s h.1 h.2).1 hc
        exact Or.inl ⟨hs, h.1, h.2, this⟩
    · rintro (⟨hs, h0, hk', hb⟩ | ⟨hs, -, hc⟩)
      · exact ⟨hs, (bulk_cut g.toPathData s h0 hk').2 hb⟩
      · exact ⟨hs, hc⟩
  · rw [Finset.disjoint_filter]
    rintro s - ⟨h0, hk', -⟩ ⟨h | h, -⟩ <;> contradiction

end RJLemmaJ

#print axioms RJLemmaJ.cut_unfold
#print axioms RJLemmaJ.J_site0_pos
#print axioms RJLemmaJ.J_site0_neg
#print axioms RJLemmaJ.J_sitek_pos
#print axioms RJLemmaJ.J_sitek_neg
#print axioms RJLemmaJ.bulk_cut
#print axioms RJLemmaJ.offTravel_iff
#print axioms RJLemmaJ.cut_iff_cutChar
#print axioms RJLemmaJ.cTrue_eq_cutChar_count
#print axioms RJLemmaJ.cTrue_bulk_part
