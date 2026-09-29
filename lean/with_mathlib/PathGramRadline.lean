/-
PathGramRadline.lean
====================
Formalises the rank content of `lem:radline` from
`paper/journal/merged_novel_paper.tex`:

    When pathGram n is singular (det = 0, i.e. n ≡ 1 mod 3),
    its ℚ-rank equals n.

Strategy:
1. Map pathGram n to ℚ (pathGramQ).
2. Upper bound: det = 0 → ker is nontrivial → rank ≤ n (rank-nullity).
3. Lower bound: top-left n×n submatrix = pathGramQ (n-1) with det ≠ 0
   → IsUnit → rank = n → rank_submatrix_le gives rank(full) ≥ n.

Axioms: propext, Classical.choice, Quot.sound.  No sorry.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PathGramSingular

namespace PathGramRadline

open Matrix PathGramSingular

/-! ## pathGramQ: pathGram cast to ℚ -/

noncomputable def pathGramQ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  (pathGram n).map (algebraMap ℤ ℚ)

theorem pathGramQ_det (n : ℕ) : (pathGramQ n).det = ((pathGram n).det : ℚ) :=
  ((algebraMap ℤ ℚ).map_det (pathGram n)).symm

theorem pathGramQ_det_eq_zero_iff (n : ℕ) : (pathGramQ n).det = 0 ↔ ∃ j, n = 3 * j + 1 := by
  rw [pathGramQ_det, Int.cast_eq_zero]
  exact pathGram_singular_iff n

/-! ## Submatrix identity for pathGramQ -/

private theorem sub_pathGramQ (n : ℕ) :
    (pathGramQ (n + 1)).submatrix Fin.castSucc Fin.castSucc = pathGramQ n := by
  ext i j
  simp only [pathGramQ, Matrix.submatrix_apply, Matrix.map_apply, pathGram, Fin.val_castSucc]
  rfl

/-! ## Upper bound: rank ≤ n when det = 0 -/

theorem pathGramQ_rank_le (n : ℕ) (hdet : (pathGramQ n).det = 0) :
    (pathGramQ n).rank ≤ n := by
  -- det = 0 → ∃ v ≠ 0, (pathGramQ n) *ᵥ v = 0 → ker ≠ ⊥
  obtain ⟨v, hv_ne, hv_mul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hker_ne : LinearMap.ker (pathGramQ n).mulVecLin ≠ ⊥ := by
    rw [ne_eq, Submodule.eq_bot_iff]; push Not
    exact ⟨v, by rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply], hv_ne⟩
  -- rank-nullity: rank + finrank(ker) = n+1
  have hrn := LinearMap.finrank_range_add_finrank_ker (pathGramQ n).mulVecLin
  -- finrank(Fin(n+1) → ℚ) = n+1
  have hfin : Module.finrank ℚ (Fin (n + 1) → ℚ) = n + 1 := by simp
  -- ker ≠ ⊥ → finrank(ker) ≥ 1
  have hker_pos : 1 ≤ Module.finrank ℚ (LinearMap.ker (pathGramQ n).mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hker_ne
  -- rank ≤ n
  have : (pathGramQ n).rank =
      Module.finrank ℚ (LinearMap.range (pathGramQ n).mulVecLin) := rfl
  linarith

/-! ## Lower bound: rank ≥ n when det(submatrix) ≠ 0 -/

theorem pathGramQ_rank_ge_of_sub_isUnit (j : ℕ) :
    (3 * j + 1) ≤ (pathGramQ (3 * j + 1)).rank := by
  -- submatrix = pathGramQ (3j), which has det ≠ 0 → IsUnit → rank = 3j+1
  have hdet_sub : (pathGramQ (3 * j)).det ≠ 0 := by
    rw [pathGramQ_det, Ne, Int.cast_eq_zero]
    intro h
    rw [pathGram_singular_iff] at h
    obtain ⟨k, hk⟩ := h
    omega
  have hunit_det : IsUnit (pathGramQ (3 * j)).det :=
    isUnit_iff_ne_zero.mpr hdet_sub
  have hunit : IsUnit (pathGramQ (3 * j)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hunit_det
  have hrank_sub : (pathGramQ (3 * j)).rank = 3 * j + 1 := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  -- rank_submatrix_le: rank(submatrix) ≤ rank(full)
  have hle : (pathGramQ (3 * j)).rank ≤ (pathGramQ (3 * j + 1)).rank := by
    have := Matrix.rank_submatrix_le (pathGramQ (3 * j + 1)) Fin.castSucc Fin.castSucc
    rwa [sub_pathGramQ] at this
  linarith

/-! ## Main theorem: rank = n when n ≡ 1 mod 3 -/

/-- lem:radline (rank content): when pathGram n is singular, its ℚ-rank is n. -/
theorem pathGramQ_rank_eq (n : ℕ) (h : ∃ j, n = 3 * j + 1) :
    (pathGramQ n).rank = n := by
  obtain ⟨j, rfl⟩ := h
  apply Nat.le_antisymm
  · apply pathGramQ_rank_le
    exact (pathGramQ_det_eq_zero_iff (3 * j + 1)).mpr ⟨j, rfl⟩
  · exact pathGramQ_rank_ge_of_sub_isUnit j

end PathGramRadline

#print axioms PathGramRadline.pathGramQ_rank_eq
