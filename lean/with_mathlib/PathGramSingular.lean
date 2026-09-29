/-
PathGramSingular.lean
=====================
Formalises the algebraic content of `lem:lorentz` from
`paper/journal/merged_novel_paper.tex`:

    The path tridiagonal Gram matrix G_n (size (n+1)×(n+1), with 1s on the
    diagonal and −1s on the super/sub-diagonals) is singular if and only if
    n ≡ 1 (mod 3).

Strategy:
1. Define pathGram n.
2. Prove det(G_{n+2}) = det(G_{n+1}) − det(G_n) via Laplace expansion.
3. Combine with `VinbergPoint.lorentz_det_zero_iff` to conclude.

Axioms: propext, Classical.choice, Quot.sound.  No sorry.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import VinbergPoint

namespace PathGramSingular

open Matrix VinbergPoint

/-! ## Definition -/

/-- The (n+1)×(n+1) path tridiagonal Gram matrix. -/
def pathGram (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j =>
    if (i : ℕ) = (j : ℕ) then 1
    else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then -1
    else 0

/-! ## Submatrix helper -/

private theorem submatrix_castSucc (n : ℕ) :
    (pathGram (n + 1)).submatrix Fin.castSucc Fin.castSucc = pathGram n := by
  ext i j
  simp only [pathGram, Matrix.submatrix_apply, Fin.val_castSucc]
  rfl

/-! ## Second submatrix for Laplace expansion -/

-- The (n+2)×(n+2) submatrix obtained by removing row (n+1) and last col from pathGram(n+2).
private def Smat (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
  (pathGram (n + 2)).submatrix (Fin.castSucc (Fin.last (n + 1))).succAbove Fin.castSucc

-- Top-left (n+1)×(n+1) block of Smat(n) = pathGram(n).
private theorem Smat_topLeft (n : ℕ) :
    (Smat n).submatrix Fin.castSucc Fin.castSucc = pathGram n := by
  ext i j
  simp only [Smat, pathGram, Matrix.submatrix_apply, Fin.val_castSucc]
  -- Row: succAbove (castSucc (last (n+1))) (castSucc i) = castSucc (castSucc i)
  -- since castSucc (castSucc i) < castSucc (last (n+1)) (both in Fin (n+3))
  have hlt : (Fin.castSucc (Fin.castSucc i) : Fin (n + 3)) < Fin.castSucc (Fin.last (n + 1)) := by
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]; exact i.isLt
  rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
  simp only [Fin.val_castSucc]
  rfl

-- Last row of Smat(n): entry at last col = -1, all others = 0.
private theorem Smat_lastRow (n : ℕ) (j : Fin (n + 2)) :
    Smat n (Fin.last (n + 1)) j = if j = Fin.last (n + 1) then -1 else 0 := by
  simp only [Smat, Matrix.submatrix_apply]
  rw [show (Fin.castSucc (Fin.last (n + 1))).succAbove (Fin.last (n + 1)) = Fin.last (n + 2) from by
    apply Fin.succAbove_of_le_castSucc; simp]
  simp only [pathGram, Fin.val_last, Fin.val_castSucc, Fin.ext_iff]
  have hj : (j : ℕ) < n + 2 := j.isLt
  split_ifs <;> omega

private theorem det_Smat (n : ℕ) : (Smat n).det = -(pathGram n).det := by
  rw [Matrix.det_succ_row (Smat n) (Fin.last (n + 1))]
  rw [Finset.sum_eq_single_of_mem (Fin.last (n + 1)) (Finset.mem_univ _)]
  · -- The single surviving term
    have hentry : Smat n (Fin.last (n + 1)) (Fin.last (n + 1)) = -1 := by
      rw [Smat_lastRow]; simp
    have hsign : (-1 : ℤ) ^ ((Fin.last (n + 1) : ℕ) + (Fin.last (n + 1) : ℕ)) = 1 := by
      simp only [Fin.val_last]
      rw [show (n + 1) + (n + 1) = 2 * (n + 1) from by omega, pow_mul]; norm_num
    have hsub : (Smat n).submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove =
        pathGram n := by
      simp only [Fin.succAbove_last]
      exact Smat_topLeft n
    rw [hentry, hsign, hsub]; ring
  · -- All other j: Smat(n)[Fin.last, j] = 0
    intro j _ hjne
    have hentry : Smat n (Fin.last (n + 1)) j = 0 := by
      rw [Smat_lastRow]; rw [if_neg hjne]
    simp only [hentry, mul_zero, zero_mul]

/-! ## Laplace expansion along last column -/

private theorem pathGram_det_succ (n : ℕ) :
    (pathGram (n + 2)).det = (pathGram (n + 1)).det - (pathGram n).det := by
  rw [Matrix.det_succ_column (pathGram (n + 2)) (Fin.last (n + 2))]
  simp_rw [Fin.succAbove_last]
  -- Split sum: first n+1 terms (zero) + penultimate + last
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  -- All terms in the first sum are zero (row val ≤ n, col val = n+2, not adjacent)
  have hzero : ∀ i : Fin (n + 1),
      (-1 : ℤ) ^ ((Fin.castSucc (Fin.castSucc i) : ℕ) + (Fin.last (n + 2) : ℕ)) *
      pathGram (n + 2) (Fin.castSucc (Fin.castSucc i)) (Fin.last (n + 2)) *
      ((pathGram (n + 2)).submatrix (Fin.castSucc (Fin.castSucc i)).succAbove Fin.castSucc).det = 0 := by
    intro i
    have hcol : pathGram (n + 2) (Fin.castSucc (Fin.castSucc i)) (Fin.last (n + 2)) = 0 := by
      simp only [pathGram, Fin.val_castSucc, Fin.val_last]
      have : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
      omega
    simp [hcol]
  simp_rw [hzero, Finset.sum_const_zero, zero_add]
  -- Penultimate term
  have hpen_entry : pathGram (n + 2) (Fin.castSucc (Fin.last (n + 1))) (Fin.last (n + 2)) = -1 := by
    simp [pathGram, Fin.val_castSucc, Fin.val_last]
  have hpen_sign : (-1 : ℤ) ^ ((Fin.castSucc (Fin.last (n + 1)) : ℕ) + (Fin.last (n + 2) : ℕ)) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [show (n + 1) + (n + 2) = 2 * (n + 1) + 1 from by omega, pow_add, pow_mul]; norm_num
  have hpen_sub : ((pathGram (n + 2)).submatrix
      (Fin.castSucc (Fin.last (n + 1))).succAbove Fin.castSucc).det = -(pathGram n).det := det_Smat n
  -- Last term
  have hlast_entry : pathGram (n + 2) (Fin.last (n + 2)) (Fin.last (n + 2)) = 1 := by
    simp [pathGram]
  have hlast_sign : (-1 : ℤ) ^ ((Fin.last (n + 2) : ℕ) + (Fin.last (n + 2) : ℕ)) = 1 := by
    simp only [Fin.val_last]
    rw [show (n + 2) + (n + 2) = 2 * (n + 2) from by omega, pow_mul]; norm_num
  have hlast_sub : ((pathGram (n + 2)).submatrix (Fin.last (n + 2)).succAbove Fin.castSucc).det =
      (pathGram (n + 1)).det := by
    rw [Fin.succAbove_last, submatrix_castSucc (n + 1)]
  rw [hpen_entry, hpen_sign, hpen_sub, hlast_entry, hlast_sign, hlast_sub]
  ring

/-! ## Two-step induction -/

private theorem pathGram_det_base0 : (pathGram 0).det = contD xones 1 := by
  rw [Matrix.det_fin_one]; simp [pathGram, contD]

private theorem pathGram_det_base1 : (pathGram 1).det = contD xones 2 := by
  rw [Matrix.det_fin_two]; simp [pathGram, contD, xones]

/-- det(pathGram n) = contD xones (n+1) for all n. -/
theorem pathGram_det_eq_contD : ∀ n : ℕ,
    (pathGram n).det = contD xones (n + 1) ∧
    (pathGram (n + 1)).det = contD xones (n + 2) := by
  intro n
  induction n with
  | zero => exact ⟨pathGram_det_base0, pathGram_det_base1⟩
  | succ m ih =>
    obtain ⟨ihm, ihm1⟩ := ih
    refine ⟨ihm1, ?_⟩
    rw [pathGram_det_succ, ihm1, ihm]
    linarith [xones_step (m + 1)]

/-- lem:lorentz (algebraic part): G_n is singular iff n ≡ 1 (mod 3). -/
theorem pathGram_singular_iff (n : ℕ) :
    (pathGram n).det = 0 ↔ ∃ j, n = 3 * j + 1 := by
  rw [(pathGram_det_eq_contD n).1]
  exact VinbergPoint.lorentz_det_zero_iff n

end PathGramSingular

#print axioms PathGramSingular.pathGram_singular_iff
