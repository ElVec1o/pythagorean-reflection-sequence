/-
KplusPath.lean
==============
Weighted path Gram matrix `G(c)` of `lem:Kplus` (`merged_novel_paper.tex`):
tridiagonal, `1` on the diagonal, `-c_i` on the entries `(i-1,i)` and `(i,i-1)`.
Its leading-block determinants satisfy the continuant recursion
`D_0 = D_1 = 1`, `D_{k+1} = D_k - c_k^2 D_{k-1}`, with `det G(c) = D_{n+1}`.

This generalises `PathGramSingular` (all weights `1`, integer entries) to arbitrary real
weights, by the same Laplace-expansion argument.  No sorry.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace KplusPath

open Matrix

/-- `G(c)`, of size `(n+1) x (n+1)`; `c : ℕ → ℝ` is read at indices `1..n`. -/
def pg (c : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    if (i : ℕ) = (j : ℕ) then 1
    else if (i : ℕ) + 1 = (j : ℕ) then -c j
    else if (j : ℕ) + 1 = (i : ℕ) then -c i
    else 0

/-- The continuant `D_k` of the weights: `D_0 = D_1 = 1`, `D_{k+2} = D_{k+1} - c_{k+1}^2 D_k`. -/
def D (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (k + 2) => D c (k + 1) - (c (k + 1)) ^ 2 * D c k

private theorem submatrix_castSucc (c : ℕ → ℝ) (n : ℕ) :
    (pg c (n + 1)).submatrix Fin.castSucc Fin.castSucc = pg c n := by
  ext i j
  simp only [pg, Matrix.submatrix_apply, Fin.val_castSucc]

private def Smat (c : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  (pg c (n + 2)).submatrix (Fin.castSucc (Fin.last (n + 1))).succAbove Fin.castSucc

private theorem Smat_topLeft (c : ℕ → ℝ) (n : ℕ) :
    (Smat c n).submatrix Fin.castSucc Fin.castSucc = pg c n := by
  ext i j
  simp only [Smat, pg, Matrix.submatrix_apply, Fin.val_castSucc]
  have hlt : (Fin.castSucc (Fin.castSucc i) : Fin (n + 3)) < Fin.castSucc (Fin.last (n + 1)) := by
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]; exact i.isLt
  rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
  simp only [Fin.val_castSucc]

private theorem Smat_lastRow (c : ℕ → ℝ) (n : ℕ) (j : Fin (n + 2)) :
    Smat c n (Fin.last (n + 1)) j = if j = Fin.last (n + 1) then -c (n + 2) else 0 := by
  simp only [Smat, Matrix.submatrix_apply]
  rw [show (Fin.castSucc (Fin.last (n + 1))).succAbove (Fin.last (n + 1)) = Fin.last (n + 2) from by
    apply Fin.succAbove_of_le_castSucc; simp]
  simp only [pg, Fin.val_last, Fin.val_castSucc, Fin.ext_iff]
  have hj : (j : ℕ) < n + 2 := j.isLt
  split_ifs <;> first | rfl | omega

private theorem det_Smat (c : ℕ → ℝ) (n : ℕ) : (Smat c n).det = -c (n + 2) * (pg c n).det := by
  rw [Matrix.det_succ_row (Smat c n) (Fin.last (n + 1))]
  rw [Finset.sum_eq_single_of_mem (Fin.last (n + 1)) (Finset.mem_univ _)]
  · have hentry : Smat c n (Fin.last (n + 1)) (Fin.last (n + 1)) = -c (n + 2) := by
      rw [Smat_lastRow]; simp
    have hsign : (-1 : ℝ) ^ ((Fin.last (n + 1) : ℕ) + (Fin.last (n + 1) : ℕ)) = 1 := by
      simp only [Fin.val_last]
      rw [show (n + 1) + (n + 1) = 2 * (n + 1) from by omega, pow_mul]; norm_num
    have hsub : (Smat c n).submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove =
        pg c n := by
      simp only [Fin.succAbove_last]
      exact Smat_topLeft c n
    rw [hentry, hsign, hsub]; ring
  · intro j _ hjne
    have hentry : Smat c n (Fin.last (n + 1)) j = 0 := by
      rw [Smat_lastRow]; rw [if_neg hjne]
    simp only [hentry, mul_zero, zero_mul]

theorem pg_det_succ (c : ℕ → ℝ) (n : ℕ) :
    (pg c (n + 2)).det = (pg c (n + 1)).det - (c (n + 2)) ^ 2 * (pg c n).det := by
  rw [Matrix.det_succ_column (pg c (n + 2)) (Fin.last (n + 2))]
  simp_rw [Fin.succAbove_last]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hzero : ∀ i : Fin (n + 1),
      (-1 : ℝ) ^ ((Fin.castSucc (Fin.castSucc i) : ℕ) + (Fin.last (n + 2) : ℕ)) *
      pg c (n + 2) (Fin.castSucc (Fin.castSucc i)) (Fin.last (n + 2)) *
      ((pg c (n + 2)).submatrix (Fin.castSucc (Fin.castSucc i)).succAbove Fin.castSucc).det
        = 0 := by
    intro i
    have hcol : pg c (n + 2) (Fin.castSucc (Fin.castSucc i)) (Fin.last (n + 2)) = 0 := by
      simp only [pg, Fin.val_castSucc, Fin.val_last]
      have : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
      split_ifs <;> first | rfl | omega
    simp [hcol]
  simp_rw [hzero, Finset.sum_const_zero, zero_add]
  have hpen_entry :
      pg c (n + 2) (Fin.castSucc (Fin.last (n + 1))) (Fin.last (n + 2)) = -c (n + 2) := by
    simp [pg, Fin.val_castSucc, Fin.val_last]
  have hpen_sign :
      (-1 : ℝ) ^ ((Fin.castSucc (Fin.last (n + 1)) : ℕ) + (Fin.last (n + 2) : ℕ)) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [show (n + 1) + (n + 2) = 2 * (n + 1) + 1 from by omega, pow_add, pow_mul]; norm_num
  have hpen_sub : ((pg c (n + 2)).submatrix
      (Fin.castSucc (Fin.last (n + 1))).succAbove Fin.castSucc).det =
        -c (n + 2) * (pg c n).det := det_Smat c n
  have hlast_entry : pg c (n + 2) (Fin.last (n + 2)) (Fin.last (n + 2)) = 1 := by
    simp [pg]
  have hlast_sign : (-1 : ℝ) ^ ((Fin.last (n + 2) : ℕ) + (Fin.last (n + 2) : ℕ)) = 1 := by
    simp only [Fin.val_last]
    rw [show (n + 2) + (n + 2) = 2 * (n + 2) from by omega, pow_mul]; norm_num
  have hlast_sub : ((pg c (n + 2)).submatrix (Fin.last (n + 2)).succAbove Fin.castSucc).det =
      (pg c (n + 1)).det := by
    rw [Fin.succAbove_last, submatrix_castSucc c (n + 1)]
  rw [hpen_entry, hpen_sign, hpen_sub, hlast_entry, hlast_sign, hlast_sub]
  ring

/-- `det G(c) = D_{n+1}`. -/
theorem pg_det_eq_D (c : ℕ → ℝ) : ∀ n : ℕ,
    (pg c n).det = D c (n + 1) ∧ (pg c (n + 1)).det = D c (n + 2) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [Matrix.det_fin_one]; simp [pg, D]
    · rw [Matrix.det_fin_two]; simp [pg, D]; ring
  | succ m ih =>
    obtain ⟨ihm, ihm1⟩ := ih
    refine ⟨ihm1, ?_⟩
    rw [pg_det_succ, ihm1, ihm]
    simp only [D]

end KplusPath

#print axioms KplusPath.pg_det_eq_D
