/-
KplusSigns.lean
===============
`lem:Kplus` (iv) of `merged_novel_paper.tex`: if `c ∈ K` has every `c_i ≠ 0`, then
`|c| ∈ K^+` and `G(c) = S G(|c|) S` for a diagonal sign matrix `S`.  No sorry.
-/
import KplusMain

namespace KplusSigns

open Matrix KplusPath KplusLocus

variable {c : ℕ → ℝ} {n : ℕ}

/-- Cumulative sign: `s_0 = 1`, `s_{i+1} = s_i * sign(c_{i+1})`. -/
noncomputable def sgn (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | (i + 1) => sgn c i * (if 0 < c (i + 1) then 1 else -1)

theorem sgn_sq (i : ℕ) : sgn c i * sgn c i = 1 := by
  induction i with
  | zero => simp [sgn]
  | succ i ih =>
    simp only [sgn]
    split_ifs <;> nlinarith [ih]

theorem sgn_pm (i : ℕ) : sgn c i = 1 ∨ sgn c i = -1 := by
  induction i with
  | zero => left; simp [sgn]
  | succ i ih =>
    simp only [sgn]
    split_ifs <;> rcases ih with h | h <;> simp [h]

/-- The diagonal sign matrix. -/
noncomputable def Smat (c : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  diagonal fun i => sgn c i

theorem Smat_mul_self (c : ℕ → ℝ) (n : ℕ) : Smat c n * Smat c n = 1 := by
  unfold Smat
  rw [diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; simp [sgn_sq]
  · simp [h]

theorem Smat_isUnit_det (c : ℕ → ℝ) (n : ℕ) : IsUnit (Smat c n).det := by
  have := congrArg det (Smat_mul_self c n)
  rw [det_mul, det_one] at this
  exact isUnit_iff_ne_zero.mpr (fun h => by rw [h] at this; simp at this)

theorem pg_signs (hc0 : ∀ i, 1 ≤ i → i ≤ n → c i ≠ 0) :
    pg c n = Smat c n * pg (fun i => |c i|) n * Smat c n := by
  unfold Smat
  ext i j
  rw [mul_diagonal, diagonal_mul]
  simp only [pg]
  by_cases hij : (i : ℕ) = j
  · simp only [hij, if_true]
    have := sgn_sq (c := c) j
    nlinarith [this]
  · simp only [hij, if_false]
    by_cases h1 : (i : ℕ) + 1 = j
    · simp only [h1, if_true]
      have hj1 : 1 ≤ (j : ℕ) := by omega
      have hjn : (j : ℕ) ≤ n := by have := j.isLt; omega
      have hs : sgn c j = sgn c i * (if 0 < c j then 1 else -1) := by
        rw [← h1]; rfl
      have hcj := hc0 j hj1 hjn
      have hsq := sgn_sq (c := c) i
      rw [hs]
      rcases lt_or_gt_of_ne hcj with h | h
      · simp only [not_lt.mpr h.le, if_false, abs_of_neg h]
        nlinarith [hsq]
      · simp only [h, if_true, abs_of_pos h]
        nlinarith [hsq]
    · simp only [h1, if_false]
      by_cases h2 : (j : ℕ) + 1 = i
      · simp only [h2, if_true]
        have hi1 : 1 ≤ (i : ℕ) := by omega
        have hin : (i : ℕ) ≤ n := by have := i.isLt; omega
        have hs : sgn c i = sgn c j * (if 0 < c i then 1 else -1) := by
          rw [← h2]; rfl
        have hci := hc0 i hi1 hin
        have hsq := sgn_sq (c := c) j
        rw [hs]
        rcases lt_or_gt_of_ne hci with h | h
        · simp only [not_lt.mpr h.le, if_false, abs_of_neg h]
          nlinarith [hsq]
        · simp only [h, if_true, abs_of_pos h]
          nlinarith [hsq]
      · simp [h2]

/-- **`lem:Kplus` (iv).**  If `c ∈ K` has all `c_i ≠ 0` then `|c| ∈ K^+` and
`G(c) = S G(|c|) S` with `S` a diagonal matrix of signs. -/
theorem sign_reduction (hc0 : ∀ i, 1 ≤ i → i ≤ n → c i ≠ 0) (hK : InK c n) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < |c i|) ∧ InK (fun i => |c i|) n ∧
    ∃ s : Fin (n + 1) → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      pg c n = diagonal s * pg (fun i => |c i|) n * diagonal s := by
  refine ⟨fun i h1 h2 => abs_pos.mpr (hc0 i h1 h2), ?_, ⟨fun i => sgn c i, fun i => sgn_pm i,
    pg_signs hc0⟩⟩
  have hrev : pg (fun i => |c i|) n = Smat c n * pg c n * Smat c n := by
    have h := pg_signs hc0
    have hS := Smat_mul_self c n
    calc pg (fun i => |c i|) n
        = (Smat c n * Smat c n) * pg (fun i => |c i|) n * (Smat c n * Smat c n) := by
          rw [hS]; simp
      _ = Smat c n * (Smat c n * pg (fun i => |c i|) n * Smat c n) * Smat c n := by
          simp only [mul_assoc]
      _ = Smat c n * pg c n * Smat c n := by rw [← h]
  have hSH : (Smat c n)ᴴ = Smat c n := by
    unfold Smat
    ext i j
    by_cases h : i = j
    · subst h; simp [conjTranspose_apply, diagonal_apply]
    · simp [conjTranspose_apply, diagonal_apply, h, Ne.symm h]
  refine ⟨?_, ?_⟩
  · rw [hrev]
    have := hK.1.mul_mul_conjTranspose_same (Smat c n)
    rwa [hSH] at this
  · rw [hrev, rank_mul_eq_left_of_isUnit_det _ _ (Smat_isUnit_det c n)]
    rw [rank_mul_eq_right_of_isUnit_det _ _ (Smat_isUnit_det c n)]
    exact hK.2

end KplusSigns

#print axioms KplusSigns.sign_reduction
