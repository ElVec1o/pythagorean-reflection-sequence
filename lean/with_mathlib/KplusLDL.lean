/-
KplusLDL.lean
=============
The tridiagonal quadratic form of `G(c)` and its LDL^T (sum-of-squares) decomposition, used for
`lem:Kplus` (b) => (a).

  `Q_n(x) = sum_{i<=n} x_i^2 - 2 sum_{i<n} c_{i+1} x_i x_{i+1}`  equals  `x^T G(c) x`, and
  `Q_m(x) = sum_{i<m} d_i (x_i - (c_{i+1}/d_i) x_{i+1})^2 + d_m x_m^2`,   `d_i = D_{i+1}/D_i`,
valid whenever `D_1,...,D_m` are nonzero.  Hence `D_1..D_n > 0` and `D_{n+1} = 0` give
`G(c)` positive semidefinite.  No sorry.
-/
import KplusPath
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace KplusLDL

open Matrix KplusPath Finset

variable (c : ℕ → ℝ)

/-- `Q_n(x)` for a sequence `x : ℕ → ℝ`. -/
def Q (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), x i ^ 2 - 2 * ∑ i ∈ range n, c (i + 1) * x i * x (i + 1)

theorem quad_pg_succ (n : ℕ) (x : Fin (n + 2) → ℝ) :
    x ⬝ᵥ (pg c (n + 1) *ᵥ x) =
      (fun i : Fin (n + 1) => x i.castSucc) ⬝ᵥ (pg c n *ᵥ fun i : Fin (n + 1) => x i.castSucc)
        + x (Fin.last (n + 1)) ^ 2
        - 2 * c (n + 1) * x (Fin.last n).castSucc * x (Fin.last (n + 1)) := by
  simp only [dotProduct, mulVec]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc (n := n + 1)]
  have hcc : ∀ i j : Fin (n + 1), pg c (n + 1) i.castSucc j.castSucc = pg c n i j := by
    intro i j; simp [pg]
  have hcl : ∀ i : Fin (n + 1), pg c (n + 1) i.castSucc (Fin.last (n + 1)) =
      if (i : ℕ) = n then -c (n + 1) else 0 := by
    intro i
    simp only [pg, Fin.val_castSucc, Fin.val_last]
    have := i.isLt
    split_ifs <;> first | rfl | (exfalso; omega) | omega
  have hlc : ∀ j : Fin (n + 1), pg c (n + 1) (Fin.last (n + 1)) j.castSucc =
      if (j : ℕ) = n then -c (n + 1) else 0 := by
    intro j
    simp only [pg, Fin.val_castSucc, Fin.val_last]
    have := j.isLt
    split_ifs <;> first | rfl | (exfalso; omega) | omega
  have hll : pg c (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1)) = 1 := by simp [pg]
  simp only [hcc, hcl, hlc, hll]
  have hsum1 : ∑ i : Fin (n + 1), x i.castSucc * (if (i : ℕ) = n then -c (n + 1) else 0) *
      x (Fin.last (n + 1)) = -c (n + 1) * x (Fin.last n).castSucc * x (Fin.last (n + 1)) := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp only [Fin.val_last, if_true]; ring
    · intro b _ hb
      have : (b : ℕ) ≠ n := fun h => hb (Fin.ext (by simpa using h))
      simp [this]
    · simp
  have hsum2 : ∑ j : Fin (n + 1), (if (j : ℕ) = n then -c (n + 1) else 0) * x j.castSucc =
      -c (n + 1) * x (Fin.last n).castSucc := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ n := fun h => hb (Fin.ext (by simpa using h))
      simp [this]
    · simp
  have e1 : ∀ i : Fin (n + 1), x i.castSucc * ((∑ j : Fin (n + 1), pg c n i j * x j.castSucc) +
      (if (i : ℕ) = n then -c (n + 1) else 0) * x (Fin.last (n + 1))) =
      x i.castSucc * (∑ j : Fin (n + 1), pg c n i j * x j.castSucc) +
        x i.castSucc * (if (i : ℕ) = n then -c (n + 1) else 0) * x (Fin.last (n + 1)) := by
    intro i; ring
  simp_rw [e1, Finset.sum_add_distrib, hsum1]
  rw [hsum2]
  ring

/-- `x^T G(c) x = Q_n(x)` for the restriction of a sequence. -/
theorem quad_pg_eq_Q : ∀ (n : ℕ) (x : ℕ → ℝ),
    (fun i : Fin (n + 1) => x i) ⬝ᵥ (pg c n *ᵥ fun i : Fin (n + 1) => x i) = Q c n x := by
  intro n
  induction n with
  | zero =>
    intro x
    simp [Q, pg, dotProduct, mulVec]
    ring
  | succ m ih =>
    intro x
    rw [quad_pg_succ]
    have := ih x
    simp only [Fin.val_castSucc, Fin.val_last] at this ⊢
    rw [this]
    simp only [Q, Finset.sum_range_succ _ (m + 1), Finset.sum_range_succ _ m]
    ring

/-- LDL^T identity. -/
theorem Q_ldl (x : ℕ → ℝ) : ∀ m : ℕ, (∀ i, 1 ≤ i → i ≤ m → D c i ≠ 0) →
    Q c m x = ∑ i ∈ range m, (D c (i + 1) / D c i) *
        (x i - (c (i + 1) * D c i / D c (i + 1)) * x (i + 1)) ^ 2
      + (D c (m + 1) / D c m) * x m ^ 2 := by
  intro m
  induction m with
  | zero =>
    intro _
    simp [Q, D]
  | succ m ih =>
    intro hD
    have ih' := ih (fun i h1 h2 => hD i h1 (by omega))
    have hm1 : D c (m + 1) ≠ 0 := hD (m + 1) (by omega) le_rfl
    have hm : D c m ≠ 0 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp [D]
      · exact hD m h (by omega)
    have hrec : D c (m + 2) = D c (m + 1) - c (m + 1) ^ 2 * D c m := rfl
    have e : Q c (m + 1) x = Q c m x + x (m + 1) ^ 2 - 2 * (c (m + 1) * x m * x (m + 1)) := by
      simp only [Q, Finset.sum_range_succ _ (m + 1), Finset.sum_range_succ _ m]
      ring
    rw [e, ih', Finset.sum_range_succ, hrec]
    field_simp
    ring

/-- `D_1..D_n > 0` and `D_{n+1} = 0` make `x^T G(c) x >= 0`. -/
theorem Q_nonneg (n : ℕ) (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < D c k) (hlast : D c (n + 1) = 0)
    (x : ℕ → ℝ) : 0 ≤ Q c n x := by
  rw [Q_ldl c x n (fun i h1 h2 => (hpos i h1 h2).ne'), hlast]
  simp only [zero_div, zero_mul, add_zero]
  refine Finset.sum_nonneg fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have h1 : 0 < D c (i + 1) := hpos (i + 1) (by omega) (by omega)
  have h0 : 0 < D c i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [D]
    · exact hpos i h (by omega)
  exact mul_nonneg (div_pos h1 h0).le (sq_nonneg _)

/-- `G(c)` is positive semidefinite when `D_1..D_n > 0` and `D_{n+1} = 0`. -/
theorem psd_of_D (n : ℕ)
    (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < D c k) (hlast : D c (n + 1) = 0) :
    (pg c n).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [transpose_apply, pg]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · simp only [star_trivial]
    let xh : ℕ → ℝ := fun k => if h : k < n + 1 then x ⟨k, h⟩ else 0
    have hx : x = fun i : Fin (n + 1) => xh i := by
      funext i; simp only [xh]; rw [dif_pos i.isLt]
    rw [hx, quad_pg_eq_Q]
    exact Q_nonneg c n hpos hlast xh

end KplusLDL

#print axioms KplusLDL.psd_of_D
