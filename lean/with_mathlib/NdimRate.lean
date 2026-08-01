/-
  NdimRate.lean
  =============
  The algebraic core of paper 1b, Theorem "ndim-rate":

      r_n = 1 + 2 cos(2 pi / (n+3)),

  together with its asymptotic corollary  3 - r_n = 4 sin^2(pi/(n+3)).

  Two ingredients of the paper's proof are formalised here:

  (1) `pell_binet` -- the Binet formula for the Fibonacci-Pell polynomials
      P_m(y) defined by P_0 = 0, P_1 = 1, P_{m+2} = P_{m+1} + y P_m, in the
      division-free form  (alpha - beta) * P m = alpha^m - beta^m,  where
      alpha, beta are the roots of x^2 = x + y.  This is what licenses the
      step "P_m(y) = 0 iff (alpha/beta)^m = 1" in the paper.

  (2) `root_translation` -- the trigonometric identity 4 cos^2 t - 1 =
      1 + 2 cos(2t) used to convert the roots y_j = -1/(4 cos^2(pi j/m))
      back to t_j = 1 + 2 cos(2 pi j/m).

  What is NOT formalised: that the abstract orbit-growth rate equals the
  largest such root (a generating-function/dominant-pole argument).  That
  step remains PROVED-on-paper only, and is flagged as such in the paper.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace NdimRate

variable {R : Type*} [CommRing R]

/-- If `alpha + beta = 1` and `alpha * beta = -y` then `alpha` satisfies `x^2 = x + y`. -/
theorem sq_eq (α β y : R) (hs : α + β = 1) (hp : α * β = -y) : α ^ 2 = α + y := by
  have : α * (α + β - 1) = 0 := by rw [hs]; ring
  linear_combination this - hp

/-- **Binet formula, division-free.** -/
theorem pell_binet (α β y : R) (P : ℕ → R)
    (hs : α + β = 1) (hp : α * β = -y)
    (h0 : P 0 = 0) (h1 : P 1 = 1)
    (hrec : ∀ m : ℕ, P (m + 2) = P (m + 1) + y * P m) :
    ∀ m : ℕ, (α - β) * P m = α ^ m - β ^ m := by
  have ha : α ^ 2 = α + y := sq_eq α β y hs hp
  have hb : β ^ 2 = β + y :=
    sq_eq β α y (by linear_combination hs) (by linear_combination hp)
  have key : ∀ m : ℕ, ((α - β) * P m = α ^ m - β ^ m)
      ∧ ((α - β) * P (m + 1) = α ^ (m + 1) - β ^ (m + 1)) := by
    intro m
    induction m with
    | zero => exact ⟨by rw [h0]; ring, by rw [h1]; ring⟩
    | succ n ih =>
      obtain ⟨ihn, ihn1⟩ := ih
      refine ⟨ihn1, ?_⟩
      have hexp : ∀ k : ℕ, α ^ (k + 2) = α ^ (k + 1) + y * α ^ k := by
        intro k; have : α ^ (k + 2) = α ^ k * α ^ 2 := by ring
        rw [this, ha]; ring
      have hexpb : ∀ k : ℕ, β ^ (k + 2) = β ^ (k + 1) + y * β ^ k := by
        intro k; have : β ^ (k + 2) = β ^ k * β ^ 2 := by ring
        rw [this, hb]; ring
      rw [hrec n, mul_add, ihn1, hexp n, hexpb n]
      linear_combination y * ihn
  exact fun m => (key m).1

open Real

/-- **Root translation.** `4 cos^2 t - 1 = 1 + 2 cos(2t)`. -/
theorem root_translation (t : ℝ) : 4 * Real.cos t ^ 2 - 1 = 1 + 2 * Real.cos (2 * t) := by
  rw [Real.cos_two_mul]; ring

/-- **Asymptotic residual.** `3 - (1 + 2 cos(2t)) = 4 sin^2 t`. -/
theorem rate_residual (t : ℝ) : 3 - (1 + 2 * Real.cos (2 * t)) = 4 * Real.sin t ^ 2 := by
  rw [Real.cos_two_mul]
  linear_combination (-4 : ℝ) * Real.sin_sq_add_cos_sq t

/-- The rate at dimension `n`, as it appears in the paper. -/
noncomputable def r (n : ℕ) : ℝ := 1 + 2 * Real.cos (2 * Real.pi / (n + 3))

/-- `3 - r_n = 4 sin^2(pi/(n+3))`, the paper's Corollary. -/
theorem three_sub_r (n : ℕ) : 3 - r n = 4 * Real.sin (Real.pi / (n + 3)) ^ 2 := by
  unfold r
  have h : 2 * Real.pi / (n + 3) = 2 * (Real.pi / (n + 3)) := by ring
  rw [h]; exact rate_residual _

end NdimRate

-- Rule 5 axiom check.
#print axioms NdimRate.sq_eq
#print axioms NdimRate.pell_binet
#print axioms NdimRate.root_translation
#print axioms NdimRate.rate_residual
#print axioms NdimRate.three_sub_r
