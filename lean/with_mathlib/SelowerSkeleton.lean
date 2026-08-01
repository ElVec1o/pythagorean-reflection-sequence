/-
  SelowerSkeleton.lean
  ====================
  The algebraic skeleton of paper 2, Appendix A (Proposition `prop:selower`).

  The appendix's analytic inputs (the annulus representation, the Poisson envelope,
  the mean value theorem) are NOT formalised here.  What is formalised is everything
  the appendix does with them once they are granted, i.e. the steps a referee flagged
  as stated without an equation number:

    * the pole reduction: from c(Z) = 0 and the two shift rules, the "exact facts"
      s(qZ) = s(Z) and c(qZ) = q Z s(Z);
    * the invariant at a pole, F_0 = q s(Z)^2;
    * the quadratic-form lower bound behind "lambda_n >= q - Z/2";
    * the Weierstrass/Gronwall product bound prod (1 - d i) >= 1 - sum (d i).

  Each is stated with its hypotheses explicit, so that the analytic facts enter only
  where they are actually used.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

namespace Selower

open Finset

/-! ### The pole reduction -/

/-- **The two "exact facts" at a travel pole.**  Given the Koornwinder--Swarttouw shift
    rules as hypotheses and the pole condition `c Z = 0`, both facts are pure algebra. -/
theorem pole_facts {R : Type*} [CommRing R] (q Z cZ cqZ sZ sqZ : R)
    (hs : sZ - sqZ = Z * cZ)          -- s(z) - s(qz) = z c(z)   at z = Z
    (hc : cZ - cqZ = -(q * Z) * sqZ)  -- c(z) - c(qz) = -q z s(qz) at z = Z
    (hpole : cZ = 0) :
    sqZ = sZ ∧ cqZ = q * Z * sZ := by
  have h1 : sqZ = sZ := by rw [hpole] at hs; linear_combination -hs
  refine ⟨h1, ?_⟩
  rw [hpole, h1] at hc
  linear_combination -hc

/-- **The invariant at a pole.**  With `F = c^2 - Z q c s + q s^2`, the pole condition
    collapses it to `q s^2`. -/
theorem F_at_pole {R : Type*} [CommRing R] (q Z c s : R) (hpole : c = 0) :
    c ^ 2 - Z * q * c * s + q * s ^ 2 = q * s ^ 2 := by
  rw [hpole]; ring

/-! ### The quadratic-form bound -/

/-- **Lower bound for the energy form.**  For `b ≥ 0`, the form `x^2 - b x y + q y^2`
    dominates `(min 1 q - b/2)(x^2 + y^2)`.  This is the content of the appendix's
    eigenvalue bound `lambda_n ≥ q - Z/2`, via `|b x y| ≤ (b/2)(x^2 + y^2)`. -/
theorem form_lower_bound (q b x y : ℝ) (hb : 0 ≤ b) (hq1 : q ≤ 1) :
    (q - b / 2) * (x ^ 2 + y ^ 2) ≤ x ^ 2 - b * x * y + q * y ^ 2 := by
  have hxy : b * x * y ≤ b / 2 * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), hb]
  nlinarith [sq_nonneg x, hq1]

/-! ### The discrete Gronwall / Weierstrass step -/

/-- **Weierstrass product bound.**  If every `d i ∈ [0,1]` then
    `∏ (1 - d i) ≥ 1 - ∑ d i`.  This is what turns the telescoped drift into the
    lower bound on `F_0`. -/
theorem prod_one_sub_ge (n : ℕ) (d : ℕ → ℝ)
    (h0 : ∀ i, 0 ≤ d i) (h1 : ∀ i, d i ≤ 1) :
    1 - ∑ i ∈ range n, d i ≤ ∏ i ∈ range n, (1 - d i) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hp : (0:ℝ) ≤ ∏ i ∈ range k, (1 - d i) :=
      Finset.prod_nonneg fun i _ => by linarith [h1 i]
    have hS : (0:ℝ) ≤ ∑ i ∈ range k, d i :=
      Finset.sum_nonneg fun i _ => h0 i
    have hd : 0 ≤ d k := h0 k
    have hdk : d k ≤ 1 := h1 k
    nlinarith [ih, hp, hS, hd, hdk, mul_nonneg hS hd]

end Selower

-- Rule 5 axiom audit.
#print axioms Selower.pole_facts
#print axioms Selower.F_at_pole
#print axioms Selower.form_lower_bound
#print axioms Selower.prod_one_sub_ge
