/-
  GateInputs.lean
  ===============
  The algebraic core of the four inputs G1-G4 of paper 2, section 6.

  These are the steps where the derivation actually went wrong in practice, so they
  are the ones worth machine-checking:

    * `re_div_eq`      -- Re(A/B) = (Re A Re B + Im A Im B)/|B|^2.  Bounding |1/B|
                          instead of using this identity inflated G1 by a factor 14,
                          because Im A and Im B are each O(s) while their PRODUCT is
                          O(s^2).  The identity is what forbids that loss.
    * `lam_coeff`      -- the k-th coefficient of Lam_n is Re/Im of i^{n+k}; guessing
                          the 4-cycle by hand made two halves add instead of cancel.
    * `ReLam0_lead`    -- the leading term of Re Lam_0 is EXACTLY e^{2h}/(1+q).
    * `G4_const`       -- (1/2) h^2 w^2 = tau/4 exactly, given w^2 tau = 2, h = tau/2.
    * `exp_sub_one_le` -- e^P - 1 <= P/(1-P), the product-term majorant behind G2.

  What is NOT here: the convergent-series tail estimates and the Gaussian moment
  bounds.  Those are analysis, they are not formalised, and paper 2 says so.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

namespace GateInputs

open Complex

/-- **The pairing identity.**  For `B ≠ 0`,
    `Re (A / B) = (Re A * Re B + Im A * Im B) / (Re B ^ 2 + Im B ^ 2)`.
    Using `|Re (A/B)| ≤ |A| * |1/B|` instead loses the cancellation between the two
    imaginary parts; that loss is exactly the factor that broke the first G1 bound. -/
theorem re_div_eq (A B : ℂ) :
    (A / B).re = (A.re * B.re + A.im * B.im) / (B.re ^ 2 + B.im ^ 2) := by
  rw [Complex.div_re]
  have : Complex.normSq B = B.re ^ 2 + B.im ^ 2 := by
    simp [Complex.normSq_apply]; ring
  rw [this]
  ring

/-- **Why the pairing matters, quantitatively.**  If `|Im A| ≤ s` and `|Im B| ≤ s`
    then the cross term they contribute is at most `s ^ 2`: individually first order,
    jointly second order. -/
theorem cross_term_sq (A B : ℂ) (s : ℝ) (hA : |A.im| ≤ s) (hB : |B.im| ≤ s) :
    |A.im * B.im| ≤ s ^ 2 := by
  rw [abs_mul]
  have hs : 0 ≤ s := le_trans (abs_nonneg _) hA
  calc |A.im| * |B.im| ≤ s * s := by
        exact mul_le_mul hA hB (abs_nonneg _) hs
    _ = s ^ 2 := by ring

/-- **The cumulant coefficient.**  `Lam_n = ∑_k k^{n-1} i^{n+k} rho^k/(1-q^k)`, so the
    `k`-th coefficient is `i ^ (n + k)`; its real and imaginary parts are the 4-cycle,
    here fixed by `i ^ 4 = 1` rather than written out by hand. -/
theorem lam_coeff (n k : ℕ) : (Complex.I) ^ (n + k + 4) = (Complex.I) ^ (n + k) := by
  rw [pow_add]
  simp [Complex.I_pow_four]

/-- **The leading term of `Re Lam_0` is exact.**  With `rho ^ 2 = 2 (1 - q) e`, the
    first even-`k` term `rho^2 / (2 (1 - q^2))` equals `e / (1 + q)`; no expansion. -/
theorem ReLam0_lead (q e rho : ℝ) (hq1 : q ≠ 1) (hq : 1 + q ≠ 0)
    (hrho : rho ^ 2 = 2 * (1 - q) * e) :
    rho ^ 2 / (2 * (1 - q ^ 2)) = e / (1 + q) := by
  have h2 : (1 : ℝ) - q ^ 2 = (1 - q) * (1 + q) := by ring
  have hne : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  rw [hrho, h2]
  field_simp

/-- **G4's constant is exactly `tau/4`.**  With `w ^ 2 * tau = 2` and `h = tau / 2`,
    the second-difference bound `(1/2) h^2 w^2` equals `tau / 4`. -/
theorem G4_const (w tau : ℝ) (h : w ^ 2 * tau = 2) :
    (1 / 2 : ℝ) * (tau / 2) ^ 2 * w ^ 2 = tau / 4 := by
  linear_combination (tau / 8) * h

/-- **The product majorant behind G2.**  For `0 ≤ P < 1`, `exp P - 1 ≤ P / (1 - P)`.
    This is what covers the product terms of `exp(∑ Lam_n xi^n / n!) - 1`. -/
theorem exp_sub_one_le (P : ℝ) (h1 : P < 1) :
    Real.exp P - 1 ≤ P / (1 - P) := by
  have hlt : (0:ℝ) < 1 - P := by linarith
  -- e^{-P} ≥ 1 - P, hence e^P ≤ 1/(1-P), hence the claim.
  have hkey : Real.exp P ≤ 1 / (1 - P) := by
    rw [le_div_iff₀ hlt]
    have h1P : (1:ℝ) - P ≤ Real.exp (-P) := by
      linarith [Real.add_one_le_exp (-P)]
    calc Real.exp P * (1 - P)
        ≤ Real.exp P * Real.exp (-P) :=
          mul_le_mul_of_nonneg_left h1P (le_of_lt (Real.exp_pos P))
      _ = 1 := by rw [← Real.exp_add]; simp
  have hid : 1 / (1 - P) - 1 = P / (1 - P) := by field_simp; ring
  linarith [hkey, hid.ge, hid.le]

end GateInputs

-- Rule 5 axiom audit.
#print axioms GateInputs.re_div_eq
#print axioms GateInputs.cross_term_sq
#print axioms GateInputs.lam_coeff
#print axioms GateInputs.ReLam0_lead
#print axioms GateInputs.G4_const
#print axioms GateInputs.exp_sub_one_le
