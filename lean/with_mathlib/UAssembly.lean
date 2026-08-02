/-
  UAssembly.lean
  ==============
  The ASSEMBLY of paper 2, Theorem `thm:U` ("the true growth series U is transcendental
  over Q(x)"), machine-checked from its analytic inputs.

  WHAT THIS IS.  Each analytic lemma of the paper enters as an explicit named hypothesis;
  Lean checks that they compose into the conclusion.  So this file verifies the *logic* of
  the transcendence argument and, as a by-product, produces an auditable list of exactly
  what U's transcendence rests on.  It does NOT formalise any of the analysis: no q-series,
  no steepest descent, no rigorous numerics.  Nothing here should be read as a claim that
  U's transcendence is formally verified.

  WHY IT IS WORTH HAVING.  Every serious defect found in the eleven adversarial review
  rounds of this chapter was of one kind: a step *consumed but not supplied*.
    * the gate arithmetic delivered |s| <= 1.77, not |s| < 1
      (a numerator bound 0.619 against the only proved denominator constant 0.35);
    * `b0 > 0`, the other half of the gate, was discharged nowhere;
    * infinitude of the travel poles -- used by BOTH transcendence theorems -- was asserted,
      never proved;
    * the truncation remainder `lem:cos` needs was asserted nowhere.
  In this file each of those is a hypothesis that must be supplied, or an unfilled goal.
  In particular `hKc : K < c` below is precisely the inequality that failed: with the
  numerator constant 0.619 and the annulus denominator constant 0.35 it is FALSE, and
  `gate_ratio_lt_one` is then unusable -- see `round9_defect` at the end.

  Correspondence with the paper:
    hstar  <-> Theorem `thm:star`        (|P12| <= 0.619 tau^{3/2} at every travel pole)
    hSe    <-> Lemma   `app:Se`          (|S_e| >= 0.63 sqrt(tau)), itself from `lem:P12closed`
    hb0    <-> Corollary `app:gate`      (b0 > 0, via the pole invariant)
    hred   <-> the supplement, S lifting (gate ==> the assembled numerator is non-zero)
    hInf   <-> Lemma   `lem:infpoles`    (the travel poles are infinite)
    hfin   <-> Theorem `thm:V`'s last step (an algebraic function has finitely many poles
                                            in the unit disc)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace UAssembly

open Real

/-! ### 1. The gate arithmetic

    This is the step that was wrong.  `s = q/(1-q) * P12/S_e`, and the paper needs `|s| < 1`.
    From a numerator bound `K tau^{3/2}` and a denominator bound `c sqrt(tau)` one gets
    `|s| <= (K/c) * tau/(e^tau - 1) <= K/c`, so the gate closes **iff `K < c`**. -/

/-- `q/(1-q) = 1/(e^tau - 1)` for `q = e^{-tau}`, `tau > 0`. -/
theorem q_ratio {τ : ℝ} (hτ : 0 < τ) :
    Real.exp (-τ) / (1 - Real.exp (-τ)) = 1 / (Real.exp τ - 1) := by
  have h1 : (1:ℝ) < Real.exp τ := by
    have := Real.add_one_le_exp τ; linarith
  have hne : Real.exp τ - 1 ≠ 0 := by linarith
  have hpos : Real.exp τ ≠ 0 := ne_of_gt (Real.exp_pos τ)
  have hexp : Real.exp (-τ) = 1 / Real.exp τ := by
    rw [Real.exp_neg, inv_eq_one_div]
  rw [hexp]
  field_simp

/-- **The gate ratio.**  With `|P| <= K tau^{3/2}` and `c sqrt(tau) <= |S_e|`, the gate
    quantity is `< 1` provided `K < c`.  The hypothesis `hKc` is not decoration: it is the
    entire content of the step, and it is what a numerator bound alone cannot supply.
    (`0 <= K` is not assumed: it follows from `hP`, since `|P| >= 0` and `tau sqrt(tau) > 0`.) -/
theorem gate_ratio_lt_one {τ K c P Se : ℝ}
    (hτ : 0 < τ) (hc : 0 < c) (hKc : K < c)
    (hP : |P| ≤ K * (τ * Real.sqrt τ))
    (hS : c * Real.sqrt τ ≤ |Se|) :
    |P / ((Real.exp τ - 1) * Se)| < 1 := by
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hτe : τ ≤ Real.exp τ - 1 := by
    have := Real.add_one_le_exp τ
    linarith
  have hE : 0 < Real.exp τ - 1 := lt_of_lt_of_le hτ hτe
  have hSpos : 0 < |Se| := lt_of_lt_of_le (by positivity) hS
  have hSne : Se ≠ 0 := by
    intro h; rw [h, abs_zero] at hSpos; exact lt_irrefl 0 hSpos
  rw [abs_div, abs_mul, abs_of_pos hE, div_lt_one (by positivity)]
  calc |P| ≤ K * (τ * Real.sqrt τ) := hP
    _ < c * (τ * Real.sqrt τ) := by
        have hpos : (0:ℝ) < τ * Real.sqrt τ := by positivity
        exact mul_lt_mul_of_pos_right hKc hpos
    _ ≤ (Real.exp τ - 1) * (c * Real.sqrt τ) := by
        have hcs : (0:ℝ) ≤ c * Real.sqrt τ := by positivity
        calc c * (τ * Real.sqrt τ) = (c * Real.sqrt τ) * τ := by ring
          _ ≤ (c * Real.sqrt τ) * (Real.exp τ - 1) :=
              mul_le_mul_of_nonneg_left hτe hcs
          _ = (Real.exp τ - 1) * (c * Real.sqrt τ) := by ring
    _ ≤ (Real.exp τ - 1) * |Se| := mul_le_mul_of_nonneg_left hS (le_of_lt hE)

/-! ### 2. The denominator bound of `app:Se`

    `S_e = (qZ/2) s(Z) - P12` is an identity, so a lower bound on `|s(Z)|` and an upper
    bound on `|P12|` give a lower bound on `|S_e|`.  This is how the same certificate that
    bounds the numerator also bounds the denominator. -/

/-- From the exact identity and `0.90 <= |sZ|`, the denominator bound. -/
theorem Se_lower {Se P halfqZ sZ : ℝ}
    (hid : Se = halfqZ * sZ - P) (hq : 0 ≤ halfqZ) (hsZ : (0.90 : ℝ) ≤ |sZ|) :
    0.90 * halfqZ - |P| ≤ |Se| := by
  have h1 : |halfqZ * sZ| - |P| ≤ |halfqZ * sZ - P| := abs_sub_abs_le_abs_sub _ _
  have h2 : 0.90 * halfqZ ≤ |halfqZ * sZ| := by
    rw [abs_mul, abs_of_nonneg hq]
    calc (0.90:ℝ) * halfqZ = halfqZ * 0.90 := by ring
      _ ≤ halfqZ * |sZ| := mul_le_mul_of_nonneg_left hsZ hq
  rw [hid]
  linarith

/-! ### 3. Infinitely many uncancelled poles defeat algebraicity -/

variable {Series : Type*}

/-- If a set of genuine poles of `U` is infinite while algebraicity would force the pole set
    to be finite, `U` is not algebraic.  This is the shape of the final step of `thm:V` and
    `thm:U`. -/
theorem not_alg_of_infinite_poles
    {Poles : Series → Set ℝ} {IsAlg : Series → Prop} {U : Series} {S : Set ℝ}
    (hSub : S ⊆ Poles U) (hInf : S.Infinite) (hfin : IsAlg U → (Poles U).Finite) :
    ¬ IsAlg U := fun h => hInf ((hfin h).subset hSub)

/-! ### 4. The assembly -/

/-- **Theorem `thm:U`, assembled.**  Every hypothesis is one of the paper's lemmas; the
    proof is the composition Lean checks.

    Read the hypothesis list as the audit: this is exactly what U's transcendence rests on. -/
theorem U_not_algebraic
    {Poles : Series → Set ℝ} {IsAlg : Series → Prop}
    (U : Series) (S : Set ℝ) (P12 Se b0 : ℝ → ℝ) (K c : ℝ)
    -- the travel poles are positive parameters, and there are infinitely many  [lem:infpoles]
    (hSpos : ∀ τ ∈ S, 0 < τ)
    (hInf  : S.Infinite)
    -- the two quantitative inputs, and the inequality that makes the gate close
    (hc : 0 < c) (hKc : K < c)
    (hstar : ∀ τ ∈ S, |P12 τ| ≤ K * (τ * Real.sqrt τ))          -- [thm:star]
    (hSe   : ∀ τ ∈ S, c * Real.sqrt τ ≤ |Se τ|)                 -- [app:Se]
    (hb0   : ∀ τ ∈ S, 0 < b0 τ)                                 -- [app:gate]
    -- the supplement's reduction: the full gate gives an uncancelled pole      [S lifting]
    (hred  : ∀ τ ∈ S, 0 < b0 τ →
              |P12 τ / ((Real.exp τ - 1) * Se τ)| < 1 → τ ∈ Poles U)
    -- an algebraic function has finitely many poles in the unit disc           [thm:V step]
    (hfin  : IsAlg U → (Poles U).Finite) :
    ¬ IsAlg U := by
  refine not_alg_of_infinite_poles (fun τ hτS => ?_) hInf hfin
  exact hred τ hτS (hb0 τ hτS)
    (gate_ratio_lt_one (hSpos τ hτS) hc hKc (hstar τ hτS) (hSe τ hτS))

/-! ### 5. The paper's constants, and the round-9 defect

    `thm:star` gives `K = 0.619`; `app:Se` gives `c = 0.63`.  These satisfy `K < c`, with
    the margin that makes `|s| <= 0.983 < 1`. -/

/-- The paper's constants close the gate. -/
theorem paper_constants : (0.619 : ℝ) < 0.63 := by norm_num

/-- **The round-9 defect, as a Lean statement.**  Before `app:Se`, the only proved
    denominator constant was `prop:selower`'s `0.35`.  With `K = 0.619` and `c = 0.35` the
    hypothesis `hKc` of `gate_ratio_lt_one` is false, so the gate could not be closed --
    which is exactly what the review found, and what the new denominator bound repaired. -/
theorem round9_defect : ¬ ((0.619 : ℝ) < 0.35) := by norm_num

end UAssembly
