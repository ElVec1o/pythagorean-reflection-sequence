/-
  AtomN.lean
  ==========
  Machine-checked verification of "Atom N" — the amplitude atom of the U-gate
  transcendence proof (route_b/amplitude_bound.tex, Lemma `lem:twobessel`).

  The two-Bessel confluence gives the envelope A/A_cl = 1 + τ·h(X) + O(τ²) with
  O(τ) coefficient
        h(X) = (1 + 3/(2X²)) / (1 + 1/X²),
  obtained from the half-integer cross-term identity
        j₃⁄₂·j₅⁄₂ + y₃⁄₂·y₅⁄₂ = 3/X³ + 2/X          (Theorem `cross_term`)
  (the reduced spherical-Bessel components, prefactor √(2/πX) stripped), which is
  equivalent to  J₃⁄₂J₅⁄₂ + Y₃⁄₂Y₅⁄₂ = (4/πX²)(1 + 3/(2X²)).

  The Atom N closure is that h is uniformly bounded:
        1 ≤ h(X) ≤ 3/2   for all X > 0                (Theorem `h_bounds`).
  This is exactly what makes γ/γ_cl = 1 + O(τ) with explicit constant 3/2 —
  no saddle, no turning-point analysis. Everything below is closed by `ring` /
  `nlinarith` from the single fact sin²+cos²=1, with no `sorry`.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real

namespace AtomN

/-- Reduced spherical-Bessel components at ν = 3/2 and 5/2 (prefactor √(2/πX) stripped). -/
noncomputable def j32 (X : ℝ) : ℝ := sin X / X - cos X
noncomputable def y32 (X : ℝ) : ℝ := -cos X / X - sin X
noncomputable def j52 (X : ℝ) : ℝ := (3 / X ^ 2 - 1) * sin X - (3 / X) * cos X
noncomputable def y52 (X : ℝ) : ℝ := (1 - 3 / X ^ 2) * cos X - (3 / X) * sin X

/-- **Cross-term identity.** j₃⁄₂j₅⁄₂ + y₃⁄₂y₅⁄₂ = 3/X³ + 2/X, from sin²+cos²=1.
    (The sin·cos cross terms cancel; the sin²+cos² collapses to 1.) -/
theorem cross_term (X : ℝ) :
    j32 X * j52 X + y32 X * y52 X = 3 / X ^ 3 + 2 / X := by
  simp only [j32, y32, j52, y52]
  linear_combination (3 / X ^ 3 + 2 / X) * sin_sq_add_cos_sq X

/-- Reduced components at ν = ∓1/2 (the *denominator* pair, block `S_e`):
    j₋₁⁄₂ = cos X, j₁⁄₂ = sin X, y₋₁⁄₂ = sin X, y₁⁄₂ = -cos X. -/
noncomputable def jm12 (X : ℝ) : ℝ := Real.cos X
noncomputable def j12  (X : ℝ) : ℝ := Real.sin X
noncomputable def ym12 (X : ℝ) : ℝ := Real.sin X
noncomputable def y12  (X : ℝ) : ℝ := -Real.cos X

/-- **Denominator cross-term vanishes.** j₋₁⁄₂·j₁⁄₂ + y₋₁⁄₂·y₁⁄₂ = 0.
    In contrast to `cross_term` (the numerator's ν = 3/2,5/2 pair, which is nonzero),
    the ν = ±1/2 denominator pair has a vanishing cross-term. Hence the two-Bessel
    confluence of `S_e` carries *no* O(τ) amplitude correction: it reproduces `cos W`
    exactly at that order, and the deviation `T_2` is a pure phase (saddle) effect — the
    structural reason the denominator estimate needs stationary phase (`rem:gaussint`)
    whereas the numerator amplitude closes algebraically (`h_bounds`). -/
theorem cross_term_half (X : ℝ) : jm12 X * j12 X + ym12 X * y12 X = 0 := by
  simp only [jm12, j12, ym12, y12]; ring

/-- The envelope coefficient. -/
noncomputable def h (X : ℝ) : ℝ := (1 + 3 / (2 * X ^ 2)) / (1 + 1 / X ^ 2)

/-- `h` in cleared form: h(X) = (X² + 3/2)/(X² + 1). -/
theorem h_eq (X : ℝ) (hX : X ≠ 0) : h X = (X ^ 2 + 3 / 2) / (X ^ 2 + 1) := by
  have hX2 : X ^ 2 ≠ 0 := pow_ne_zero 2 hX
  unfold h
  field_simp
  ring

/-- **Atom N closure.** 1 ≤ h(X) ≤ 3/2 for every X > 0. -/
theorem h_bounds (X : ℝ) (hX : 0 < X) : 1 ≤ h X ∧ h X ≤ 3 / 2 := by
  have hXne : X ≠ 0 := ne_of_gt hX
  have hX2 : (0 : ℝ) < X ^ 2 := by positivity
  rw [h_eq X hXne]
  have hd : (0 : ℝ) < X ^ 2 + 1 := by positivity
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith

/-- Consequently the amplitude correction is uniformly O(τ): |h(X)| ≤ 3/2. -/
theorem h_le_three_halves (X : ℝ) (hX : 0 < X) : |h X| ≤ 3 / 2 := by
  have ⟨h1, h2⟩ := h_bounds X hX
  rw [abs_of_nonneg (by linarith)]
  exact h2

end AtomN

-- Axiom audit: confirm no `sorry`, only Lean's foundational axioms.
#print axioms AtomN.cross_term
#print axioms AtomN.cross_term_half
#print axioms AtomN.h_eq
#print axioms AtomN.h_bounds
#print axioms AtomN.h_le_three_halves
