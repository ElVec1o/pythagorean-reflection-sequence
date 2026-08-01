/-
The linear part of a product of reflections, which is part (i) of the
rotation-relations theorem.

A reflection of the plane in a line of direction `θ` is `z ↦ e^{2iθ} conj z + b`.
Composing, the conjugations alternate, so the linear coefficient of
`r_{a_1} ⋯ r_{a_L}` is

    exp (2i (θ_{a_1} - θ_{a_2} + θ_{a_3} - ⋯))  =  exp (2i Σ_i c_i(w) θ_i),

with `c_i` the signed occurrence count already used in `RotationRelations.lean`.
That alternation is exactly the recursion defining `cvec`, so the two
developments share the invariant.

The consequence is `linOf_of_cvec_two_eq_zero`: normalising `θ₀ = 0` and
`θ₁ = π/m`, the linear part is `exp (2πi c₁/m)`, the rotation by `2πc₁/m`,
as soon as `c₂ = 0` -- and it is then the same at every shape of the stratum,
since `θ₂` has dropped out. `linOf_depends_on_theta_two` is the converse: when
`c₂ ≠ 0` the linear part does move with the shape.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import RotationRelations

namespace LinearPart

open Complex RotationRelations

/-- The linear coefficient of the product of the reflections named by a word.
The head reflection contributes `exp (2iθ)` and conjugates the rest. -/
noncomputable def linOf (θ : Letter → ℝ) : List Letter → ℂ
  | [] => 1
  | l :: w => Complex.exp (2 * Complex.I * (θ l : ℂ)) * (starRingEnd ℂ) (linOf θ w)

/-- The total turning of a word, `Σ_i c_i(w) θ_i`. -/
def turn (θ : Letter → ℝ) (w : List Letter) : ℝ :=
  (cvec w 0 : ℝ) * θ 0 + (cvec w 1 : ℝ) * θ 1 + (cvec w 2 : ℝ) * θ 2

@[simp] theorem turn_nil (θ : Letter → ℝ) : turn θ [] = 0 := by
  simp [turn, cvec]

theorem turn_cons (θ : Letter → ℝ) (l : Letter) (w : List Letter) :
    turn θ (l :: w) = θ l - turn θ w := by
  fin_cases l <;>
    · simp only [turn, cvec]
      push_cast
      norm_num
      ring

/-- The linear part is the exponential of twice the turning. This is the
formula in part (i) of the rotation-relations theorem. -/
theorem linOf_eq (θ : Letter → ℝ) (w : List Letter) :
    linOf θ w = Complex.exp (2 * Complex.I * (turn θ w : ℂ)) := by
  induction w with
  | nil => simp [linOf]
  | cons l w ih =>
      rw [linOf, ih, turn_cons]
      rw [← Complex.exp_conj]
      rw [← Complex.exp_add]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast
      ring

/-- On the stratum of angle `π/m`, normalising `θ₀ = 0` and `θ₁ = π/m`, a word
whose second invariant vanishes has linear part the rotation by `2πc₁/m`. The
third direction `θ₂` has dropped out, so this is the same at every shape of the
stratum. -/
theorem linOf_of_cvec_two_eq_zero (m : ℕ) (θ : Letter → ℝ) (w : List Letter)
    (h0 : θ 0 = 0) (h1 : θ 1 = Real.pi / m) (h2 : cvec w 2 = 0) :
    linOf θ w = Complex.exp (2 * Real.pi * Complex.I * (cvec w 1 : ℂ) / m) := by
  rw [linOf_eq, turn, h0, h1, h2]
  congr 1
  push_cast
  ring

/-- The converse: if the second invariant does not vanish, the linear part
really does move with the shape, so it is not the same at every shape of the
stratum. -/
theorem linOf_depends_on_theta_two (θ θ' : Letter → ℝ) (w : List Letter)
    (hne : turn θ w - turn θ' w ≠ 0)
    (hsmall : |turn θ w - turn θ' w| < Real.pi) :
    linOf θ w ≠ linOf θ' w := by
  rw [linOf_eq, linOf_eq]
  intro hEq
  rw [Complex.exp_eq_exp_iff_exists_int] at hEq
  obtain ⟨k, hk⟩ := hEq
  have hI : Complex.I *
      (((2 * turn θ w - 2 * turn θ' w - k * (2 * Real.pi) : ℝ)) : ℂ) = 0 := by
    push_cast
    linear_combination hk
  have hr : (2 * turn θ w - 2 * turn θ' w - k * (2 * Real.pi) : ℝ) = 0 := by
    rcases mul_eq_zero.mp hI with h | h
    · exact absurd h Complex.I_ne_zero
    · exact_mod_cast h
  have hk0 : (k : ℝ) = 0 := by
    by_contra hc
    have hkz : k ≠ 0 := by exact_mod_cast hc
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hkz
    have h2 : |turn θ w - turn θ' w| = |(k : ℝ)| * Real.pi := by
      have hd : turn θ w - turn θ' w = (k : ℝ) * Real.pi := by linarith
      rw [hd, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  apply hne
  rw [hk0] at hr
  linarith

end LinearPart

-- Rule 5 axiom audit (added 2026-08-01): declare every axiom these results rest on.
#print axioms LinearPart.turn_nil
#print axioms LinearPart.turn_cons
#print axioms LinearPart.linOf_eq
#print axioms LinearPart.linOf_of_cvec_two_eq_zero
#print axioms LinearPart.linOf_depends_on_theta_two
