/-
  GaussHS.lean
  ============
  Machine-checked analytic backbone of the Hubbard–Stratonovich representation
  (route_b/paper2.tex, rem:gaussint, eq:HS) of the denominator block S_e.

  The representation
        S_e = (4πτ)^{-1/2} ∫_ℝ e^{-u²/(4τ)} Ψ(u,q) du,   Ψ(u,q)=Σ_j Z^j/(q;q)_{2j},
  rests, term by term, on the single Gaussian-moment identity
        ∫_ℝ e^{-u²/(4τ)+iju} du = √(4πτ) · e^{-τ j²}        (τ>0, j∈ℝ),
  since  q^{j(j+1)} = q^j · e^{-τ j²}  and  Z = -2(1-q)q e^{iu}.

  We prove this identity from Mathlib's Gaussian Fourier transform
  `integral_cexp_neg_mul_sq_add_real_mul_I` (b = 1/(4τ), c = -2τj), with no `sorry`.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic

open Complex MeasureTheory
open scoped Real

namespace GaussHS

/-- **Gaussian moment.** For `τ > 0` and `j ∈ ℝ`,
      `∫_ℝ exp(-u²/(4τ) + i·j·u) du = √(4πτ) · exp(-τ j²)`.
    This is the exact identity that turns `q^{j(j+1)}` into the real Gaussian integral
    of `eq:HS`; the interchange with the (absolutely convergent) `j`-sum then gives the
    representation of `S_e`. -/
theorem gaussian_moment (τ : ℝ) (hτ : 0 < τ) (j : ℝ) :
    (∫ u : ℝ, Complex.exp (-(u : ℂ) ^ 2 / (4 * τ) + Complex.I * j * u))
      = (Real.sqrt (4 * Real.pi * τ) : ℂ) * Complex.exp (-(τ : ℂ) * j ^ 2) := by
  have hτc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  set b : ℂ := 1 / (4 * τ) with hb
  -- 0 < Re b
  have hbre : 0 < b.re := by
    have : b = ((1 / (4 * τ) : ℝ) : ℂ) := by rw [hb]; push_cast; ring
    rw [this, Complex.ofReal_re]; positivity
  -- pointwise: integrand = exp(-τ j²) · exp(-b·(u + (-2τj)·I)²)
  have key : ∀ u : ℝ,
      Complex.exp (-(u : ℂ) ^ 2 / (4 * τ) + Complex.I * j * u)
        = Complex.exp (-(τ : ℂ) * j ^ 2)
          * Complex.exp (-b * ((u : ℂ) + ((-2 * τ * j : ℝ) : ℂ) * Complex.I) ^ 2) := by
    intro u
    rw [← Complex.exp_add]
    congr 1
    rw [hb]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    field_simp
    linear_combination (4 * (τ : ℂ) ^ 2 * (j : ℂ) ^ 2) * hI
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul,
    GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I hbre (-2 * τ * j)]
  -- (π/b)^{1/2} = √(4πτ)
  have hpb : (Real.pi : ℂ) / b = ((4 * Real.pi * τ : ℝ) : ℂ) := by
    rw [hb]; push_cast; field_simp; ring
  rw [hpb]
  have hnn : (0 : ℝ) ≤ 4 * Real.pi * τ := by positivity
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hnn, ← Real.sqrt_eq_rpow]
  ring

end GaussHS

#print axioms GaussHS.gaussian_moment
