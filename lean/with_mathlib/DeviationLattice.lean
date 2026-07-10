/-
  DeviationLattice.lean
  =====================
  Machine-checked algebraic facts underpinning the deviation-depth law of Paper 1
  (Proposition `prop:deviation-law`, Lemma `lem:finite-svp`, Remark `rem:l1-insufficient`).

  The shape complexity of a triangle T is packaged in the palindromic quadratic
        μ_T(t) = c_T t² − e_T t + c_T,          0 < e_T < 2 c_T,
  the minimal polynomial of the rotation number ζ_T. Three facts are formalized:

  1. `mu_selfReciprocal` — μ_T is self-reciprocal: t² μ_T(1/t) = μ_T(t).  This is why
     conjugation stabilizes the kernel ideal (Corollary `cor:kernel-classification`).

  2. `mu_root_normSq_one` / `mu_root_abs_one` — BOTH roots of μ_T lie on the unit circle.
     This is the crux of `rem:l1-insufficient`: because the roots are on |t|=1 (and, by
     Niven, are not roots of unity) the ℓ¹-norm ‖μ_T m‖₁ need not grow with deg m, so the
     ℓ¹ bound alone does NOT terminate the shortest-vector search — the travel/span bound
     of `lem:finite-svp` is genuinely required.

  3. `window_60`, `window_5637` — the two angle-window boundaries of the law, e_T = c_T and
     e_T = ¾c_T, are exactly b² = 3a² (β = 60°) and 5b² = 11a² (tan β = √(11/5)).

  Everything is closed by `ring` / `nlinarith` / `field_simp`; no `sorry`.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace DeviationLattice

/-- The shape polynomial μ_T(t) = c t² − e t + c, over any field. -/
def mu (c e t : ℝ) : ℝ := c * t ^ 2 - e * t + c

/-- **Self-reciprocity (palindrome).** t² μ(1/t) = μ(t) for t ≠ 0. -/
theorem mu_selfReciprocal (c e t : ℝ) (ht : t ≠ 0) :
    t ^ 2 * mu c e (1 / t) = mu c e t := by
  unfold mu
  field_simp
  ring

/-- **Roots on the unit circle, real form.** If ρ = x + iy satisfies the real and
    imaginary parts of c ρ² − e ρ + c = 0, with 0 < e < 2c, then x² + y² = 1.
    (The imaginary part forces y(2cx − e) = 0; a real root y = 0 is impossible since the
    discriminant e² − 4c² is negative, so 2cx = e, and the real part then gives x²+y²=1.) -/
theorem mu_root_normSq_one (c e x y : ℝ) (hc : 0 < c) (he0 : 0 < e) (he : e < 2 * c)
    (hre : c * (x ^ 2 - y ^ 2) - e * x + c = 0) (him : c * (2 * x * y) - e * y = 0) :
    x ^ 2 + y ^ 2 = 1 := by
  have hy : y * (2 * c * x - e) = 0 := by linarith [him]
  rcases mul_eq_zero.mp hy with hy0 | hcx
  · exfalso
    rw [hy0] at hre
    nlinarith [sq_nonneg (2 * c * x - e), hre, hc, he0, he]
  · have hxe : e = 2 * c * x := by linarith
    have hc' : c ≠ 0 := ne_of_gt hc
    have : c * (x ^ 2 + y ^ 2 - 1) = 0 := by nlinarith [hre, hxe]
    have h2 : x ^ 2 + y ^ 2 - 1 = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hc'
      · exact h
    linarith [h2]

/-- **Roots on the unit circle, complex form.** Every complex root of c t² − e t + c
    (with 0 < e < 2c) has modulus 1. -/
theorem mu_root_abs_one (c e : ℝ) (hc : 0 < c) (he0 : 0 < e) (he : e < 2 * c)
    (ρ : ℂ) (hρ : (c : ℂ) * ρ ^ 2 - (e : ℂ) * ρ + (c : ℂ) = 0) :
    ‖ρ‖ = 1 := by
  have h1 := congrArg Complex.re hρ
  have h2 := congrArg Complex.im hρ
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
    Complex.zero_im, mul_zero, zero_mul, sub_zero, add_zero] at h1 h2
  have hre : c * (ρ.re ^ 2 - ρ.im ^ 2) - e * ρ.re + c = 0 := by ring_nf; ring_nf at h1; linarith [h1]
  have him : c * (2 * ρ.re * ρ.im) - e * ρ.im = 0 := by ring_nf; ring_nf at h2; linarith [h2]
  have hns : ρ.re ^ 2 + ρ.im ^ 2 = 1 := mu_root_normSq_one c e ρ.re ρ.im hc he0 he hre him
  have hsq : ‖ρ‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [hns]
  have h0 : 0 ≤ ‖ρ‖ := norm_nonneg ρ
  calc ‖ρ‖ = Real.sqrt (‖ρ‖ ^ 2) := (Real.sqrt_sq h0).symm
    _ = Real.sqrt 1 := by rw [hsq]
    _ = 1 := Real.sqrt_one

/-- **Angle window β = 60°.** The boundary e_T = c_T of the deviation law is b² = 3a²,
    i.e. tan β = b/a = √3, β = 60°.  (Here c_T = a²+b², e_T = 2(b²−a²).) -/
theorem window_60 (a b : ℝ) :
    2 * (b ^ 2 - a ^ 2) = a ^ 2 + b ^ 2 ↔ b ^ 2 = 3 * a ^ 2 := by
  constructor <;> intro h <;> linarith

/-- **Angle window tan β = √(11/5).** The boundary e_T = ¾c_T is 5b² = 11a². -/
theorem window_5637 (a b : ℝ) :
    8 * (b ^ 2 - a ^ 2) = 3 * (a ^ 2 + b ^ 2) ↔ 5 * b ^ 2 = 11 * a ^ 2 := by
  constructor <;> intro h <;> linarith

end DeviationLattice

-- Axiom audit: only Lean's foundational axioms, no `sorry`.
#print axioms DeviationLattice.mu_selfReciprocal
#print axioms DeviationLattice.mu_root_normSq_one
#print axioms DeviationLattice.mu_root_abs_one
#print axioms DeviationLattice.window_60
#print axioms DeviationLattice.window_5637
