/-
EffUnivCore.lean
================
Arithmetic core of `thm:effective-universality` (`paper1.tex`).

For a shape `T` with arithmetic complexity `c_T = A` and `e_T = E`, the minimal polynomial is
`mu_T = A t^2 - E t + A` (primitive, with `0 < E < 2A`, so its roots are non-real).  The theorem's
proof is: a nonzero `D~ ∈ Z[t]` vanishing at `zeta_T` is divisible by `mu_T` in `Z[t]` (Gauss), so
`A` divides the leading and constant coefficients of `D~`; if all coefficients are at most `M` in
absolute value, then `A <= M`.

Proved here, for any complex root `zeta` of such a `mu`:
  * `mu_dvd`       : `D(zeta) = 0` and `D ∈ Z[t]` imply `mu ∣ D` in `Z[t]`;
  * `lead_dvd`, `const_dvd` : `A` divides the leading and the constant coefficient;
  * `complexity_le_bound`   : a nonzero such `D` with `|coeff| <= M` forces `A <= M`;
  * `no_collision_of_large_complexity` : the contrapositive, `A > M` excludes any such `D`.

NOT formalised: that a depth-`d` deviation produces such a `D` with `M = 2d`
(`prop:collision-vanishing`, `lem:symbolic-form`), which needs the lamplighter word machinery.
No sorry.
-/
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.SpecificDegree

namespace EffUnivCore

open Polynomial

/-- `mu = A t^2 - E t + A`. -/
noncomputable def mu (A E : ℤ) : ℤ[X] := C A * X ^ 2 - C E * X + C A

theorem mu_natDegree (A E : ℤ) (hA : A ≠ 0) : (mu A E).natDegree = 2 := by
  unfold mu
  compute_degree!

theorem mu_coeff2 (A E : ℤ) : (mu A E).coeff 2 = A := by
  simp only [mu, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

theorem mu_coeff0 (A E : ℤ) : (mu A E).coeff 0 = A := by
  simp only [mu, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

variable {A E : ℤ}

/-- `mu` has no rational root when `0 < E < 2A`. -/
theorem mu_no_rat_root (hA : 0 < A) (hE : 0 < E) (hE2 : E < 2 * A) (q : ℚ) :
    ((mu A E).map (Int.castRingHom ℚ)).eval q ≠ 0 := by
  have e : ((mu A E).map (Int.castRingHom ℚ)).eval q = (A : ℚ) * q ^ 2 - E * q + A := by
    simp only [mu, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow]
    simp
  rw [e]
  have hA' : (0 : ℚ) < A := by exact_mod_cast hA
  have hE' : (E : ℚ) < 2 * A := by exact_mod_cast hE2
  have hE0 : (0 : ℚ) < E := by exact_mod_cast hE
  intro h
  nlinarith [sq_nonneg ((A : ℚ) * q - E / 2), sq_nonneg q, mul_pos hA' hA']

theorem mu_leadingCoeff (hA : A ≠ 0) : (mu A E).leadingCoeff = A := by
  rw [Polynomial.leadingCoeff, mu_natDegree A E hA, mu_coeff2]

/-- Gauss: a polynomial in `Z[t]` vanishing at a root of `mu` is divisible by `mu`. -/
theorem mu_dvd (hA : 0 < A) (hE : 0 < E) (hE2 : E < 2 * A) (hprim : (mu A E).IsPrimitive)
    (ζ : ℂ) (hζ : aeval ζ (mu A E) = 0) (D : ℤ[X]) (hD : aeval ζ D = 0) : mu A E ∣ D := by
  by_cases hD0' : D = 0
  · rw [hD0']; exact dvd_zero _
  set μQ : ℚ[X] := (mu A E).map (Int.castRingHom ℚ) with hμQ
  set DQ : ℚ[X] := D.map (Int.castRingHom ℚ) with hDQ
  have hμ0 : aeval ζ μQ = 0 := by
    rw [hμQ, ← algebraMap_int_eq (R := ℚ), Polynomial.aeval_map_algebraMap]; exact hζ
  have hD0 : aeval ζ DQ = 0 := by
    rw [hDQ, ← algebraMap_int_eq (R := ℚ), Polynomial.aeval_map_algebraMap]; exact hD
  have hdeg : μQ.natDegree = 2 := by
    rw [hμQ, Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact mu_natDegree A E hA.ne'
  have hirr : Irreducible μQ :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (by rw [Finset.mem_Icc]; omega) (fun q hq => mu_no_rat_root hA hE hE2 q hq)
  have hmin := minpoly.eq_of_irreducible hirr hμ0
  have h1 : minpoly ℚ ζ ∣ DQ := minpoly.dvd ℚ ζ hD0
  rw [← hmin] at h1
  have hμDQ : μQ ∣ DQ := (dvd_mul_right μQ _).trans h1
  -- pass to the primitive part of `D`
  have hcont : D.content ≠ 0 := by
    intro h; exact hD0' (Polynomial.content_eq_zero_iff.mp h)
  have hDeq : D = C D.content * D.primPart := Polynomial.eq_C_content_mul_primPart D
  have hPQ : (D.primPart).map (Int.castRingHom ℚ) = C ((D.content : ℚ)⁻¹) * DQ := by
    have : DQ = C (D.content : ℚ) * (D.primPart).map (Int.castRingHom ℚ) := by
      conv_lhs => rw [hDQ, hDeq]
      rw [Polynomial.map_mul, Polynomial.map_C]
      simp
    rw [this, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (by exact_mod_cast hcont), C_1, one_mul]
  have hμP : μQ ∣ (D.primPart).map (Int.castRingHom ℚ) := by
    rw [hPQ]; exact Dvd.dvd.mul_left hμDQ _
  have hPdvd : mu A E ∣ D.primPart :=
    (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ hprim
      (Polynomial.isPrimitive_primPart D)).mpr hμP
  rw [hDeq]
  exact Dvd.dvd.mul_left hPdvd _

theorem lead_dvd (hA : 0 < A) (hE : 0 < E) (hE2 : E < 2 * A) (hprim : (mu A E).IsPrimitive)
    (ζ : ℂ) (hζ : aeval ζ (mu A E) = 0) (D : ℤ[X]) (hD : aeval ζ D = 0) :
    A ∣ D.leadingCoeff := by
  obtain ⟨F, hF⟩ := mu_dvd hA hE hE2 hprim ζ hζ D hD
  rw [hF, Polynomial.leadingCoeff_mul, mu_leadingCoeff hA.ne']
  exact dvd_mul_right _ _

theorem const_dvd (hA : 0 < A) (hE : 0 < E) (hE2 : E < 2 * A) (hprim : (mu A E).IsPrimitive)
    (ζ : ℂ) (hζ : aeval ζ (mu A E) = 0) (D : ℤ[X]) (hD : aeval ζ D = 0) :
    A ∣ D.coeff 0 := by
  obtain ⟨F, hF⟩ := mu_dvd hA hE hE2 hprim ζ hζ D hD
  rw [hF, Polynomial.mul_coeff_zero, mu_coeff0]
  exact dvd_mul_right _ _

/-- **Core of `thm:effective-universality`.**  A nonzero `D ∈ Z[t]` vanishing at `zeta_T` with
all coefficients bounded by `M` forces `c_T <= M`. -/
theorem complexity_le_bound (hA : 0 < A) (hE : 0 < E) (hE2 : E < 2 * A)
    (hprim : (mu A E).IsPrimitive) (ζ : ℂ) (hζ : aeval ζ (mu A E) = 0) (D : ℤ[X]) (hD : aeval ζ D = 0)
    (hD0 : D ≠ 0) (M : ℤ) (hM : ∀ k, |D.coeff k| ≤ M) : A ≤ M := by
  have hdvd := lead_dvd hA hE hE2 hprim ζ hζ D hD
  have hne : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD0
  have h1 : A ≤ |D.leadingCoeff| :=
    Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  exact h1.trans (hM _)

/-- Contrapositive: if `c_T > M` no nonzero integer polynomial with coefficients `<= M` vanishes
at `zeta_T`. -/
theorem no_collision_of_large_complexity (hA : 0 < A) (hE : 0 < E) (hE2 : E < 2 * A)
    (hprim : (mu A E).IsPrimitive) (ζ : ℂ) (hζ : aeval ζ (mu A E) = 0) (M : ℤ) (hAM : M < A)
    (D : ℤ[X]) (hD0 : D ≠ 0) (hM : ∀ k, |D.coeff k| ≤ M) : aeval ζ D ≠ 0 := by
  intro hD
  have := complexity_le_bound hA hE hE2 hprim ζ hζ D hD hD0 M hM
  omega

theorem mu_coeff1 (A E : ℤ) : (mu A E).coeff 1 = -E := by
  simp only [mu, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- `mu` is primitive as soon as `gcd(A, E) = 1`. -/
theorem mu_isPrimitive (h : IsCoprime A E) : (mu A E).IsPrimitive := by
  intro r hr
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
  have h0 := hr 0
  have h1 := hr 1
  rw [mu_coeff0] at h0
  rw [mu_coeff1] at h1
  exact h.isUnit_of_dvd' h0 ((dvd_neg).mp h1)

/-- For the shape `T = (a, b)`: `zeta_T = (a + bi)/(a - bi)` is a root of
`mu_T = (a^2+b^2) t^2 - 2(a^2-b^2) t + (a^2+b^2)` (the case `a + b` odd, `c_T = a^2 + b^2`,
`e_T = 2(a^2 - b^2)`). -/
theorem zeta_root (a b : ℤ) (hb : 0 < b) :
    aeval (((a : ℂ) + b * Complex.I) / ((a : ℂ) - b * Complex.I))
      (mu (a ^ 2 + b ^ 2) (2 * (a ^ 2 - b ^ 2))) = 0 := by
  have hne : ((a : ℂ) - b * Complex.I) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    omega
  simp only [mu, map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_pow, Int.cast_mul,
    Int.cast_sub, Int.cast_ofNat]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end EffUnivCore

#print axioms EffUnivCore.mu_no_rat_root
#print axioms EffUnivCore.complexity_le_bound
#print axioms EffUnivCore.no_collision_of_large_complexity
#print axioms EffUnivCore.zeta_root
#print axioms EffUnivCore.mu_isPrimitive
