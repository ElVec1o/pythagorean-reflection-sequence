/-
  RoundNorm.lean -- room E, seat E3.  The abstract core of paper1 `prop:round-norm`
  (section 8, rational triangles, "The stable norm is round").

  Setting.  `s : ℂ → ℝ` is
    * subadditive:                s (v + w) ≤ s v + s w,
    * positively homogeneous:     s (t * v) = t * s v  for real t ≥ 0,
    * invariant under a rotation: s (ζ * v) = s v, with ‖ζ‖ = 1 and ζ not a root of unity.

  Results.
    * `lipschitz_of_bounded`   : if moreover `s ≤ M` on the unit circle, then
                                 |s v - s w| ≤ M * ‖v - w‖   (so `s` is continuous);
    * `round_of_continuous`    : if `s` is continuous, then s v = s 1 * ‖v‖;
    * `round_of_bounded`       : the same with "continuous" replaced by "bounded above on the
                                 unit circle" (via the Lipschitz lemma);
    * `round_nonneg`           : the constant s 1 is ≥ 0.

  This is exactly the "Rotation invariance" step of the paper's proof, plus the Lipschitz
  step in abstract form: the paper's `N` is a continuous seminorm on ℂ = ℝ² invariant
  under multiplication by ζ, and we show every such function is κ·|v|.  The density input is
  Mathlib's `AddCircle.denseRange_zsmul_iff` (irrational rotations have dense orbits).

  No sorry, no native_decide.
-/
import Mathlib

namespace RoundNorm

open Complex

section Basic

variable {s : ℂ → ℝ}

/-- Homogeneity at `t = 0` gives `s 0 = 0`. -/
theorem map_zero (homog : ∀ t : ℝ, 0 ≤ t → ∀ v, s ((t : ℂ) * v) = t * s v) : s 0 = 0 := by
  have := homog 0 le_rfl 0
  simpa using this

/-- Polar decomposition: `s v = ‖v‖ * s (v / ‖v‖)`. -/
theorem polar (homog : ∀ t : ℝ, 0 ≤ t → ∀ v, s ((t : ℂ) * v) = t * s v) (v : ℂ) :
    s v = ‖v‖ * s (v / (‖v‖ : ℂ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [map_zero homog]
  · have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hv
    rw [← homog ‖v‖ (norm_nonneg v)]
    congr 1
    field_simp

theorem norm_div_norm {v : ℂ} (hv : v ≠ 0) : ‖v / (‖v‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact div_self (norm_ne_zero_iff.mpr hv)

/-- **Bounded on the circle ⇒ Lipschitz.**  If `s ≤ M` on the unit circle, then `s` is
`M`-Lipschitz.  Only subadditivity and homogeneity are used. -/
theorem lipschitz_of_bounded
    (subadd : ∀ v w, s (v + w) ≤ s v + s w)
    (homog : ∀ t : ℝ, 0 ≤ t → ∀ v, s ((t : ℂ) * v) = t * s v)
    (M : ℝ) (hM : ∀ u : ℂ, ‖u‖ = 1 → s u ≤ M) (v w : ℂ) :
    |s v - s w| ≤ M * ‖v - w‖ := by
  -- `s x ≤ M * ‖x‖` for every `x`
  have hle : ∀ x : ℂ, s x ≤ M * ‖x‖ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [map_zero homog]
    · rw [polar homog x, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM _ (norm_div_norm hx)) (norm_nonneg x)
  have h1 : s v ≤ s w + s (v - w) := by
    have := subadd w (v - w); simpa using this
  have h2 : s w ≤ s v + s (w - v) := by
    have := subadd v (w - v); simpa using this
  have h3 := hle (v - w)
  have h4 := hle (w - v)
  rw [norm_sub_rev w v] at h4
  rw [abs_le]
  constructor <;> linarith

/-- Hence `s` is continuous when it is bounded above on the unit circle. -/
theorem continuous_of_bounded
    (subadd : ∀ v w, s (v + w) ≤ s v + s w)
    (homog : ∀ t : ℝ, 0 ≤ t → ∀ v, s ((t : ℂ) * v) = t * s v)
    (M : ℝ) (hM : ∀ u : ℂ, ‖u‖ = 1 → s u ≤ M) : Continuous s := by
  refine (LipschitzWith.of_dist_le' (K := M) fun v w => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact lipschitz_of_bounded subadd homog M hM v w

/-- Invariance under every integer power of `ζ`. -/
theorem rot_zpow {ζ : ℂ} (hζ0 : ζ ≠ 0) (rot : ∀ v, s (ζ * v) = s v) :
    ∀ (n : ℤ) (v : ℂ), s (ζ ^ n * v) = s v := by
  have hnat : ∀ (n : ℕ) (v : ℂ), s (ζ ^ n * v) = s v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih => intro v; rw [pow_succ', mul_assoc, rot, ih]
  intro n v
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using hnat m v
  · have := hnat m (ζ ^ (-(m : ℤ)) * v)
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hζ0] at this
    simpa using this.symm

end Basic

section Density

/-- **Density.**  If `‖ζ‖ = 1` and `ζ` is not a root of unity, the integer powers of `ζ`
are dense in the unit circle.  (Irrational rotation, via `AddCircle.denseRange_zsmul_iff`.) -/
theorem denseRange_zpow {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hroot : ∀ n : ℕ, 0 < n → ζ ^ n ≠ 1) :
    ∃ z : Circle, (z : ℂ) = ζ ∧ DenseRange (fun n : ℤ => z ^ n) := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  set a : AddCircle (2 * Real.pi) := ((Complex.arg ζ : ℝ) : AddCircle (2 * Real.pi))
  have hza : ((AddCircle.toCircle a : Circle) : ℂ) = ζ := by
    have h := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hζ] at h
    simp only [ofReal_one, one_mul] at h
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    have : (2 * Real.pi / (2 * Real.pi) * Complex.arg ζ : ℝ) = Complex.arg ζ := by
      field_simp
    rw [this, h]
  refine ⟨AddCircle.toCircle a, hza, ?_⟩
  have hord : addOrderOf a = 0 := by
    rw [addOrderOf_eq_zero_iff']
    intro n hn hna
    apply hroot n hn
    have := congrArg (fun x => ((AddCircle.toCircle x : Circle) : ℂ)) hna
    simp only [AddCircle.toCircle_nsmul, AddCircle.toCircle_zero] at this
    rw [← hza]
    simpa using this
  have hd : DenseRange (fun n : ℤ => n • a) := AddCircle.denseRange_zsmul_iff.mpr hord
  have hsurj : Function.Surjective (@AddCircle.toCircle (2 * Real.pi)) := by
    intro z
    obtain ⟨x, rfl⟩ := Circle.exp_surjective z
    refine ⟨((x : ℝ) : AddCircle (2 * Real.pi)), ?_⟩
    rw [AddCircle.toCircle_apply_mk]
    congr 1
    field_simp
  have := hsurj.denseRange.comp hd AddCircle.continuous_toCircle
  convert this using 1
  funext n
  simp [Function.comp, AddCircle.toCircle_zsmul]

end Density

section Main

variable {s : ℂ → ℝ}

/-- **Rotation invariance (continuous form).**  A continuous function on ℂ invariant under
multiplication by `ζ` (unit modulus, not a root of unity) is constant on the unit circle. -/
theorem const_on_circle {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hroot : ∀ n : ℕ, 0 < n → ζ ^ n ≠ 1)
    (rot : ∀ v, s (ζ * v) = s v) (hcont : Continuous s) (u : ℂ) (hu : ‖u‖ = 1) :
    s u = s 1 := by
  obtain ⟨z, hz, hd⟩ := denseRange_zpow hζ hroot
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ; exact zero_ne_one hζ
  have hf : Continuous (fun w : Circle => s (w : ℂ)) := hcont.comp continuous_subtype_val
  have heq : (fun w : Circle => s (w : ℂ)) = fun _ => s 1 := by
    refine hd.equalizer hf continuous_const ?_
    funext n
    simp only [Function.comp]
    have := rot_zpow hζ0 rot n 1
    rw [mul_one] at this
    rw [← this, Circle.coe_zpow, hz]
  have hmem : u ∈ Submonoid.unitSphere ℂ := by simpa [Submonoid.unitSphere] using hu
  exact congrFun heq ⟨u, hmem⟩

/-- **The round-norm theorem (continuous form).**  `s v = s 1 * ‖v‖`. -/
theorem round_of_continuous {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hroot : ∀ n : ℕ, 0 < n → ζ ^ n ≠ 1)
    (homog : ∀ t : ℝ, 0 ≤ t → ∀ v, s ((t : ℂ) * v) = t * s v)
    (rot : ∀ v, s (ζ * v) = s v) (hcont : Continuous s) (v : ℂ) :
    s v = s 1 * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [map_zero homog]
  · rw [polar homog v, const_on_circle hζ hroot rot hcont _ (norm_div_norm hv), mul_comm]

/-- **The round-norm theorem (bounded form).**  Continuity may be replaced by an upper bound on
the unit circle; subadditivity then supplies continuity through the Lipschitz lemma. -/
theorem round_of_bounded {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hroot : ∀ n : ℕ, 0 < n → ζ ^ n ≠ 1)
    (subadd : ∀ v w, s (v + w) ≤ s v + s w)
    (homog : ∀ t : ℝ, 0 ≤ t → ∀ v, s ((t : ℂ) * v) = t * s v)
    (rot : ∀ v, s (ζ * v) = s v)
    (M : ℝ) (hM : ∀ u : ℂ, ‖u‖ = 1 → s u ≤ M) (v : ℂ) :
    s v = s 1 * ‖v‖ :=
  round_of_continuous hζ hroot homog rot (continuous_of_bounded subadd homog M hM) v

/-- The constant is non-negative: `0 = s 0 ≤ s 1 + s (-1) = 2 s 1`. -/
theorem round_nonneg {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hroot : ∀ n : ℕ, 0 < n → ζ ^ n ≠ 1)
    (subadd : ∀ v w, s (v + w) ≤ s v + s w)
    (homog : ∀ t : ℝ, 0 ≤ t → ∀ v, s ((t : ℂ) * v) = t * s v)
    (rot : ∀ v, s (ζ * v) = s v) (hcont : Continuous s) : 0 ≤ s 1 := by
  have h := subadd 1 (-1)
  rw [add_neg_cancel, map_zero homog, round_of_continuous hζ hroot homog rot hcont (-1)] at h
  simp at h
  linarith

end Main

section NonVacuity

/-- The hypotheses on `ζ` are satisfiable: `ζ = e^{i}` has modulus one and is not a root of
unity (because `π` is irrational). -/
theorem exists_zeta : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ n : ℕ, 0 < n → ζ ^ n ≠ 1 := by
  refine ⟨(Circle.exp 1 : ℂ), Circle.norm_coe _, fun n hn h => ?_⟩
  have h1 : Circle.exp (n : ℝ) = 1 := by
    apply Subtype.ext
    rw [← Circle.coe_pow, ← Circle.exp_natCast_mul, mul_one] at h
    simpa using h
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp h1
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hm; exact (Nat.cast_pos.mpr hn).ne' hm
  apply irrational_pi
  refine ⟨(n : ℚ) / (2 * m), ?_⟩
  push_cast
  field_simp
  linarith

/-- And the whole hypothesis set is satisfiable, by `s = ‖·‖` (with `s 1 = 1`). -/
theorem norm_satisfies (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (∀ v w : ℂ, ‖v + w‖ ≤ ‖v‖ + ‖w‖) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ v : ℂ, ‖(t : ℂ) * v‖ = t * ‖v‖) ∧
    (∀ v : ℂ, ‖ζ * v‖ = ‖v‖) ∧ Continuous (fun v : ℂ => ‖v‖) := by
  refine ⟨norm_add_le, fun t ht v => ?_, fun v => ?_, continuous_norm⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  · rw [norm_mul, hζ, one_mul]

end NonVacuity

end RoundNorm

#print axioms RoundNorm.map_zero
#print axioms RoundNorm.polar
#print axioms RoundNorm.norm_div_norm
#print axioms RoundNorm.lipschitz_of_bounded
#print axioms RoundNorm.continuous_of_bounded
#print axioms RoundNorm.rot_zpow
#print axioms RoundNorm.denseRange_zpow
#print axioms RoundNorm.const_on_circle
#print axioms RoundNorm.round_of_continuous
#print axioms RoundNorm.round_of_bounded
#print axioms RoundNorm.round_nonneg
#print axioms RoundNorm.exists_zeta
#print axioms RoundNorm.norm_satisfies
