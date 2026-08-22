/-
The plane, its isometries, and the reflections generating a triangle group.

An affine map of the plane that preserves or reverses orientation is
`z ↦ a z + b` or `z ↦ a conj z + b`, and these form a group under composition
for any `a ≠ 0`; the isometries are the ones with `‖a‖ = 1`. Carrying `a` as a
unit of `ℂ` makes the group laws free of side conditions.

`refl θ p` is the reflection in the line through `p` of direction `θ`. Its
linear coefficient is `exp (2iθ)`, so by `linOf_eq` the linear coefficient of a
product of reflections is `exp (2i Σ_i c_i(w) θ_i)`: `linCoeff_prod` is the
statement that the abstract invariant of `LinearPart.lean` really is the linear
part of the plane map. That is part (i) of the rotation-relations theorem,
now about actual isometries.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import RotationRelations
import LinearPart

namespace PlaneGroup

open Complex RotationRelations LinearPart

/-- Conjugation, switched by a boolean, as a ring homomorphism. -/
def cj (s : Bool) : ℂ →+* ℂ := if s then starRingEnd ℂ else RingHom.id ℂ

@[simp] theorem cj_false : cj false = RingHom.id ℂ := rfl
@[simp] theorem cj_true : cj true = starRingEnd ℂ := rfl

theorem cj_cj (s r : Bool) (z : ℂ) : cj s (cj r z) = cj (xor s r) z := by
  cases s <;> cases r <;> simp [cj]

theorem cj_ofReal (s : Bool) (x : ℝ) : cj s (x : ℂ) = (x : ℂ) := by
  cases s <;> simp [cj]

/-- Conjugation on the units. -/
def cjU (s : Bool) : ℂˣ →* ℂˣ := Units.map (cj s).toMonoidHom

@[simp] theorem cjU_val (s : Bool) (a : ℂˣ) : ((cjU s a : ℂˣ) : ℂ) = cj s (a : ℂ) := rfl

/-- An orientation-preserving or reversing affine map of the plane. -/
structure Aff where
  a : ℂˣ
  b : ℂ
  flip : Bool

namespace Aff

@[ext] theorem ext : ∀ {f g : Aff}, f.a = g.a → f.b = g.b → f.flip = g.flip → f = g
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl, rfl => rfl

/-- The map itself. -/
def act (f : Aff) (z : ℂ) : ℂ := (f.a : ℂ) * cj f.flip z + f.b

instance : One Aff := ⟨⟨1, 0, false⟩⟩
instance : Mul Aff :=
  ⟨fun f g => ⟨f.a * cjU f.flip g.a, (f.a : ℂ) * cj f.flip g.b + f.b, xor f.flip g.flip⟩⟩
instance : Inv Aff :=
  ⟨fun f => ⟨cjU f.flip f.a⁻¹, -(cj f.flip ((f.a⁻¹ : ℂˣ) : ℂ) * cj f.flip f.b), f.flip⟩⟩

@[simp] theorem one_a : (1 : Aff).a = 1 := rfl
@[simp] theorem one_b : (1 : Aff).b = 0 := rfl
@[simp] theorem one_flip : (1 : Aff).flip = false := rfl
@[simp] theorem mul_a (f g : Aff) : (f * g).a = f.a * cjU f.flip g.a := rfl
@[simp] theorem mul_b (f g : Aff) :
    (f * g).b = (f.a : ℂ) * cj f.flip g.b + f.b := rfl
@[simp] theorem mul_flip (f g : Aff) : (f * g).flip = xor f.flip g.flip := rfl
@[simp] theorem inv_a (f : Aff) : f⁻¹.a = cjU f.flip f.a⁻¹ := rfl
@[simp] theorem inv_b (f : Aff) :
    f⁻¹.b = -(cj f.flip ((f.a⁻¹ : ℂˣ) : ℂ) * cj f.flip f.b) := rfl
@[simp] theorem inv_flip (f : Aff) : f⁻¹.flip = f.flip := rfl

/-- Multiplication is composition of the maps. -/
theorem act_mul (f g : Aff) (z : ℂ) : (f * g).act z = f.act (g.act z) := by
  simp only [act, mul_a, mul_b, mul_flip, Units.val_mul, cjU_val, map_add, map_mul]
  rw [← cj_cj]
  ring

/-- The maps determine the data: `b` is the image of `0`, `a` the increment
from `0` to `1`, and the orientation is read off the image of `i`. -/
theorem act_injective : Function.Injective Aff.act := by
  intro f g h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have hI := congrFun h Complex.I
  simp only [Aff.act, map_zero, map_one, mul_zero, mul_one, zero_add] at h0 h1 hI
  have hb : f.b = g.b := h0
  have ha : (f.a : ℂ) = (g.a : ℂ) := by
    rw [hb] at h1
    exact add_right_cancel h1
  have hflip : f.flip = g.flip := by
    by_contra hne
    rw [hb, ha] at hI
    have h2 := add_right_cancel hI
    have h3 := mul_left_cancel₀ (Units.ne_zero g.a) h2
    cases hf : f.flip <;> cases hg : g.flip
    · exact hne (by rw [hf, hg])
    · rw [hf, hg] at h3
      simp only [cj_false, cj_true, RingHom.id_apply, Complex.conj_I] at h3
      exact Complex.I_ne_zero (by linear_combination h3 / 2)
    · rw [hf, hg] at h3
      simp only [cj_false, cj_true, RingHom.id_apply, Complex.conj_I] at h3
      exact Complex.I_ne_zero (by linear_combination -h3 / 2)
    · exact hne (by rw [hf, hg])
  exact Aff.ext (Units.ext ha) hb hflip

instance : Group Aff where
  mul_assoc f g h := act_injective (by funext z; rw [act_mul, act_mul, act_mul, act_mul])
  one_mul f := act_injective (by funext z; rw [act_mul]; simp [Aff.act, cj])
  mul_one f := act_injective (by funext z; rw [act_mul]; simp [Aff.act, cj])
  inv_mul_cancel f := by
    refine act_injective ?_
    funext z
    rw [act_mul]
    have hz : cj f.flip (cj f.flip z) = z := by
      rw [cj_cj]
      cases f.flip <;> simp [cj]
    have hinv : cj f.flip ((f.a⁻¹ : ℂˣ) : ℂ) * cj f.flip ((f.a : ℂˣ) : ℂ) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    simp only [Aff.act, inv_a, inv_b, inv_flip, cjU_val, one_a, one_flip,
      one_b, Units.val_one, cj_false, RingHom.id_apply, one_mul, add_zero,
      map_add, map_mul, hz]
    linear_combination z * hinv

end Aff

/-- The reflection in the line through `p` of direction `θ`. -/
noncomputable def refl (θ : ℝ) (p : ℂ) : Aff :=
  ⟨Units.mk0 (Complex.exp (2 * Complex.I * (θ : ℂ))) (Complex.exp_ne_zero _),
    p - Complex.exp (2 * Complex.I * (θ : ℂ)) * (starRingEnd ℂ) p, true⟩

@[simp] theorem refl_a (θ : ℝ) (p : ℂ) :
    ((refl θ p).a : ℂ) = Complex.exp (2 * Complex.I * (θ : ℂ)) := rfl

@[simp] theorem refl_flip (θ : ℝ) (p : ℂ) : (refl θ p).flip = true := rfl

/-- A reflection fixes every point of its line. -/
theorem refl_fixes (θ : ℝ) (p : ℂ) : (refl θ p).act p = p := by
  simp [Aff.act, refl, cj]

/-- `exp (2iθ)` has modulus one, for real `θ`. -/
theorem exp_mul_conj (θ : ℝ) :
    Complex.exp (2 * Complex.I * (θ : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (2 * Complex.I * (θ : ℂ))) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- A reflection is an involution. -/
theorem refl_sq (θ : ℝ) (p : ℂ) : refl θ p * refl θ p = 1 := by
  refine Aff.act_injective ?_
  funext z
  rw [Aff.act_mul]
  have hu := exp_mul_conj θ
  simp only [Aff.act, refl, cj_true, Aff.one_a, Aff.one_flip, Aff.one_b,
    Units.val_one, cj_false, RingHom.id_apply, one_mul, add_zero, Units.val_mk0,
    map_add, map_sub, map_mul, Complex.conj_conj]
  linear_combination (z - p) * hu

/-- The product of the reflections named by a word, each in the line of its own
direction through the origin. -/
noncomputable def prodRefl (θ : Letter → ℝ) (p : Letter → ℂ) : List Letter → Aff
  | [] => 1
  | l :: w => refl (θ l) (p l) * prodRefl θ p w

/-- **The linear part.** The linear coefficient of a product of reflections is
the invariant computed in `LinearPart.lean`, so by `linOf_eq` it is
`exp (2i Σ_i c_i(w) θ_i)`. -/
theorem linCoeff_prod (θ : Letter → ℝ) (p : Letter → ℂ) (w : List Letter) :
    ((prodRefl θ p w).a : ℂ) = linOf θ w := by
  induction w with
  | nil => simp [prodRefl, linOf]
  | cons l w ih =>
      simp only [prodRefl, Aff.mul_a, refl_flip, cjU_val, refl_a, cj_true,
        Units.val_mul, linOf]
      rw [ih]

/-- Hence, on the stratum of angle `π/m` with `θ₀ = 0` and `θ₁ = π/m`, a word
whose second invariant vanishes has linear part the rotation by `2πc₁/m`,
whatever the shape. -/
theorem linCoeff_of_cvec_two_eq_zero (m : ℕ) (θ : Letter → ℝ) (p : Letter → ℂ)
    (w : List Letter) (h0 : θ 0 = 0) (h1 : θ 1 = Real.pi / m) (h2 : cvec w 2 = 0) :
    ((prodRefl θ p w).a : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * (cvec w 1 : ℂ) / m) := by
  rw [linCoeff_prod, linOf_of_cvec_two_eq_zero m θ w h0 h1 h2]

/-- A word of even length composes to an orientation-preserving map, and one of
odd length to an orientation-reversing one. -/
theorem prodRefl_flip (θ : Letter → ℝ) (p : Letter → ℂ) (w : List Letter) :
    (prodRefl θ p w).flip = decide (Odd w.length) := by
  induction w with
  | nil => simp [prodRefl]
  | cons l w ih =>
      simp only [prodRefl, Aff.mul_flip, refl_flip, ih, List.length_cons]
      rcases Nat.even_or_odd w.length with h | h
      · simp [h, Nat.not_odd_iff_even.mpr h]
      · simp [Nat.odd_add_one, h]

end PlaneGroup

-- Rule 5 axiom audit (added 2026-08-01): declare every axiom these results rest on.
#print axioms PlaneGroup.cj_false
#print axioms PlaneGroup.cj_true
#print axioms PlaneGroup.cj_cj
#print axioms PlaneGroup.cj_ofReal
#print axioms PlaneGroup.cjU_val
#print axioms PlaneGroup.Aff.ext
#print axioms PlaneGroup.Aff.one_a
#print axioms PlaneGroup.Aff.one_b
#print axioms PlaneGroup.Aff.one_flip
#print axioms PlaneGroup.Aff.mul_a
#print axioms PlaneGroup.Aff.mul_b
#print axioms PlaneGroup.Aff.mul_flip
#print axioms PlaneGroup.Aff.inv_a
#print axioms PlaneGroup.Aff.inv_b
#print axioms PlaneGroup.Aff.inv_flip
#print axioms PlaneGroup.Aff.act_mul
#print axioms PlaneGroup.Aff.act_injective
#print axioms PlaneGroup.refl_a
#print axioms PlaneGroup.refl_flip
#print axioms PlaneGroup.refl_fixes
#print axioms PlaneGroup.exp_mul_conj
#print axioms PlaneGroup.refl_sq
#print axioms PlaneGroup.linCoeff_prod
#print axioms PlaneGroup.linCoeff_of_cvec_two_eq_zero
#print axioms PlaneGroup.prodRefl_flip
