/-
  ReflectionTriple.lean
  =====================
  Paper "Universality for orthoscheme reflection groups", Theorem `thm:len6`, step (2).

  The step formalised here is the linear-algebra heart of the exclusion of length-six kernel
  elements outside the rank-two standard parabolics.  There one arrives at a word
  `(R_p R_q R_r)^2` in the kernel, hence at three reflections whose product is `-id` on the
  span of their normals, and one has to conclude that the three normals are pairwise
  orthogonal, which in the orthoscheme forces the three indices to be pairwise non-adjacent
  and hence the word to be trivial already in the envelope.

  Statement proved here, over an arbitrary real inner product space and with no dimension
  hypothesis: if `u, v, w` are nonzero, `v` and `w` are linearly independent, and the composite
  of the three reflections is `-id`, then `u`, `v`, `w` are pairwise orthogonal.

  The reflection is defined by hand,

      refl x y = y - (2 * <y, x> / <x, x>) . x,

  so nothing is imported beyond the inner product space itself; `refl x` is additive, commutes
  with scalars, is an involution for `x` nonzero, negates `x` and fixes `x`-orthogonal vectors.

  What is NOT formalised here: the rest of `thm:len6`, namely the word combinatorics in the
  right-angled Coxeter group, Carter's rank lemma, and the affine argument in dimension three.
  Those are paper proofs.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ReflectionTriple

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The reflection of `y` in the hyperplane orthogonal to a nonzero vector `x`. -/
noncomputable def refl (x y : E) : E := y - (2 * ⟪y, x⟫ / ⟪x, x⟫) • x

/-- For `x ≠ 0` the normalising denominator is nonzero. -/
theorem inner_self_ne_zero' {x : E} (hx : x ≠ 0) : ⟪x, x⟫ ≠ (0 : ℝ) := by
  rw [real_inner_self_eq_norm_sq]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)

omit [InnerProductSpace ℝ E] in
/-- Cancellation on the right of a difference, used twice below. -/
theorem eq_of_sub_eq_sub {a x y : E} (h : a - x = a - y) : x = y := by
  have h2 : a - (a - x) = a - (a - y) := by rw [h]
  simpa using h2

omit [InnerProductSpace ℝ E] in
/-- If subtracting `b` from `a` changes nothing, `b` is zero. -/
theorem eq_zero_of_sub_eq_self {a b : E} (h : a - b = a) : b = 0 := by
  have h2 : a - b - a = a - a := by rw [h]
  simpa using h2

/-- A reflection negates its own normal. -/
theorem refl_self {x : E} (hx : x ≠ 0) : refl x x = -x := by
  have h : ⟪x, x⟫ ≠ (0 : ℝ) := inner_self_ne_zero' hx
  unfold refl
  rw [mul_div_assoc, div_self h, mul_one, two_smul]
  abel

/-- A reflection fixes every vector orthogonal to its normal. -/
theorem refl_of_inner_eq_zero {x y : E} (h : ⟪y, x⟫ = (0 : ℝ)) : refl x y = y := by
  unfold refl
  rw [h]
  simp

/-- `refl x` is additive. -/
theorem refl_add (x y z : E) : refl x (y + z) = refl x y + refl x z := by
  unfold refl
  rw [inner_add_left]
  rw [show 2 * (⟪y, x⟫ + ⟪z, x⟫) / ⟪x, x⟫
      = 2 * ⟪y, x⟫ / ⟪x, x⟫ + 2 * ⟪z, x⟫ / ⟪x, x⟫ by ring]
  rw [add_smul]
  abel

/-- `refl x` commutes with scalars. -/
theorem refl_smul (x y : E) (r : ℝ) : refl x (r • y) = r • refl x y := by
  unfold refl
  rw [real_inner_smul_left, smul_sub, smul_smul]
  congr 2
  ring

theorem refl_neg (x y : E) : refl x (-y) = -refl x y := by
  have h := refl_smul x y (-1 : ℝ)
  simpa using h

theorem refl_sub (x y z : E) : refl x (y - z) = refl x y - refl x z := by
  rw [sub_eq_add_neg, refl_add, refl_neg, sub_eq_add_neg]

/-- The inner product of a reflected vector with the normal is negated. -/
theorem inner_refl_left {x y : E} (hx : x ≠ 0) : ⟪refl x y, x⟫ = -⟪y, x⟫ := by
  have h : ⟪x, x⟫ ≠ (0 : ℝ) := inner_self_ne_zero' hx
  show ⟪y - (2 * ⟪y, x⟫ / ⟪x, x⟫) • x, x⟫ = -⟪y, x⟫
  rw [inner_sub_left, real_inner_smul_left]
  field_simp
  ring

/-- A reflection is an involution. -/
theorem refl_involutive {x : E} (hx : x ≠ 0) (y : E) : refl x (refl x y) = y := by
  have e1 : refl x (refl x y) = refl x y - (2 * ⟪refl x y, x⟫ / ⟪x, x⟫) • x := rfl
  rw [e1, inner_refl_left hx]
  show y - (2 * ⟪y, x⟫ / ⟪x, x⟫) • x - (2 * -⟪y, x⟫ / ⟪x, x⟫) • x = y
  rw [show (2 : ℝ) * -⟪y, x⟫ / ⟪x, x⟫ = -(2 * ⟪y, x⟫ / ⟪x, x⟫) by ring, neg_smul]
  abel

/-- A reflection is injective. -/
theorem refl_injective {x : E} (hx : x ≠ 0) : Function.Injective (refl x) := by
  intro y z hyz
  have h := congrArg (refl x) hyz
  rwa [refl_involutive hx, refl_involutive hx] at h

/--
**The triple-reflection rigidity lemma.**  If the product of the reflections in three nonzero
vectors `u`, `v`, `w` is `-id`, and `v`, `w` are linearly independent, then the three vectors
are pairwise orthogonal.

This is step (2) of Theorem `thm:len6`: in the orthoscheme the conclusion contradicts the
adjacency of two of the three indices, which is what kills the word `(R_p R_q R_r)^2`.
-/
theorem pairwise_orth_of_comp_eq_neg
    {u v w : E} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : ∀ a b : ℝ, a • v + b • w = 0 → a = 0 ∧ b = 0)
    (h : ∀ x : E, refl u (refl v (refl w x)) = -x) :
    ⟪u, v⟫ = (0 : ℝ) ∧ ⟪u, w⟫ = (0 : ℝ) ∧ ⟪v, w⟫ = (0 : ℝ) := by
  have hvv : ⟪v, v⟫ ≠ (0 : ℝ) := inner_self_ne_zero' hv
  have hww : ⟪w, w⟫ ≠ (0 : ℝ) := inner_self_ne_zero' hw
  -- Peel off the outer reflection: `refl v ∘ refl w = - refl u`.
  have key : ∀ x : E, refl v (refl w x) = -refl u x := by
    intro x
    have h2 := congrArg (refl u) (h x)
    rwa [refl_involutive hu, refl_neg] at h2
  -- At `x = u` this says `refl v (refl w u) = u`.
  have step1 : refl v (refl w u) = u := by
    have h3 := key u
    rwa [refl_self hu, neg_neg] at h3
  -- Hence `refl w u = refl v u`.
  have step2 : refl w u = refl v u := by
    have h3 := congrArg (refl v) step1
    rwa [refl_involutive hv] at h3
  -- Read off the coefficients: the two reflections move `u` along `w` and along `v`.
  have step3 : (2 * ⟪u, w⟫ / ⟪w, w⟫) • w = (2 * ⟪u, v⟫ / ⟪v, v⟫) • v :=
    eq_of_sub_eq_sub (a := u) step2
  have step4 : (2 * ⟪u, v⟫ / ⟪v, v⟫) • v + (-(2 * ⟪u, w⟫ / ⟪w, w⟫)) • w = 0 := by
    rw [neg_smul, ← step3]
    abel
  obtain ⟨hA, hB⟩ := hvw _ _ step4
  have huv : ⟪u, v⟫ = (0 : ℝ) := by
    field_simp at hA
    linarith
  have huw : ⟪u, w⟫ = (0 : ℝ) := by
    have hB' := neg_eq_zero.mp hB
    field_simp at hB'
    linarith
  -- Second half: with `u ⊥ v`, the identity at `x = v` forces `v ⊥ w`.
  have hvu : ⟪v, u⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact huv
  have step5 : refl v (refl w v) = -v := by
    have h3 := key v
    rwa [refl_of_inner_eq_zero hvu] at h3
  have hexp : refl w v = v - (2 * ⟪v, w⟫ / ⟪w, w⟫) • w := rfl
  rw [hexp, refl_sub, refl_smul, refl_self hv] at step5
  have step6 : (2 * ⟪v, w⟫ / ⟪w, w⟫) • refl v w = 0 :=
    eq_zero_of_sub_eq_self (a := -v) step5
  have hrvw : refl v w ≠ 0 := by
    intro hzero
    have h4 : refl v (refl v w) = refl v 0 := by rw [hzero]
    rw [refl_involutive hv] at h4
    exact hw (by simpa [refl] using h4)
  have hc : 2 * ⟪v, w⟫ / ⟪w, w⟫ = 0 := by
    rcases smul_eq_zero.mp step6 with hc | hc
    · exact hc
    · exact absurd hc hrvw
  have hvwzero : ⟪v, w⟫ = (0 : ℝ) := by
    field_simp at hc
    linarith
  exact ⟨huv, huw, hvwzero⟩

end ReflectionTriple

-- Rule 5 axiom audit.
#print axioms ReflectionTriple.inner_self_ne_zero'
#print axioms ReflectionTriple.eq_of_sub_eq_sub
#print axioms ReflectionTriple.eq_zero_of_sub_eq_self
#print axioms ReflectionTriple.refl_self
#print axioms ReflectionTriple.refl_of_inner_eq_zero
#print axioms ReflectionTriple.refl_add
#print axioms ReflectionTriple.refl_smul
#print axioms ReflectionTriple.refl_neg
#print axioms ReflectionTriple.refl_sub
#print axioms ReflectionTriple.refl_involutive
#print axioms ReflectionTriple.refl_injective
#print axioms ReflectionTriple.inner_refl_left
#print axioms ReflectionTriple.pairwise_orth_of_comp_eq_neg
