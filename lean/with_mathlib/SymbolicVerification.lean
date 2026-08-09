/-
  SymbolicVerification.lean
  =========================

  Machine-checked symbolic verification of Relation #1 of the side-
  reflection group of an arbitrary right triangle with positive legs,
  in the field of rational functions Q(a,b).

  Strategy: instead of working with RatFunc, we encode each affine
  isometry as a 6-tuple of polynomials plus a single common-denominator
  polynomial.  The composition rule keeps the denominator a power of
  D := a^2 + b^2.  We prove relation #1 by showing the corresponding
  6-tuples of numerators are equal as polynomials in Q[a,b], modulo
  a common power of D — which is a finite-degree polynomial identity
  that `ring` can dispatch.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open MvPolynomial

abbrev R : Type := MvPolynomial (Fin 2) ℚ

noncomputable def a : R := X 0
noncomputable def b : R := X 1

/-- D = a^2 + b^2, the common denominator factor for R_2. -/
noncomputable def D : R := a * a + b * b

/-- An affine isometry over the rational-function field, encoded as
    six numerator polynomials (entries `(p, q, r, s, tx, ty)`) and a
    common denominator polynomial `d`.

    Semantics: this represents the affine map p ↦ ⎡p/d  q/d⎤ p + ⎡tx/d⎤. -/
structure Aff where
  p : R
  q : R
  r : R
  s : R
  tx : R
  ty : R
  d : R

namespace Aff

/-- Identity. -/
noncomputable def one : Aff :=
  { p := 1, q := 0, r := 0, s := 1, tx := 0, ty := 0, d := 1 }

/-- Composition: `(comp M N)` represents `M ∘ N`.  Both numerator and
    denominator are scaled. -/
noncomputable def comp (M N : Aff) : Aff :=
  { p  := M.p * N.p + M.q * N.r
    q  := M.p * N.q + M.q * N.s
    r  := M.r * N.p + M.s * N.r
    s  := M.r * N.q + M.s * N.s
    tx := M.p * N.tx + M.q * N.ty + M.tx * N.d
    ty := M.r * N.tx + M.s * N.ty + M.ty * N.d
    d  := M.d * N.d }

/-- Two affine isometries `M` and `N` represent the same map iff their
    cross-product numerators are equal as polynomials. -/
def equiv (M N : Aff) : Prop :=
  M.p * N.d = N.p * M.d ∧
  M.q * N.d = N.q * M.d ∧
  M.r * N.d = N.r * M.d ∧
  M.s * N.d = N.s * M.d ∧
  M.tx * N.d = N.tx * M.d ∧
  M.ty * N.d = N.ty * M.d

end Aff

/-! ## The three reflections on the (a, b) right triangle. -/

noncomputable def R0 : Aff :=
  { p := 1, q := 0, r := 0, s := -1, tx := 0, ty := 0, d := 1 }

noncomputable def R1 : Aff :=
  { p := -1, q := 0, r := 0, s := 1, tx := 2 * a, ty := 0, d := 1 }

noncomputable def R2 : Aff :=
  { p := a * a - b * b, q := 2 * a * b
    r := 2 * a * b, s := b * b - a * a
    tx := 0, ty := 0, d := D }

noncomputable def applyWord : List Nat → Aff
  | []      => Aff.one
  | i :: is =>
      let g := match i with
        | 0 => R0
        | 1 => R1
        | _ => R2
      Aff.comp g (applyWord is)

/-! ## Relation #1 holds symbolically. -/

set_option maxHeartbeats 4000000 in
/-- Relation #1: holds for every right triangle. -/
theorem rel1_symbolic :
    Aff.equiv
      (applyWord [0, 1, 2, 0, 2, 0, 1, 2, 1, 2])
      (applyWord [2, 1, 2, 0, 1, 2, 0, 2, 0, 1]) := by
  unfold Aff.equiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [applyWord, Aff.comp, Aff.one, R0, R1, R2, D, a, b]
    ring

set_option maxHeartbeats 4000000 in
/-- Relation #2: holds for every right triangle. -/
theorem rel2_symbolic :
    Aff.equiv
      (applyWord [0, 1, 2, 1, 2, 0, 1, 2, 0, 2])
      (applyWord [2, 0, 2, 0, 1, 2, 1, 2, 0, 1]) := by
  unfold Aff.equiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [applyWord, Aff.comp, Aff.one, R0, R1, R2, D, a, b]
    ring

set_option maxHeartbeats 4000000 in
/-- Relation #3: holds for every right triangle. -/
theorem rel3_symbolic :
    Aff.equiv
      (applyWord [0, 2, 0, 1, 2, 1, 2, 0, 1, 2])
      (applyWord [2, 0, 1, 2, 1, 2, 0, 1, 2, 0]) := by
  unfold Aff.equiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [applyWord, Aff.comp, Aff.one, R0, R1, R2, D, a, b]
    ring

set_option maxHeartbeats 4000000 in
/-- Relation #4: holds for every right triangle. -/
theorem rel4_symbolic :
    Aff.equiv
      (applyWord [0, 2, 0, 2, 0, 1, 2, 1, 2, 0])
      (applyWord [1, 2, 1, 2, 0, 1, 2, 0, 2, 1]) := by
  unfold Aff.equiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [applyWord, Aff.comp, Aff.one, R0, R1, R2, D, a, b]
    ring

set_option maxHeartbeats 4000000 in
/-- Relation #5: holds for every right triangle. -/
theorem rel5_symbolic :
    Aff.equiv
      (applyWord [0, 2, 0, 2, 0, 1, 2, 1, 2, 1])
      (applyWord [1, 2, 1, 2, 0, 1, 2, 0, 2, 0]) := by
  unfold Aff.equiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [applyWord, Aff.comp, Aff.one, R0, R1, R2, D, a, b]
    ring

set_option maxHeartbeats 4000000 in
/-- Relation #6: holds for every right triangle. -/
theorem rel6_symbolic :
    Aff.equiv
      (applyWord [0, 2, 1, 2, 0, 1, 2, 0, 2, 0])
      (applyWord [1, 2, 0, 2, 0, 1, 2, 1, 2, 1]) := by
  unfold Aff.equiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [applyWord, Aff.comp, Aff.one, R0, R1, R2, D, a, b]
    ring

set_option maxHeartbeats 4000000 in
/-- Relation #7: holds for every right triangle. -/
theorem rel7_symbolic :
    Aff.equiv
      (applyWord [0, 2, 1, 2, 0, 1, 2, 0, 2, 1])
      (applyWord [1, 2, 0, 2, 0, 1, 2, 1, 2, 0]) := by
  unfold Aff.equiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [applyWord, Aff.comp, Aff.one, R0, R1, R2, D, a, b]
    ring

set_option maxHeartbeats 4000000 in
/-- Relation #8: holds for every right triangle. -/
theorem rel8_symbolic :
    Aff.equiv
      (applyWord [1, 2, 0, 1, 2, 0, 2, 0, 1, 2])
      (applyWord [2, 0, 1, 2, 0, 2, 0, 1, 2, 1]) := by
  unfold Aff.equiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [applyWord, Aff.comp, Aff.one, R0, R1, R2, D, a, b]
    ring
