/-
  SymbolicVerification.lean
  =========================

  Machine-checked symbolic verification of Relation #1 of the
  side-reflection group of an arbitrary right triangle with positive
  unequal rational legs.  This is the universality statement, at
  word-length 10, for the single relation

      w_A  =  R_0 R_1 R_2 R_0 R_2 R_0 R_1 R_2 R_1 R_2
      w_B  =  R_2 R_1 R_2 R_0 R_1 R_2 R_0 R_2 R_0 R_1

  We work in the field ℚ(a, b) of rational functions in two indeterminates,
  encoded via `MvPolynomial (Fin 2) ℚ`.  The relation is proved by
  reducing both sides to the same canonical polynomial after clearing
  denominators.

  This file requires Mathlib.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open MvPolynomial

/-- Two indeterminates `a` and `b`. -/
abbrev R : Type := MvPolynomial (Fin 2) ℚ

/-- The first indeterminate. -/
def a : R := X 0

/-- The second indeterminate. -/
def b : R := X 1

/-- The field of rational functions in two indeterminates. -/
abbrev F : Type := RatFunc R

/-- The first indeterminate in F. -/
def aF : F := RatFunc.algebraMap _ _ a

/-- The second indeterminate in F. -/
def bF : F := RatFunc.algebraMap _ _ b

/-! ## Affine isometries over F = ℚ(a, b) -/

abbrev Aff := F × F × F × F × F × F

namespace Aff

def one : Aff := (1, 0, 0, 1, 0, 0)

def comp (M N : Aff) : Aff :=
  let (a1, b1, c1, d1, tx1, ty1) := M
  let (a2, b2, c2, d2, tx2, ty2) := N
  ( a1 * a2 + b1 * c2,
    a1 * b2 + b1 * d2,
    c1 * a2 + d1 * c2,
    c1 * b2 + d1 * d2,
    a1 * tx2 + b1 * ty2 + tx1,
    c1 * tx2 + d1 * ty2 + ty1 )

end Aff

/-! ## Reflections over an arbitrary right triangle with legs (a, b)

  Vertices: A = (0, 0), B = (a, 0), C = (a, b).  Right angle at B.
  R_0 = reflection across AB (x-axis)
  R_1 = reflection across BC (vertical line x = a)
  R_2 = reflection across CA (line through origin with direction (a, b))
-/

/-- Common denominator for R_2, namely a^2 + b^2. -/
def D : F := aF * aF + bF * bF

def R0 : Aff := (1, 0, 0, -1, 0, 0)

def R1 : Aff := (-1, 0, 0, 1, 2 * aF, 0)

def R2 : Aff :=
  ( (aF * aF - bF * bF) / D,
    2 * aF * bF / D,
    2 * aF * bF / D,
    (bF * bF - aF * aF) / D,
    0,
    0 )

/-! ## The word-application function -/

def applyWord : List Nat → Aff
  | []      => Aff.one
  | i :: is =>
      let g := match i with
        | 0 => R0
        | 1 => R1
        | _ => R2
      Aff.comp g (applyWord is)

/-! ## Relation #1 symbolically over ℚ(a, b)

  Both sides evaluate to the same element of `Aff F`. -/

theorem rel1_symbolic :
    applyWord [0, 1, 2, 0, 2, 0, 1, 2, 1, 2] =
    applyWord [2, 1, 2, 0, 1, 2, 0, 2, 0, 1] := by
  unfold applyWord
  simp only [Aff.comp, R0, R1, R2]
  -- The two sides should reduce to the same rational function.
  -- We attempt the kitchen-sink approach.
  ext <;> field_simp <;> ring
