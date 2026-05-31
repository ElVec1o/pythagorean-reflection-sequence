/-
  RightTriangleReflection.lean
  ============================

  Machine-checkable verification of the eight length-10 affine relations
  that drive OEIS A396406 (the universal right-triangle reflection sequence).

  These relations explain the first deviation from Fibonacci at depth 10:
    a(10) = F(13) - 8 = 233 - 8 = 225.

  This file works in core Lean 4 (no Mathlib dependency).  All proofs are
  done by `decide` or `native_decide` over exact rational arithmetic on
  the canonical (3, 4, 5) right triangle with vertices
    A = (0, 0),  B = (3, 0),  C = (3, 4)
  and the labeling
    R_0 = reflection across side AB,
    R_1 = reflection across side BC,
    R_2 = reflection across side CA.

  Reference: Bonfioli, V., "The Universal Right-Triangle Reflection
  Sequence (Unequal Legs)" (2026), Theorem 1 / Table 1.
  https://github.com/ElVec1o/pythagorean-reflection-sequence
-/

import Lean.Data.Rat
open Lean

/-! ## Affine isometries of the plane

An affine isometry of `ℝ²` (here taken over `ℚ` since all our data is
rational) is encoded as a 6-tuple `(a, b, c, d, tx, ty)` representing
the map  p ↦ ⎡a b⎤ p + ⎡tx⎤.
                 ⎣c d⎦     ⎣ty⎦  -/

abbrev Aff := Rat × Rat × Rat × Rat × Rat × Rat

namespace Aff

/-- Identity affine isometry. -/
def one : Aff := (1, 0, 0, 1, 0, 0)

/-- Composition: `(comp M N) p = M (N p)`. -/
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

/-! ## The (3, 4, 5) right triangle and its three side-reflections -/

namespace RightTriangle345

/-- Reflection R_0 across side AB (the x-axis): (x, y) ↦ (x, -y). -/
def R0 : Aff := (1, 0, 0, -1, 0, 0)

/-- Reflection R_1 across side BC (the vertical line x = 3): (x, y) ↦ (6 - x, y). -/
def R1 : Aff := (-1, 0, 0, 1, 6, 0)

/-- Reflection R_2 across side CA (line through origin with direction (3, 4)). -/
def R2 : Aff := (-7/25, 24/25, 24/25, 7/25, 0, 0)

/-- Apply a word (list of generator indices) by repeated composition.
    `applyWord [i₀, i₁, …, iₙ]` evaluates as
    `R_{i₀} ∘ R_{i₁} ∘ ⋯ ∘ R_{iₙ}` (composition order, leftmost-first).  -/
def applyWord : List Nat → Aff
  | []      => Aff.one
  | i :: is =>
      let g := match i with
        | 0 => R0
        | 1 => R1
        | _ => R2
      Aff.comp g (applyWord is)

end RightTriangle345

/-! ## Sanity check: identity action on the basic Coxeter relations

  R_i² = 1  and  (R_0 R_1)² = 1  (the perpendicular legs). -/

namespace BasicCoxeter

open RightTriangle345

example : applyWord [0, 0] = Aff.one := by native_decide
example : applyWord [1, 1] = Aff.one := by native_decide
example : applyWord [2, 2] = Aff.one := by native_decide
example : applyWord [0, 1, 0, 1] = Aff.one := by native_decide

end BasicCoxeter

/-! ## The eight length-10 affine relations

  Each line below is one row of Table 1 of the manuscript.  Each relation
  says that two distinct length-10 words in the free Coxeter group
  ⟨R_0, R_1, R_2 | R_i² = 1, (R_0 R_1)² = 1⟩ both reduced with respect to
  these basic relations evaluate to the same element of `Aff(ℚ²)`. -/

namespace LengthTenRelations

open RightTriangle345

/-- Relation #1.  Both sides equal the half-turn about (2931/625, 2808/625). -/
theorem rel1 :
    applyWord [0, 1, 2, 0, 2, 0, 1, 2, 1, 2] =
    applyWord [2, 1, 2, 0, 1, 2, 0, 2, 0, 1] := by native_decide

/-- The matrix of relation #1 is the half-turn about (2931/625, 2808/625),
    i.e., the affine map p ↦ -p + (5862/625, 5616/625). -/
theorem rel1_matrix :
    applyWord [0, 1, 2, 0, 2, 0, 1, 2, 1, 2] =
    ((-1 : Rat), 0, 0, -1, 5862/625, 5616/625) := by native_decide

/-- Relation #2. -/
theorem rel2 :
    applyWord [0, 1, 2, 1, 2, 0, 1, 2, 0, 2] =
    applyWord [2, 0, 2, 0, 1, 2, 1, 2, 0, 1] := by native_decide

/-- Relation #3. -/
theorem rel3 :
    applyWord [0, 2, 0, 1, 2, 1, 2, 0, 1, 2] =
    applyWord [2, 0, 1, 2, 1, 2, 0, 1, 2, 0] := by native_decide

/-- Relation #4.  Both sides are pure translations (linear part = identity). -/
theorem rel4 :
    applyWord [0, 2, 0, 2, 0, 1, 2, 1, 2, 0] =
    applyWord [1, 2, 1, 2, 0, 1, 2, 0, 2, 1] := by native_decide

/-- Relation #5. -/
theorem rel5 :
    applyWord [0, 2, 0, 2, 0, 1, 2, 1, 2, 1] =
    applyWord [1, 2, 1, 2, 0, 1, 2, 0, 2, 0] := by native_decide

/-- Relation #6.  Pure translation. -/
theorem rel6 :
    applyWord [0, 2, 1, 2, 0, 1, 2, 0, 2, 0] =
    applyWord [1, 2, 0, 2, 0, 1, 2, 1, 2, 1] := by native_decide

/-- Relation #7. -/
theorem rel7 :
    applyWord [0, 2, 1, 2, 0, 1, 2, 0, 2, 1] =
    applyWord [1, 2, 0, 2, 0, 1, 2, 1, 2, 0] := by native_decide

/-- Relation #8. -/
theorem rel8 :
    applyWord [1, 2, 0, 1, 2, 0, 2, 0, 1, 2] =
    applyWord [2, 0, 1, 2, 0, 2, 0, 1, 2, 1] := by native_decide

end LengthTenRelations

/-! ## Distinctness of the eight collision-pair images

  The eight relations identify eight pairwise distinct elements of
  `Aff(ℚ²)`.  We formulate this via boolean equality (which is decidable
  for `Aff` as a product of `Rat`s) so `native_decide` can dispatch each
  inequality. -/

namespace DistinctImages

open RightTriangle345

/-- The eight collision-pair affine matrices. -/
abbrev images : List Aff :=
  [ applyWord [0, 1, 2, 0, 2, 0, 1, 2, 1, 2],
    applyWord [0, 1, 2, 1, 2, 0, 1, 2, 0, 2],
    applyWord [0, 2, 0, 1, 2, 1, 2, 0, 1, 2],
    applyWord [0, 2, 0, 2, 0, 1, 2, 1, 2, 0],
    applyWord [0, 2, 0, 2, 0, 1, 2, 1, 2, 1],
    applyWord [0, 2, 1, 2, 0, 1, 2, 0, 2, 0],
    applyWord [0, 2, 1, 2, 0, 1, 2, 0, 2, 1],
    applyWord [1, 2, 0, 1, 2, 0, 2, 0, 1, 2] ]

/-- The eight images are pairwise distinct. -/
theorem images_nodup : images.Nodup := by native_decide

end DistinctImages

/-! ## Summary

  This file machine-checks:

    *  The three reflection generators R_0, R_1, R_2 for the (3, 4, 5)
       right triangle satisfy the basic Coxeter relations R_i² = 1 and
       (R_0 R_1)² = 1.

    *  Eight length-10 word-pair equalities (the eight rows of Table 1
       of the manuscript) hold as affine matrix identities over ℚ.

    *  The relation #1 affine matrix equals the half-turn
       (-1, 0, 0, -1, 5862/625, 5616/625), i.e., rotation by π about
       the point (2931/625, 2808/625).  This is the central element
       c = X X' in the linear quotient Q.

    *  The eight collision-pair affine matrices are pairwise distinct,
       confirming the deficit count a(10) = F(13) - 8 = 225 contributed
       by these specific relations.

  All proofs are `by native_decide`, i.e., compiled to native code,
  running in seconds without Mathlib.
-/
