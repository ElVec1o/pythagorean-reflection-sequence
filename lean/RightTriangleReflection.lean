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

/-! ### Explicit matrix values for relations #2 - #8.

  Six of the eight identities are half-turns (linear part = -I);
  the remaining two (relations #4 and #6) are pure translations
  (linear part = +I).  All eight matrices are pairwise distinct. -/

/-- Relation #2 evaluates to the half-turn about (819/625, -2808/625). -/
theorem rel2_matrix :
    applyWord [0, 1, 2, 1, 2, 0, 1, 2, 0, 2] =
    ((-1 : Rat), 0, 0, -1, 1638/625, -5616/625) := by native_decide

/-- Relation #3 evaluates to the half-turn about (-117/25, 0). -/
theorem rel3_matrix :
    applyWord [0, 2, 0, 1, 2, 1, 2, 0, 1, 2] =
    ((-1 : Rat), 0, 0, -1, -234/25, 0) := by native_decide

/-- Relation #4 is the pure translation (-2112/625, 5616/625). -/
theorem rel4_matrix :
    applyWord [0, 2, 0, 2, 0, 1, 2, 1, 2, 0] =
    ((1 : Rat), 0, 0, 1, -2112/625, 5616/625) := by native_decide

/-- Relation #5 evaluates to the half-turn about (819/625, 2808/625). -/
theorem rel5_matrix :
    applyWord [0, 2, 0, 2, 0, 1, 2, 1, 2, 1] =
    ((-1 : Rat), 0, 0, -1, 1638/625, 5616/625) := by native_decide

/-- Relation #6 is the pure translation (2112/625, -5616/625). -/
theorem rel6_matrix :
    applyWord [0, 2, 1, 2, 0, 1, 2, 0, 2, 0] =
    ((1 : Rat), 0, 0, 1, 2112/625, -5616/625) := by native_decide

/-- Relation #7 evaluates to the half-turn about (2931/625, -2808/625). -/
theorem rel7_matrix :
    applyWord [0, 2, 1, 2, 0, 1, 2, 0, 2, 1] =
    ((-1 : Rat), 0, 0, -1, 5862/625, -5616/625) := by native_decide

/-- Relation #8 evaluates to the half-turn about (3, 144/25). -/
theorem rel8_matrix :
    applyWord [1, 2, 0, 1, 2, 0, 2, 0, 1, 2] =
    ((-1 : Rat), 0, 0, -1, 6, 288/25) := by native_decide

end LengthTenRelations

/-! ## Universality check on a second triangle: (5, 12, 13)

  We verify that relation #1 also holds on the (5, 12, 13) right
  triangle (a different choice of legs, still unequal).  By the
  universality theorem this is expected for all eight relations; here
  we machine-check it for the first one as a concrete instance. -/

namespace RightTriangle5_12_13

def R0 : Aff := (1, 0, 0, -1, 0, 0)
def R1 : Aff := (-1, 0, 0, 1, 10, 0)
-- Side CA on the (5,12,13) triangle: line through origin with direction (5, 12).
-- L = 169, so a = (25 - 144)/169 = -119/169, b = 120/169, d = 119/169.
def R2 : Aff := (-119/169, 120/169, 120/169, 119/169, 0, 0)

def applyWord : List Nat → Aff
  | []      => Aff.one
  | i :: is =>
      let g := match i with
        | 0 => R0
        | 1 => R1
        | _ => R2
      Aff.comp g (applyWord is)

/-- Relation #1 holds on the (5, 12, 13) triangle too. -/
theorem rel1_on_5_12_13 :
    applyWord [0, 1, 2, 0, 2, 0, 1, 2, 1, 2] =
    applyWord [2, 1, 2, 0, 1, 2, 0, 2, 0, 1] := by native_decide

end RightTriangle5_12_13

/-! ## Direct BFS verification of a(n) for small n

  We perform a true breadth-first search of the Cayley orbit on the
  (3, 4, 5) triangle, layer by layer, and machine-check the size of
  each layer for small `n`.  This directly verifies the first several
  terms of OEIS A396406:
      a(0), a(1), a(2), a(3), a(4), a(5) = 1, 3, 5, 8, 13, 21. -/

namespace BFSCounts

open RightTriangle345

/-- Apply each of R_0, R_1, R_2 to every element of the input layer. -/
def expandLayer (layer : List Aff) : List Aff :=
  layer.bind fun M => [Aff.comp R0 M, Aff.comp R1 M, Aff.comp R2 M]

/-- One BFS step: from `(seen, lastLayer)`, produce `(seen ∪ newLayer, newLayer)`
    where `newLayer` is the set of new elements not yet seen. -/
def bfsStep (state : List Aff × List Aff) : List Aff × List Aff :=
  let (seen, lastLayer) := state
  let candidates := expandLayer lastLayer
  let newLayer := (candidates.filter (fun M => !seen.elem M)).eraseDups
  (seen ++ newLayer, newLayer)

/-- Iterate `bfsStep` n times from the identity. -/
def bfsState : Nat → List Aff × List Aff
  | 0     => ([Aff.one], [Aff.one])
  | n + 1 => bfsStep (bfsState n)

/-- The n-th layer count.  This is `a(n)` in OEIS A396406. -/
def a (n : Nat) : Nat := (bfsState n).snd.length

-- Machine-checked values of a(n) for n = 0..10.
example : a 0 = 1 := by native_decide
example : a 1 = 3 := by native_decide
example : a 2 = 5 := by native_decide
example : a 3 = 8 := by native_decide
example : a 4 = 13 := by native_decide
example : a 5 = 21 := by native_decide
example : a 6 = 34 := by native_decide
example : a 7 = 55 := by native_decide
example : a 8 = 89 := by native_decide
example : a 9 = 144 := by native_decide
example : a 10 = 225 := by native_decide
example : a 11 = 351 := by native_decide
example : a 12 = 554 := by native_decide
example : a 13 = 875 := by native_decide
example : a 14 = 1345 := by native_decide
example : a 15 = 2066 := by native_decide
example : a 16 = 3203 := by native_decide
example : a 17 = 4971 := by native_decide

end BFSCounts

/-! ## Summary of all checks

  Total machine-checked theorems and examples in this file:

  * Basic Coxeter relations R_i^2 = 1 (i = 0, 1, 2) and (R_0 R_1)^2 = 1
  * Eight word-pair equalities rel1 - rel8 (length-10 affine relations)
  * Eight explicit affine matrix evaluations rel1_matrix - rel8_matrix
  * Pairwise distinctness of the eight collision-pair images
    (via `List.Nodup`)
  * Relation #1 also holds on the (5, 12, 13) triangle
    (rel1_on_5_12_13), a concrete instance of universality
  * Direct BFS computation of a(0)..a(5) = 1, 3, 5, 8, 13, 21
    (the first six terms of OEIS A396406)

  All proofs are `by native_decide`.  No Mathlib dependency.  Builds in
  a few seconds on a modest machine. -/

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
