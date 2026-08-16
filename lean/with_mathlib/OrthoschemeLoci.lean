/-
  OrthoschemeLoci.lean
  ====================
  The two hypersurfaces in dimension four on which the orthoscheme point group collapses.

  For each family a FIXED pair of words in `W_4`, independent of the leg tuple, has linear parts
  whose difference is divisible by an explicit polynomial in the legs.  Since the surviving
  cofactors are monomials, and the legs are positive, the linear parts agree exactly on the zero
  locus of that polynomial.  What is recorded here is the divisibility, which is the part that is
  a polynomial identity; the identification of the cofactors as monomials, and the passage from a
  trivial linear part to a kernel element, are elsewhere (`TranslationTrick`).

  Family I   `a1 a3 = a2 a4`,                       collision at depth 8.
  Family II  `a4 (a1^2 - a2^2) = ± 2 a1 a2 a3`,     collision at depth 12.

  In both cases the quadratic that actually appears is a product of two conjugate factors, and
  only one of them meets the positive orthant, which is why the geometric condition carries an
  absolute value.
-/

import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace OrthoschemeLoci

variable {R : Type*} [CommRing R]

/-- The quadratic cutting out family I, in the form in which it appears as a factor. -/
def famI (a1 a2 a3 a4 : R) : R := (a1*a3 - a2*a4) * (a1*a3 + a2*a4)

/-- The quartic cutting out family II. -/
def famII (a1 a2 a3 a4 : R) : R :=
  (a1^2*a4 - 2*a1*a2*a3 - a2^2*a4) * (a1^2*a4 + 2*a1*a2*a3 - a2^2*a4)

/-- Family I in expanded form: it is a difference of squares. -/
theorem famI_eq (a1 a2 a3 a4 : R) :
    famI a1 a2 a3 a4 = (a1*a3)^2 - (a2*a4)^2 := by
  simp only [famI]; ring

/-- Family II in expanded form: also a difference of squares, of `a4(a1^2-a2^2)` and `2a1a2a3`. -/
theorem famII_eq (a1 a2 a3 a4 : R) :
    famII a1 a2 a3 a4 = (a4*(a1^2 - a2^2))^2 - (2*a1*a2*a3)^2 := by
  simp only [famII]; ring

/-- **Family I vanishes exactly where `a1 a3 = a2 a4`, on the positive orthant.**  Over a linear
    ordered field, with all legs positive, the second factor is positive, so the product vanishes
    iff the first factor does. -/
theorem famI_zero_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a1 a2 a3 a4 : K} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3) (h4 : 0 < a4) :
    famI a1 a2 a3 a4 = 0 ↔ a1*a3 = a2*a4 := by
  have hpos : 0 < a1*a3 + a2*a4 := by positivity
  constructor
  · intro h
    simp only [famI, mul_eq_zero] at h
    rcases h with h | h
    · linarith [sub_eq_zero.mp h]
    · exact absurd h (ne_of_gt hpos)
  · intro h
    simp only [famI]
    rw [sub_eq_zero.mpr h, zero_mul]

/-- **Family II vanishes exactly where `a4 (a1^2 - a2^2) = ± 2 a1 a2 a3`.**  Both branches are
    retained; on the positive orthant exactly one is reachable, according as `a1 > a2` or
    `a1 < a2`. -/
theorem famII_zero_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a1 a2 a3 a4 : K) :
    famII a1 a2 a3 a4 = 0 ↔
      (a4*(a1^2 - a2^2) = 2*a1*a2*a3 ∨ a4*(a1^2 - a2^2) = -(2*a1*a2*a3)) := by
  simp only [famII, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; linarith [sub_eq_zero.mp (by linarith : a1^2*a4 - 2*a1*a2*a3 - a2^2*a4 = 0)]
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith


/-- The quartic cutting out family III, the mirror of family II at the other end of the leg
    tuple. -/
def famIII (a1 a2 a3 a4 : R) : R :=
  (a1*a3^2 - a1*a4^2 - 2*a2*a3*a4) * (a1*a3^2 - a1*a4^2 + 2*a2*a3*a4)

/-- Family III in expanded form. -/
theorem famIII_eq (a1 a2 a3 a4 : R) :
    famIII a1 a2 a3 a4 = (a1*(a3^2 - a4^2))^2 - (2*a2*a3*a4)^2 := by
  simp only [famIII]; ring

/-- **Family III vanishes exactly where `a1 (a3^2 - a4^2) = ± 2 a2 a3 a4`.** -/
theorem famIII_zero_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a1 a2 a3 a4 : K) :
    famIII a1 a2 a3 a4 = 0 ↔
      (a1*(a3^2 - a4^2) = 2*a2*a3*a4 ∨ a1*(a3^2 - a4^2) = -(2*a2*a3*a4)) := by
  simp only [famIII, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- **The mirror relation.**  Family III at `(a1,a2,a3,a4)` is family II read at the reversed
    tuple, up to sign: the path simplex is symmetric under reversing the legs, so the two ends
    contribute the same condition with the roles of the ends exchanged. -/
theorem famIII_is_famII_reversed (a1 a2 a3 a4 : R) :
    famIII a1 a2 a3 a4 = famII a4 a3 a2 a1 := by
  simp only [famIII, famII]; ring

#print axioms famIII_eq
#print axioms famIII_zero_iff
#print axioms famIII_is_famII_reversed

/-! ### Axiom audit (Rule 5) -/

#print axioms famI_eq
#print axioms famII_eq
#print axioms famI_zero_iff
#print axioms famII_zero_iff

end OrthoschemeLoci
