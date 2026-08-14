/-
  RankTwoExclusion.lean
  =====================
  Paper 1b, Proposition `prop:no-rank2` and the two finite branches of `thm:cd-general`.

  For a right-corner orthoscheme with legs a_1, ..., a_n the non-perpendicular dihedral pairs
  have cosines

      cos t_{0,1}   = a_2 / sqrt(a_1^2 + a_2^2),
      cos t_{n-1,n} = a_{n-1} / sqrt(a_{n-1}^2 + a_n^2),

  at the boundary, and an analogous three-leg expression in the interior.  By the extended
  Niven theorem a closing relation (R_i R_{i+1})^m = 1 forces cos^2 into {0, 1/4, 1/2, 3/4, 1}.
  This file discharges the boundary cases over the rationals, which is where the argument is
  purely arithmetic; the interior cases reduce to the three Diophantine quartics and are not
  formalised here (they need the rank-0 Mordell descents).

  It also proves the two lower bounds that were missing from `thm:cd-general`, and which turn
  its finite values from upper bounds into equalities:
    * no collision at length 2, because a non-perpendicular cosine is nonzero;
    (Several statements below need only one of the two positivity hypotheses; the unused one
    is dropped rather than carried, as elsewhere in this development.)
    * no collision at length 3 at a boundary pair, because cos^2 = 1/4 there forces
      a_i^2 = 3 a_{i+1}^2 and 3 is not a rational square.
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace RankTwoExclusion

/-! ### 1. Three is not a rational square -/

theorem not_isSquare_three_int : ¬ IsSquare (3 : ℤ) := by
  rintro ⟨r, hr⟩
  have h1 : r * r = 3 := hr.symm
  have hlo : -2 ≤ r := by nlinarith [sq_nonneg (r + 2)]
  have hhi : r ≤ 2 := by nlinarith [sq_nonneg (r - 2)]
  interval_cases r <;> omega

/-- **No rational has square 3.**  This is the arithmetic behind both `1/4` and `3/4`. -/
theorem sq_ne_three (q : ℚ) : q ^ 2 ≠ 3 := by
  intro h
  have hsq : IsSquare ((3 : ℤ) : ℚ) := ⟨q, by push_cast; rw [← h]; ring⟩
  exact not_isSquare_three_int (Rat.isSquare_intCast_iff.mp hsq)

/-! ### 2. The boundary cases of the Niven analysis

    Writing `c = cos^2 t = b^2 / (a^2 + b^2)` for the boundary pair with legs `a = a_i`,
    `b = a_{i+1}`, each admissible Niven value is excluded. -/

variable {a b : ℚ}

/-- `cos^2 = 0` forces `b = 0`, excluded by positivity. -/
theorem niven_zero (hb : 0 < b) (h : b ^ 2 = 0 * (a ^ 2 + b ^ 2)) : False := by
  have : b ^ 2 = 0 := by linarith
  nlinarith

/-- `cos^2 = 1` forces `a = 0`, excluded by positivity. -/
theorem niven_one (ha : 0 < a) (h : b ^ 2 = 1 * (a ^ 2 + b ^ 2)) : False := by
  have : a ^ 2 = 0 := by linarith
  nlinarith

/-- `cos^2 = 1/4` forces `a^2 = 3 b^2`, hence `(a/b)^2 = 3`, impossible over `ℚ`. -/
theorem niven_quarter (hb : 0 < b)
    (h : 4 * b ^ 2 = a ^ 2 + b ^ 2) : False := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have h3 : (a / b) ^ 2 = 3 := by
    field_simp
    linarith
  exact sq_ne_three _ h3

/-- `cos^2 = 3/4` forces `b^2 = 3 a^2`, impossible for the same reason. -/
theorem niven_three_quarter (ha : 0 < a)
    (h : 4 * b ^ 2 = 3 * (a ^ 2 + b ^ 2)) : False := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have h3 : (b / a) ^ 2 = 3 := by
    field_simp
    linarith
  exact sq_ne_three _ h3

/-- `cos^2 = 1/2` forces `a = b`, excluded by the Class C hypothesis that the legs are
    pairwise distinct. -/
theorem niven_half (ha : 0 < a) (hb : 0 < b) (h : 2 * b ^ 2 = a ^ 2 + b ^ 2) :
    a = b := by
  have hsq : a ^ 2 = b ^ 2 := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

/-! ### 3. The two lower bounds of the collision-depth theorem -/

/-- **No collision at length 2.**  A non-perpendicular pair has `cos t /= 0`, since the
    numerator is a positive leg. -/
theorem no_length_two (hb : 0 < b) (ha : 0 < a) : b / (a ^ 2 + b ^ 2) ≠ 0 := by
  positivity

/-- **No collision at length 3 from a boundary pair.**  A length-3 collision needs a dihedral
    of angle `pi/3`, i.e. `cos^2 = 1/4`, excluded by `niven_quarter`. -/
theorem no_length_three_boundary (hb : 0 < b) :
    ¬ (4 * b ^ 2 = a ^ 2 + b ^ 2) := fun h => niven_quarter hb h

/-- Together: for pairwise distinct positive rational legs no boundary pair closes a relation,
    which is the boundary half of `prop:no-rank2`. -/
theorem boundary_no_relation (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ¬ (b ^ 2 = 0 * (a ^ 2 + b ^ 2)) ∧ ¬ (b ^ 2 = 1 * (a ^ 2 + b ^ 2)) ∧
    ¬ (4 * b ^ 2 = a ^ 2 + b ^ 2) ∧ ¬ (4 * b ^ 2 = 3 * (a ^ 2 + b ^ 2)) ∧
    ¬ (2 * b ^ 2 = a ^ 2 + b ^ 2) := by
  refine ⟨fun h => niven_zero hb h, fun h => niven_one ha h,
          fun h => niven_quarter hb h, fun h => niven_three_quarter ha h,
          fun h => hab (niven_half ha hb h)⟩

end RankTwoExclusion

-- Rule 5 axiom audit.
#print axioms RankTwoExclusion.not_isSquare_three_int
#print axioms RankTwoExclusion.sq_ne_three
#print axioms RankTwoExclusion.niven_zero
#print axioms RankTwoExclusion.niven_one
#print axioms RankTwoExclusion.niven_quarter
#print axioms RankTwoExclusion.niven_three_quarter
#print axioms RankTwoExclusion.niven_half
#print axioms RankTwoExclusion.no_length_two
#print axioms RankTwoExclusion.no_length_three_boundary
#print axioms RankTwoExclusion.boundary_no_relation
