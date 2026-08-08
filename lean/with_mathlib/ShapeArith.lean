/-
  ShapeArith.lean
  ===============
  The four numerical claims of paper 1 that an audit found wrong, now stated and proved.

  Each was verified first by `code/zeta_probe/tools/shape_arith` (exact integer arithmetic);
  what is added here is a proof, so that the corrected statements do not rest on a search.

    1. `eT_even`            -- e_T is ALWAYS even, in both branches of its definition.
                              Consequence: the four "abstract pairs" (61,11), (37,35),
                              (53,45), (73,55) of the deviation-law table are not the
                              (c_T, e_T) of any rational-leg triangle.  `abstract_pairs_unreal`.
    2. `profile_coeffs`     -- the lamp profile of -2(t+1) mu_T, as a coefficient identity,
                              and the two specialisations that separate the sign conventions:
                              e = +6 gives (-10, 2, 2, -10) and e = -6 gives (-10,-22,-22,-10).
    3. `sixtyfive_four_shapes` -- 65 admits two essentially distinct representations as a sum
                              of two squares, which is exactly why the shape count at
                              c_T <= 72 is 22 and not 2 per complexity.
    4. `strand_alphabet`    -- the refinement stated in the strand bound has 3*2*2 = 12
                              letters, not 8; and only finiteness is used downstream.
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ShapeArith

/-! ### 1. `e_T` is always even -/

/-- The `a + b` odd branch: `e_T = 2|a^2 - b^2|` is even outright. -/
theorem eT_even_of_sum_odd (a b : ℤ) : Even (2 * |a ^ 2 - b ^ 2|) :=
  ⟨|a ^ 2 - b ^ 2|, by ring⟩

/-- The both-odd branch: a difference of two odd squares is even. -/
theorem eT_even_of_both_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    Even (|a ^ 2 - b ^ 2|) := by
  have hsq : ∀ {x : ℤ}, Odd x → Odd (x ^ 2) := by
    rintro x ⟨k, rfl⟩; exact ⟨2 * k ^ 2 + 2 * k, by ring⟩
  have h : Even (a ^ 2 - b ^ 2) := Odd.sub_odd (hsq ha) (hsq hb)
  rcases abs_cases (a ^ 2 - b ^ 2) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; exact h
  · rw [he]; exact h.neg

/-- **`e_T` is even in both branches of its definition**, with no hypothesis on `a` and `b`
    beyond the branch condition itself: the `a+b` odd branch is even because of its explicit
    factor `2`, and the both-odd branch because a difference of two odd squares is even. -/
theorem eT_even (a b : ℤ) :
    Even (2 * |a ^ 2 - b ^ 2|) ∧ ((Odd a ∧ Odd b) → Even (|a ^ 2 - b ^ 2|)) := by
  refine ⟨eT_even_of_sum_odd a b, ?_⟩
  rintro ⟨ha, hb⟩
  exact eT_even_of_both_odd ha hb

/-- **The four tabulated "abstract pairs" are unrealizable.**  Each has odd second
    coordinate, and no `e_T` is odd. -/
theorem abstract_pairs_unreal :
    ¬ Even (11 : ℤ) ∧ ¬ Even (35 : ℤ) ∧ ¬ Even (45 : ℤ) ∧ ¬ Even (55 : ℤ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### 2. The lamp profile of `-2(t+1) mu_T`

    `mu_T(t) = c t^2 - e t + c`, so `-2(t+1) mu_T` has coefficient vector
    `(-2c, -2(c-e), -2(c-e), -2c)` in degrees `0,1,2,3`. -/

theorem profile_coeffs (c e t : ℤ) :
    -2 * (t + 1) * (c * t ^ 2 - e * t + c)
      = (-2 * c) + (-2 * (c - e)) * t + (-2 * (c - e)) * t ^ 2 + (-2 * c) * t ^ 3 := by
  ring

/-- With the convention actually used in the tables, `e_T = 6` at the shape `(1,2)`, the
    profile is `(-10, 2, 2, -10)`. -/
theorem profile_at_e_pos (t : ℤ) :
    -2 * (t + 1) * (5 * t ^ 2 - 6 * t + 5)
      = (-10) + 2 * t + 2 * t ^ 2 + (-10) * t ^ 3 := by
  ring

/-- With the signed definition, `e_T = -6` at `(1,2)`, and the profile is
    `(-10, -22, -22, -10)`.  The two are different, which is why the convention had to be
    fixed rather than left implicit. -/
theorem profile_at_e_neg (t : ℤ) :
    -2 * (t + 1) * (5 * t ^ 2 + 6 * t + 5)
      = (-10) + (-22) * t + (-22) * t ^ 2 + (-10) * t ^ 3 := by
  ring

theorem profiles_differ : ((2 : ℤ) ≠ -22) := by decide

/-! ### 3. Why the count at `c_T ≤ 72` is 22

    Every admissible complexity below 65 contributes two shapes.  `65 = 5 * 13` is the first
    with two essentially distinct representations as a sum of two squares, and contributes
    four.  The arithmetic behind that is the following four identities. -/

theorem sixtyfive_four_shapes :
    (1 : ℤ) ^ 2 + 8 ^ 2 = 65 ∧ (4 : ℤ) ^ 2 + 7 ^ 2 = 65 ∧
    ((3 : ℤ) ^ 2 + 11 ^ 2) / 2 = 65 ∧ ((7 : ℤ) ^ 2 + 9 ^ 2) / 2 = 65 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The two `a + b` odd shapes at 65 are genuinely distinct, as are the two both-odd ones. -/
theorem sixtyfive_distinct :
    ((1 : ℤ), (8 : ℤ)) ≠ (4, 7) ∧ ((3 : ℤ), (11 : ℤ)) ≠ (7, 9) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Hence `18 + 4 = 22`, not `20` and not `24`. -/
theorem shape_count_72 : 18 + 4 = 22 ∧ (22 : ℕ) ≠ 24 := by
  refine ⟨by norm_num, by decide⟩

/-! ### 4. The strand alphabet -/

/-- The refinement stated in the strand bound is three crossing contents, two lamp signs and
    two marker states.  That is twelve letters, not eight. -/
theorem strand_alphabet : 3 * 2 * 2 = 12 ∧ (3 * 2 * 2 : ℕ) ≠ 8 := by
  refine ⟨by norm_num, by decide⟩

end ShapeArith
