/-
Lamp configurations, and the step `cor:localzero` rests on.

A group element carries a displacement `k` and a lamp configuration assigning a
deposit to each edge.  The travel indicator is `NoGapCutFree.f`, already defined
and used for the cut analysis.

`no_gap_of_pure_travel` is the hypothesis step of `cor:localzero`: an element whose
lamp support lies inside its travel interval has no gap edge.  The span of such an
element is the travel interval itself, where the indicator is `±1`, so no edge can
have both deposit and indicator zero.  Until now this step lived only in prose.
-/
import Mathlib.Tactic
import NoGapCutFree
import EdgeData

namespace GroupElt

open NoGapCutFree

/-- Membership in the travel interval `I_k`. -/
def InTravel (k j : ℤ) : Prop := (0 ≤ j ∧ j < k) ∨ (k ≤ j ∧ j < 0)

/-- On the travel interval the indicator is non-zero. -/
theorem f_ne_zero_of_inTravel {k j : ℤ} (h : InTravel k j) : f k j ≠ 0 := by
  unfold f
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos ⟨h1, h2⟩]; norm_num
  · rw [if_neg (by omega), if_pos ⟨h1, h2⟩]; norm_num

/-- Conversely, off the travel interval the indicator vanishes. -/
theorem f_eq_zero_of_not_inTravel {k j : ℤ} (h : ¬ InTravel k j) : f k j = 0 := by
  unfold f
  unfold InTravel at h
  split_ifs with h1 h2
  · exact absurd (Or.inl h1) h
  · exact absurd (Or.inr h2) h
  · rfl

/-- **The hypothesis step of `cor:localzero`.**  If every lamp lies inside the
travel interval, then every edge of the span has non-zero indicator, so no edge is
a gap edge.  `hspan` says `j` is in the span, which for a pure-travel element means
it carries a lamp or lies in the travel interval. -/
theorem no_gap_of_pure_travel {k j : ℤ} {lamps : ℤ → ℤ}
    (hpure : ∀ i : ℤ, lamps i ≠ 0 → InTravel k i)
    (hspan : lamps j ≠ 0 ∨ InTravel k j) :
    ¬ EdgeData.IsGap (lamps j) (f k j) := by
  rintro ⟨hd, hf⟩
  have hin : InTravel k j := by
    rcases hspan with h | h
    · exact hpure j h
    · exact h
  exact f_ne_zero_of_inTravel hin hf

/-- Consequently a pure-travel element satisfies the hypothesis of the gap-free
theorem at every edge of its span. -/
theorem gapFree_of_pure_travel {k : ℤ} {lamps : ℤ → ℤ}
    (hpure : ∀ i : ℤ, lamps i ≠ 0 → InTravel k i) :
    ∀ j : ℤ, (lamps j ≠ 0 ∨ InTravel k j) → ¬ EdgeData.IsGap (lamps j) (f k j) :=
  fun j hj => no_gap_of_pure_travel hpure hj

/-! ### Non-vacuity

`k = 2`, lamps `1` on edge `0` and `1` on edge `1`, both inside `I_2 = {0,1}`.
Every span edge is a travel edge, so none is a gap. -/

def lampsW : ℤ → ℤ := fun j => if j = 0 ∨ j = 1 then 1 else 0

theorem pureW : ∀ i : ℤ, lampsW i ≠ 0 → InTravel 2 i := by
  intro i hi
  unfold lampsW at hi
  by_cases h : i = 0 ∨ i = 1
  · rcases h with rfl | rfl <;> exact Or.inl (by norm_num)
  · rw [if_neg h] at hi; exact absurd rfl hi

theorem witness_no_gap : ¬ EdgeData.IsGap (lampsW 0) (f 2 0) :=
  no_gap_of_pure_travel pureW (Or.inr (Or.inl (by norm_num)))

/-- And the element is non-degenerate: the deposit really is non-zero there, so the
statement is not about an empty span. -/
theorem witness_dep_ne_zero : lampsW 0 ≠ 0 := by norm_num [lampsW]

-- Certification (Rule 5).
#print axioms GroupElt.f_ne_zero_of_inTravel
#print axioms GroupElt.f_eq_zero_of_not_inTravel
#print axioms GroupElt.no_gap_of_pure_travel
#print axioms GroupElt.gapFree_of_pure_travel
#print axioms GroupElt.witness_no_gap
#print axioms GroupElt.witness_dep_ne_zero

end GroupElt
