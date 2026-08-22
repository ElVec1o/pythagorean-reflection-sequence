/-
Edge data, and the two arithmetic steps that gap-freeness buys.

Each edge of the span carries a deposit `d` and a travel indicator `f ∈ {-1,0,1}`,
subject to the parity `d ≡ f (mod 2)`.  A *gap edge* is one with `d = 0` and
`f = 0`.

Two steps of `thm:nogap` live here.  `dep_ne_zero_of_not_gap` is step 2: away from
gap edges the deposit never vanishes, because a vanishing deposit forces `f` even,
hence `f = 0` in the allowed range, hence a gap.  `mult_eq_abs_dep` is step 3's
first half: the minimum crossing multiplicity `max |d| |f|` is then `|d|`, which is
what makes the sign split forced in `NoGapMerge.split_forced_pos/neg`.
-/
import Mathlib.Tactic

namespace EdgeData

/-- The travel indicator takes only three values. -/
def IsTravel (f : ℤ) : Prop := f = -1 ∨ f = 0 ∨ f = 1

/-- A gap edge: no deposit and no travel. -/
def IsGap (d f : ℤ) : Prop := d = 0 ∧ f = 0

/-- **Step 2.** Off a gap edge the deposit is non-zero.  A vanishing deposit makes
`f` even by parity, and the only even travel indicator is `0`, which would be a
gap. -/
theorem dep_ne_zero_of_not_gap {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hgap : ¬ IsGap d f) : d ≠ 0 := by
  intro hd
  apply hgap
  refine ⟨hd, ?_⟩
  rcases hf with h | h | h <;> subst h <;> omega

/-- **Step 3, first half.** With a non-zero deposit the minimum multiplicity is the
absolute deposit: `|d| ≥ |f|` in both parities. -/
theorem one_le_abs {d : ℤ} (hd : d ≠ 0) : 1 ≤ |d| := by
  rcases abs_cases d with ⟨he, _⟩ | ⟨he, _⟩ <;> omega

theorem abs_dep_ge_abs_trav {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hd : d ≠ 0) : |f| ≤ |d| := by
  have h1 : 1 ≤ |d| := one_le_abs hd
  rcases hf with h | h | h <;> subst h
  · simpa using h1
  · simpa using abs_nonneg d
  · simpa using h1

theorem mult_eq_abs_dep {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hd : d ≠ 0) : max |d| |f| = |d| :=
  max_eq_left (abs_dep_ge_abs_trav hf hpar hd)

/-- The two together: a non-gap edge has non-zero deposit and multiplicity `|d|`. -/
theorem nongap_mult {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hgap : ¬ IsGap d f) : d ≠ 0 ∧ max |d| |f| = |d| :=
  let hd := dep_ne_zero_of_not_gap hf hpar hgap
  ⟨hd, mult_eq_abs_dep hf hpar hd⟩

/-- And the multiplicity is at least one, which is the covering hypothesis
`SharedSite.shared_site_exists` needs: every span edge carries a crossing. -/
theorem mult_pos {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hgap : ¬ IsGap d f) : 1 ≤ max |d| |f| := by
  obtain ⟨hd, hm⟩ := nongap_mult hf hpar hgap
  rw [hm]
  exact one_le_abs hd

/-! ### Non-vacuity -/

/-- A bulk edge: even deposit, no travel.  Not a gap, deposit non-zero,
multiplicity `2`. -/
theorem witness_bulk : (2 : ℤ) ≠ 0 ∧ max |(2:ℤ)| |(0:ℤ)| = 2 :=
  nongap_mult (Or.inr (Or.inl rfl)) (by decide) (by simp [IsGap])

/-- A travel edge: odd deposit, travel `1`.  Multiplicity `1`. -/
theorem witness_travel : (1 : ℤ) ≠ 0 ∧ max |(1:ℤ)| |(1:ℤ)| = 1 :=
  nongap_mult (Or.inr (Or.inr rfl)) (by decide) (by simp [IsGap])

/-- The gap edge really is excluded rather than the hypothesis being unsatisfiable:
`d = f = 0` satisfies the travel and parity conditions but *is* a gap. -/
theorem witness_gap_excluded : IsTravel 0 ∧ ((0:ℤ) - 0) % 2 = 0 ∧ IsGap 0 0 :=
  ⟨Or.inr (Or.inl rfl), by decide, ⟨rfl, rfl⟩⟩

/-- And a gap edge has multiplicity `0`, which is why reachability has to force it
to `2`: the covering hypothesis fails there. -/
theorem witness_gap_mult_zero : max |(0:ℤ)| |(0:ℤ)| = 0 := by decide

-- Certification (Rule 5).
#print axioms EdgeData.dep_ne_zero_of_not_gap
#print axioms EdgeData.one_le_abs
#print axioms EdgeData.abs_dep_ge_abs_trav
#print axioms EdgeData.mult_eq_abs_dep
#print axioms EdgeData.nongap_mult
#print axioms EdgeData.mult_pos
#print axioms EdgeData.witness_bulk
#print axioms EdgeData.witness_travel
#print axioms EdgeData.witness_gap_excluded
#print axioms EdgeData.witness_gap_mult_zero

end EdgeData
