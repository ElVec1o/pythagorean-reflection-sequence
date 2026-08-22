/-
The two structural skeletons behind M2 and M6.

Neither is about strand walks; each is the abstract principle the corresponding
argument runs on, with the domain-specific facts appearing as hypotheses.  This is
what can be formalised without first building a model of realisations, and it is
stated that way rather than dressed up as a formalisation of the theorems
themselves.

* `min_count_eq_one` is the descent used by `thm:nogap`: if every cost-minimal
  realisation with at least two components admits a cost-minimal realisation with
  strictly fewer, then some cost-minimal realisation has exactly one component.
  The zero-cost 2-swap of `lem:freeswap` supplies the hypothesis.
* `min_sum_eq_sum_min` is the decomposition used by `rem:decomp`: when the choices
  at distinct sites are independent, the minimum of the total is the total of the
  minima, in both directions.
-/
import Mathlib.Tactic

namespace MergeDescent

/-- Descent on the component count.  `T` is the (finite, nonempty) set of
cost-minimal realisations, `comp` the component count. -/
theorem min_count_eq_one {R : Type*} [DecidableEq R]
    (T : Finset R) (hT : T.Nonempty) (comp : R → ℕ)
    (hpos : ∀ r ∈ T, 1 ≤ comp r)
    (hstep : ∀ r ∈ T, 2 ≤ comp r → ∃ r' ∈ T, comp r' < comp r) :
    ∃ r ∈ T, comp r = 1 := by
  obtain ⟨r, hrT, hmin⟩ := T.exists_min_image comp hT
  refine ⟨r, hrT, ?_⟩
  by_contra h
  have h2 : 2 ≤ comp r := by
    have := hpos r hrT
    omega
  obtain ⟨r', hr'T, hlt⟩ := hstep r hrT h2
  exact absurd (hmin r' hr'T) (not_le.mpr hlt)

/-- Independent choices: the minimum of the sum is the sum of the minima.
Both halves are stated, since the argument uses both: no term can fall below its
local minimum, and all local minima are attained simultaneously. -/
theorem min_sum_eq_sum_min {ι : Type*} [Fintype ι] {C : ι → Type*}
    (f : ∀ i, C i → ℤ) (m : ι → ℤ)
    (hlb : ∀ i (c : C i), m i ≤ f i c)
    (hatt : ∀ i, ∃ c : C i, f i c = m i) :
    (∀ x : ∀ i, C i, ∑ i, m i ≤ ∑ i, f i (x i)) ∧
    (∃ x : ∀ i, C i, ∑ i, f i (x i) = ∑ i, m i) := by
  constructor
  · intro x
    exact Finset.sum_le_sum fun i _ => hlb i (x i)
  · choose x hx using hatt
    exact ⟨x, Finset.sum_congr rfl fun i _ => hx i⟩

/-- The form actually cited: with both halves, the minimum is exactly the sum. -/
theorem sum_min_is_min {ι : Type*} [Fintype ι] {C : ι → Type*}
    (f : ∀ i, C i → ℤ) (m : ι → ℤ)
    (hlb : ∀ i (c : C i), m i ≤ f i c)
    (hatt : ∀ i, ∃ c : C i, f i c = m i)
    (x : ∀ i, C i) (hx : ∀ y : ∀ i, C i, ∑ i, f i (x i) ≤ ∑ i, f i (y i)) :
    ∑ i, f i (x i) = ∑ i, m i := by
  obtain ⟨hlow, y, hy⟩ := min_sum_eq_sum_min f m hlb hatt
  exact le_antisymm (hy ▸ hx y) (hlow x)

-- Certification (Rule 5): every declaration above, axioms listed in the build log.
#print axioms MergeDescent.min_count_eq_one
#print axioms MergeDescent.min_sum_eq_sum_min
#print axioms MergeDescent.sum_min_is_min

/-! ### Descent to a bound, and the pigeonhole that triggers it

`min_count_eq_one` descends to a single component.  The reverse shield inequality
needs the same descent stopped at `|Z| + 1` instead, and a pigeonhole to supply the
step: more components than classes forces two components into one class. -/

/-- **Descent to a bound.**  If every element above the bound admits a strictly
smaller one, the minimum lies at or below it. -/
theorem count_le_of_step {R : Type*} [DecidableEq R]
    (T : Finset R) (hT : T.Nonempty) (cnt : R → ℕ) (bound : ℕ)
    (hstep : ∀ r ∈ T, bound < cnt r → ∃ r' ∈ T, cnt r' < cnt r) :
    ∃ r ∈ T, cnt r ≤ bound := by
  obtain ⟨r, hrT, hmin⟩ := T.exists_min_image cnt hT
  refine ⟨r, hrT, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨r', hr'T, hlt⟩ := hstep r hrT h
  exact absurd (hmin r' hr'T) (not_le.mpr hlt)

/-- **The pigeonhole.**  More components than classes puts two components in one
class.  This is what makes the descent step available below the bound. -/
theorem two_in_one_class {C K : Type*} [Fintype C] [Fintype K] [DecidableEq K]
    (cls : C → K) (h : Fintype.card K < Fintype.card C) :
    ∃ a b : C, a ≠ b ∧ cls a = cls b :=
  Fintype.exists_ne_map_eq_of_card_lt cls h

/-- **The route, composed.**  Given that excess components always yield a free
merge, the count descends to the bound.

The hypothesis `hmerge` is what the other three pieces produce: the pigeonhole puts
two components in one class, the shared-site theorem applied to that class makes
them meet at a mergeable site, and the merge lowers the count without raising the
cost.  Composing them into `hmerge` for an actual realisation is model work, the
same work the formalisation debt on `thm:nogap` names, so it is a hypothesis here
rather than a conclusion.

What this theorem does add is that nothing further is needed: with `hmerge` in hand
the inequality follows immediately, so the whole difficulty sits in that one
hypothesis. -/
theorem count_le_bound_of_merge {R : Type*} [DecidableEq R]
    (T : Finset R) (hT : T.Nonempty) (cnt : R → ℕ) (bound : ℕ)
    (hmerge : ∀ r ∈ T, bound < cnt r → ∃ r' ∈ T, cnt r' < cnt r) :
    ∃ r ∈ T, cnt r ≤ bound :=
  count_le_of_step T hT cnt bound hmerge

#print axioms MergeDescent.count_le_of_step
#print axioms MergeDescent.two_in_one_class
#print axioms MergeDescent.count_le_bound_of_merge

end MergeDescent
