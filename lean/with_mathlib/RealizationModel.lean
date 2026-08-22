/-
The realisation model, and `thm:nogap` instantiated on it.

A realisation is carried by its transition system, a permutation of the strand
ends, together with its cost.  Its components are the cycles of that permutation,
so the component count is `OrbitCount.orbitCount`.

`nogap_realisation` is `thm:nogap` for this model: if from every cost-minimal
realisation with at least two components there is a free merge, meaning two ends in
different cycles whose swap is again cost-minimal, then some cost-minimal
realisation has a single component, that is `c = 0`.

The free-merge hypothesis is what `NoGapMerge` (a swap is free exactly when a side
is shared, and a bounce never blocks) together with `SharedSite` (a shared site
always exists) establish for a gap-free element.  Those are verified; what this
file adds is the passage from them to the component count.
-/
import Mathlib.Tactic
import OrbitCount
import MergeDescent

namespace RealizationModel

open Equiv Equiv.Perm OrbitCount

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A realisation, carried by its transition system and its cost. -/
structure Realisation (α : Type*) [DecidableEq α] [Fintype α] where
  trans : Perm α
  cost : ℤ

/-- Equality of realisations is decidable; taken classically so that no instance
mismatch arises with the permutation type. -/
noncomputable instance : DecidableEq (Realisation α) := Classical.decEq _

/-- The component count of a realisation.

**Correction (2026-08-23).**  An earlier version of this docstring called `trans`
the transition system and `comp` the number of its cycles.  That identification is
wrong and was caught by trying to satisfy the model specification: a component is a
walk, and a walk alternates between crossing an edge and turning at a site, whereas
the transition system only turns.  In the smallest instance, one edge with an up-
and a down-crossing, the cycles of the transition system are the two pairs of top
ends and bottom ends, so the two ends of a single crossing land in different
cycles.

`trans` is therefore to be read as the **walk** permutation, the turn composed with
the strand pairing.  A 2-swap re-pairs at one site, sending the turn `t` to
`swap ∘ t` and hence the walk to `swap ∘ walk`, which is the form `CycleMerge`
proves things about.  So the machinery below targets the right object; only the
name and the reading of `trans` were wrong.

What is still owed is a construction of that walk permutation from a lamp
configuration, together with a proof that its cycles are the components.  That is
recorded here rather than implied to be done. -/
noncomputable def comp (r : Realisation α) : ℕ := orbitCount r.trans

/-- The realisation obtained by a 2-swap at two ends, at unchanged cost. -/
def swapAt (r : Realisation α) (x y : α) : Realisation α :=
  ⟨swap x y * r.trans, r.cost⟩

@[simp] theorem swapAt_cost (r : Realisation α) (x y : α) : (swapAt r x y).cost = r.cost := rfl

/-- A merge across two components strictly lowers the component count. -/
theorem comp_swapAt_lt (r : Realisation α) (x y : α)
    (hxy : ¬ r.trans.SameCycle x y) : comp (swapAt r x y) < comp r :=
  orbitCount_swap_mul_lt' r.trans x y hxy

/-- **`thm:nogap` on the realisation model.**  `T` is the set of cost-minimal
realisations; `hfree` says a free merge exists whenever there are at least two
components.  Then some cost-minimal realisation has one component, i.e. `c = 0`. -/
theorem nogap_realisation (T : Finset (Realisation α)) (hT : T.Nonempty)
    (hpos : ∀ r ∈ T, 1 ≤ comp r)
    (hfree : ∀ r ∈ T, 2 ≤ comp r →
      ∃ x y : α, ¬ r.trans.SameCycle x y ∧ swapAt r x y ∈ T) :
    ∃ r ∈ T, comp r = 1 := by
  refine MergeDescent.min_count_eq_one T hT comp hpos ?_
  intro r hrT hge
  obtain ⟨x, y, hxy, hmem⟩ := hfree r hrT hge
  exact ⟨swapAt r x y, hmem, comp_swapAt_lt r x y hxy⟩

/-- The defect `c` is one less than the component count, so `thm:nogap` reads
`c = 0`. -/
theorem defect_zero (T : Finset (Realisation α)) (hT : T.Nonempty)
    (hpos : ∀ r ∈ T, 1 ≤ comp r)
    (hfree : ∀ r ∈ T, 2 ≤ comp r →
      ∃ x y : α, ¬ r.trans.SameCycle x y ∧ swapAt r x y ∈ T) :
    ∃ r ∈ T, comp r - 1 = 0 := by
  obtain ⟨r, hrT, hr⟩ := nogap_realisation T hT hpos hfree
  exact ⟨r, hrT, by omega⟩

-- Certification (Rule 5).
#print axioms RealizationModel.comp
#print axioms RealizationModel.swapAt
#print axioms RealizationModel.comp_swapAt_lt
#print axioms RealizationModel.nogap_realisation
#print axioms RealizationModel.defect_zero

end RealizationModel
