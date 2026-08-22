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

/-- The component count of a realisation: the number of cycles of its transition
system. -/
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
