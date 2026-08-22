/-
`thm:nogap` with the free-merge hypothesis discharged.

`RealizationModel.nogap_realisation` assumed that a cost-minimal realisation with
at least two components admits a free merge.  Here that assumption is replaced by
its two halves, both proved:

* `EndData.transCost_swap_free` -- a swap sharing a side does not change the cost,
  so the swapped realisation is still cost-minimal;
* `OrbitCount.orbitCount_swap_mul_lt'` -- a swap across two components lowers the
  component count.

What remains an input is the existence of the swap itself, which for a gap-free
element is `SharedSite.shared_site_exists` together with the forced-pass lemma.
That is stated as `hpair` and is the last thing tying the model to the group.
-/
import Mathlib.Tactic
import EndData
import OrbitCount
import MergeDescent

namespace NoGapCapstone

open Equiv Equiv.Perm EndData OrbitCount

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A swap sharing a side, across two components, is free **and** lowers the
component count.  Both halves are proved; this is their conjunction. -/
theorem merge_free_and_lowers (d : Data α) (π : Perm α) (x y : α)
    (hxdep : d.isArr x = false) (hydep : d.isArr y = false)
    (hxarr : d.isArr (π.symm x) = true) (hyarr : d.isArr (π.symm y) = true)
    (hne : π.symm x ≠ π.symm y)
    (hshared : d.side (π.symm x) = d.side (π.symm y) ∨ d.side x = d.side y)
    (hcyc : ¬ π.SameCycle x y) :
    transCost d (swap x y * π) = transCost d π ∧
      orbitCount (swap x y * π) < orbitCount π :=
  ⟨transCost_swap_free d π x y hxdep hydep hxarr hyarr hne hshared,
   orbitCount_swap_mul_lt' π x y hcyc⟩

/-- **`thm:nogap`, with the free merge discharged.**  `T` is a set of transition
systems closed under cost-preserving swaps; `hpair` provides, at any element of `T`
with at least two components, a pair of ends in different cycles whose swap shares
a side.  The conclusion is that some element of `T` has a single component, that is
`c = 0`. -/
theorem nogap (d : Data α) (T : Finset (Perm α)) (hT : T.Nonempty)
    (hclosed : ∀ π ∈ T, ∀ x y : α,
      transCost d (swap x y * π) = transCost d π → swap x y * π ∈ T)
    (hpos : ∀ π ∈ T, 1 ≤ orbitCount π)
    (hpair : ∀ π ∈ T, 2 ≤ orbitCount π → ∃ x y : α,
      d.isArr x = false ∧ d.isArr y = false ∧
      d.isArr (π.symm x) = true ∧ d.isArr (π.symm y) = true ∧
      π.symm x ≠ π.symm y ∧
      (d.side (π.symm x) = d.side (π.symm y) ∨ d.side x = d.side y) ∧
      ¬ π.SameCycle x y) :
    ∃ π ∈ T, orbitCount π = 1 := by
  classical
  refine MergeDescent.min_count_eq_one T hT orbitCount hpos ?_
  intro π hπT hge
  obtain ⟨x, y, hxd, hyd, hxa, hya, hne, hsh, hcyc⟩ := hpair π hπT hge
  obtain ⟨hcost, hlt⟩ :=
    merge_free_and_lowers d π x y hxd hyd hxa hya hne hsh hcyc
  exact ⟨swap x y * π, hclosed π hπT x y hcost, hlt⟩

-- Certification (Rule 5).
#print axioms NoGapCapstone.merge_free_and_lowers
#print axioms NoGapCapstone.nogap

end NoGapCapstone
