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

/-- **From a shared site to the pair the merge needs.**

Let `u` and `v` be arrivals whose pairs lie in different components, with `u`
opening a bounce.  Taking the departures `x = π u` and `y = π v`, every clause of
`hpair` holds: the pre-images are `u` and `v`, which are arrivals and distinct, and
the shared side comes from `NoGapMerge.shared_side_of_bounce`, whose two
alternatives are exactly the two the merge accepts.

The minimality hypothesis is the same one used throughout: at a cost minimum no
2-swap is strictly negative. -/
theorem hpair_of_bounce {β : Type*} [DecidableEq β] (d : Data β) (π : Perm β) (u v : β)
    (harru : d.isArr u = true) (harrv : d.isArr v = true)
    (hdepu : d.isArr (π u) = false) (hdepv : d.isArr (π v) = false)
    (huv : u ≠ v)
    (hbounce : d.side u = d.side (π u))
    (hmin : 0 ≤ NoGapMerge.swapDelta (d.side u) (d.side (π u)) (d.side v) (d.side (π v)))
    (hcyc : ¬ π.SameCycle (π u) (π v)) :
    d.isArr (π u) = false ∧ d.isArr (π v) = false ∧
    d.isArr (π.symm (π u)) = true ∧ d.isArr (π.symm (π v)) = true ∧
    π.symm (π u) ≠ π.symm (π v) ∧
    (d.side (π.symm (π u)) = d.side (π.symm (π v)) ∨ d.side (π u) = d.side (π v)) ∧
    ¬ π.SameCycle (π u) (π v) := by
  have hu : π.symm (π u) = u := Equiv.symm_apply_apply π u
  have hv : π.symm (π v) = v := Equiv.symm_apply_apply π v
  refine ⟨hdepu, hdepv, by rw [hu]; exact harru, by rw [hv]; exact harrv,
          by rw [hu, hv]; exact huv, ?_, hcyc⟩
  rw [hu, hv]
  -- the bounce puts `swapDelta` in the shape `shared_side_of_bounce` expects
  have hshape : NoGapMerge.swapDelta (d.side u) (d.side u) (d.side v) (d.side (π v))
      = NoGapMerge.swapDelta (d.side u) (d.side (π u)) (d.side v) (d.side (π v)) := by
    rw [hbounce]
  have hmin' : 0 ≤ NoGapMerge.swapDelta (d.side u) (d.side u) (d.side v) (d.side (π v)) := by
    rw [hshape]; exact hmin
  rcases NoGapMerge.shared_side_of_bounce (d.side u) (d.side v) (d.side (π v)) hmin' with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [← hbounce]; exact h)

-- Certification (Rule 5).
#print axioms NoGapCapstone.merge_free_and_lowers
#print axioms NoGapCapstone.nogap
#print axioms NoGapCapstone.hpair_of_bounce

end NoGapCapstone
