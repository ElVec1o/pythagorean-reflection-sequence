/-
`thm:nogap` assembled from its verified inputs, with the single missing ingredient
isolated as a named hypothesis.

The proof of `thm:nogap` has four inputs.  Three are verified here:

* `NoGapMerge.swap_free_iff` / `bounce_never_blocks` -- when a 2-swap is free;
* `SharedSite.shared_site_exists`                    -- a shared site always exists;
* `MergeDescent.min_count_eq_one`                    -- descent on the component count.

The fourth is the classical fact that a transposition applied to a transition
system whose two moved ends lie in *different* components merges those components.
Mathlib does not have it -- `Perm/Cycle/Basic`, `Perm/Cycle/Type` and `Perm/Sign`
carry only special cases (`IsCycle.swap_mul`, `cycleType_swap_mul_swap_of_nodup`) --
so it is proved in `CycleMerge.lean` as `sameCycle_of_not_sameCycle`.

**CORRECTION (2026-08-23).**  This header previously said that what remained was to
define the component count *as the number of cycles of the transition permutation*,
and that the missing input was the effect of a **transposition** on a transition
system.  Both readings are wrong, and neither is a small slip:

* Cycles of the walk permutation `sig = t ∘ p` number **twice** the components,
  because `p` carries each `sig`-orbit to a different one.  That is now proved,
  `ConfigMerge.p_not_in_orbit`, so the identification is refuted, not merely
  unverified.
* The re-pairing is a **double** transposition: with `d = t a`, `d' = t a'`, the new
  turn is `WalkGraph.swapT` and `swapT = (a a')(d d') ∘ t`.  A single transposition
  cannot do it, since `swap ∘ t` is not an involution while the turn must stay one.
  See the correction in `RealizationModel.lean`.

`CycleMerge.sameCycle_of_not_sameCycle` and the theorems below remain TRUE; what was
wrong is only the claim about what they model.

`thm:nogap` is instead formalised over graph components, with the involutive
re-pairing, in `ConfigMerge` -> `WalkSupport` -> `ConfigLoop`, ending at
`ConfigLoop.gapfree_merges_to_one`, which is exhibited on a real configuration by
`ConfigLoop.one_edge_merges`.  `nogap_of_merge` below stays as a conditional theorem
about the cycle model.
-/
import MergeDescent
import NoGapMerge
import SharedSite

namespace NoGapTheorem

open MergeDescent

/-- `thm:nogap` in the form the descent gives it: if from every cost-minimal
realisation with at least two components one can produce a cost-minimal realisation
with fewer, then some cost-minimal realisation has exactly one component, i.e.
`c = 0`.

`T` is the set of cost-minimal realisations, `comp` the component count. The
hypothesis `merges` is what the swap criterion plus the shared-site argument supply
once the cycle-merge fact above is available. -/
theorem nogap_of_merge {R : Type*} [DecidableEq R]
    (T : Finset R) (hT : T.Nonempty) (comp : R → ℕ)
    (hpos : ∀ r ∈ T, 1 ≤ comp r)
    (merges : ∀ r ∈ T, 2 ≤ comp r → ∃ r' ∈ T, comp r' < comp r) :
    ∃ r ∈ T, comp r = 1 :=
  min_count_eq_one T hT comp hpos merges

/-- The component count of a cost-minimal realisation, restated as the defect
`c = comp - 1`.  `thm:nogap` is the statement that this is `0`. -/
def defect (comp : ℕ) : ℕ := comp - 1

theorem defect_eq_zero_of_comp_eq_one {comp : ℕ} (h : comp = 1) : defect comp = 0 := by
  simp [defect, h]

/-- Assembled form: under the merge hypothesis, some cost-minimal realisation has
defect zero. -/
theorem defect_zero_of_merge {R : Type*} [DecidableEq R]
    (T : Finset R) (hT : T.Nonempty) (comp : R → ℕ)
    (hpos : ∀ r ∈ T, 1 ≤ comp r)
    (merges : ∀ r ∈ T, 2 ≤ comp r → ∃ r' ∈ T, comp r' < comp r) :
    ∃ r ∈ T, defect (comp r) = 0 := by
  obtain ⟨r, hrT, hr⟩ := nogap_of_merge T hT comp hpos merges
  exact ⟨r, hrT, defect_eq_zero_of_comp_eq_one hr⟩

-- Certification (Rule 5): every declaration above, axioms listed in the build log.
#print axioms NoGapTheorem.nogap_of_merge
#print axioms NoGapTheorem.defect_eq_zero_of_comp_eq_one
#print axioms NoGapTheorem.defect_zero_of_merge

end NoGapTheorem
