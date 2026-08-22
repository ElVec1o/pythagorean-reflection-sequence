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

What remains between this and a self-contained formalisation of `thm:nogap` is the
model itself: a definition of realisations, of the component count as the number of
cycles of the transition permutation, and the derivation of `merges` from
`CycleMerge` together with the swap criterion and the shared-site argument. The
mathematical inputs are all verified; the bookkeeping that ties them to a concrete
`R` is not written. `nogap_of_merge` is therefore a conditional theorem and the
condition is named.
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
