/-
The component count, and its strict drop under a merging swap.

`orbitCount π` is the number of cycles of `π`, defined as the cardinality of the
quotient of the point set by `SameCycle`.  This is the `comp` that `MergeDescent`
takes as its measure.

The drop argument is packaged in two halves.  `card_lt_of_surjective_not_injective`
is general and has nothing to do with permutations: a surjection between finite
types that is not injective strictly lowers the cardinality.  The permutation half
supplies the surjection, induced by the identity on points, and the failure of
injectivity, which is exactly the merge lemma of `CycleMerge`.
-/
import Mathlib.Tactic
import CycleMerge

namespace OrbitCount

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α]

/-- A surjection between finite types that is not injective strictly lowers the
cardinality.  This is the counting step of the merge. -/
theorem card_lt_of_surjective_not_injective {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hs : Function.Surjective f) (hni : ¬ Function.Injective f) :
    Fintype.card B < Fintype.card A := by
  rcases lt_or_ge (Fintype.card B) (Fintype.card A) with h | h
  · exact h
  · exfalso
    have hle : Fintype.card B ≤ Fintype.card A := Fintype.card_le_of_surjective f hs
    have heq : Fintype.card A = Fintype.card B := le_antisymm h hle
    exact hni ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hs, heq⟩).1

/-- `SameCycle` as a setoid, so the cycles are the classes of a quotient. -/
def sameCycleSetoid (π : Perm α) : Setoid α where
  r := π.SameCycle
  iseqv := ⟨fun z => SameCycle.refl π z, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The number of cycles of `π`. -/
noncomputable def orbitCount [Fintype α] (π : Perm α) : ℕ :=
  Nat.card (Quotient (sameCycleSetoid π))

/-- Every point of `x`'s cycle joins `x` in the merged permutation.  This is the
half of well-definedness that the merged orbit needs; the untouched orbits are
handled by `CycleMerge.sameCycle_swap_mul_of_off_orbits`. -/
theorem sameCycle_of_mem_orbit (π : Perm α) (x y : α) (k : ℕ)
    (hk : ∀ i, 0 < i → i < k → (π ^ i) x ≠ x)
    (hy : ∀ i : ℕ, (π ^ i) x ≠ y)
    (i : ℕ) (hik : i < k) :
    (swap x y * π).SameCycle x ((π ^ i) x) :=
  ⟨(i : ℤ), by
    simpa [zpow_natCast] using CycleMerge.pow_apply_eq_of_lt π x y k hk hy i hik⟩

-- Certification (Rule 5).
#print axioms OrbitCount.card_lt_of_surjective_not_injective
#print axioms OrbitCount.sameCycleSetoid
#print axioms OrbitCount.orbitCount
#print axioms OrbitCount.sameCycle_of_mem_orbit

end OrbitCount
