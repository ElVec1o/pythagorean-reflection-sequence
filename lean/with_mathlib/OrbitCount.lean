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

/-- The orbit map `n ↦ π^n x` is periodic once `π^k x = x`. -/
theorem pow_apply_mod {β : Type*} (π : Perm β) (x : β) (k : ℕ) (hkpos : 0 < k) (hk : (π ^ k) x = x) :
    ∀ n : ℕ, (π ^ n) x = (π ^ (n % k)) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n k with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have hnk : n - k < n := by omega
      have hsplit : (π ^ n) x = (π ^ (n - k)) x := by
        have : n = (n - k) + k := by omega
        rw [this, pow_add]
        simp [Perm.mul_apply, hk]
      rw [hsplit, ih (n - k) hnk]
      congr 1
      have hmod : n % k = (n - k) % k := by
        conv_lhs => rw [show n = (n - k) + k by omega]
        rw [Nat.add_mod_right]
      rw [hmod]

/-- Every point of `x`'s cycle is on `x`'s cycle after the merge. -/
theorem sameCycle_swap_mul_left [Fintype α] (π : Perm α) (x y z : α) (k : ℕ) (hkpos : 0 < k)
    (hkx : (π ^ k) x = x)
    (hk : ∀ i, 0 < i → i < k → (π ^ i) x ≠ x)
    (hy : ∀ i : ℕ, (π ^ i) x ≠ y)
    (hz : π.SameCycle x z) :
    (swap x y * π).SameCycle x z := by
  obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
  have hmod : (π ^ n) x = (π ^ (n % k)) x := pow_apply_mod π x k hkpos hkx n
  have hlt : n % k < k := Nat.mod_lt _ hkpos
  refine ⟨((n % k : ℕ) : ℤ), ?_⟩
  have hstep := CycleMerge.pow_apply_eq_of_lt π x y k hk hy (n % k) hlt
  rw [zpow_natCast, hstep, ← hmod, hn]

-- Certification (Rule 5).
#print axioms OrbitCount.card_lt_of_surjective_not_injective
#print axioms OrbitCount.sameCycleSetoid
#print axioms OrbitCount.orbitCount
#print axioms OrbitCount.sameCycle_of_mem_orbit
#print axioms OrbitCount.pow_apply_mod
#print axioms OrbitCount.sameCycle_swap_mul_left

end OrbitCount
