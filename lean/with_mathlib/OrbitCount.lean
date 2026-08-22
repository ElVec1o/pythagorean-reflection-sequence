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

/-- The cycle classes form a finite type. -/
noncomputable instance quotFintype [Fintype α] (π : Perm α) :
    Fintype (Quotient (sameCycleSetoid π)) :=
  Fintype.ofFinite _

/-- The number of cycles of `π`.  This is the `comp` of `MergeDescent`. -/
noncomputable def orbitCount [Fintype α] (π : Perm α) : ℕ :=
  Fintype.card (Quotient (sameCycleSetoid π))

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

/-- Well-definedness of the induced map on cycle classes: `SameCycle` for `π`
implies `SameCycle` for the merged permutation.  Three cases, each already proved:
the class meets `x`'s orbit, or `y`'s, or neither. -/
theorem sameCycle_mono [Fintype α] (π : Perm α) (x y : α)
    (kx ky : ℕ)
    (hkxpos : 0 < kx) (hkxx : (π ^ kx) x = x)
    (hkxmin : ∀ i, 0 < i → i < kx → (π ^ i) x ≠ x)
    (hyoff : ∀ i : ℕ, (π ^ i) x ≠ y)
    (hkypos : 0 < ky) (hkyy : (π ^ ky) y = y)
    (hkymin : ∀ i, 0 < i → i < ky → (π ^ i) y ≠ y)
    (hxoff : ∀ i : ℕ, (π ^ i) y ≠ x)
    {z w : α} (h : π.SameCycle z w) :
    (swap x y * π).SameCycle z w := by
  classical
  by_cases hzx : π.SameCycle x z
  · -- `z` and `w` both lie on `x`'s cycle
    have hwx : π.SameCycle x w := hzx.trans h
    exact (sameCycle_swap_mul_left π x y z kx hkxpos hkxx hkxmin hyoff hzx).symm.trans
      (sameCycle_swap_mul_left π x y w kx hkxpos hkxx hkxmin hyoff hwx)
  · by_cases hzy : π.SameCycle y z
    · -- `z` and `w` both lie on `y`'s cycle; the construction is symmetric in `x`, `y`
      have hwy : π.SameCycle y w := hzy.trans h
      have hswap : swap x y = swap y x := Equiv.swap_comm x y
      rw [hswap]
      exact (sameCycle_swap_mul_left π y x z ky hkypos hkyy hkymin hxoff hzy).symm.trans
        (sameCycle_swap_mul_left π y x w ky hkypos hkyy hkymin hxoff hwy)
    · -- `z` lies off both orbits, so the two permutations agree along its cycle
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      exact CycleMerge.sameCycle_swap_mul_of_off_orbits π x y z w hzx hzy n hn

/-- The map on cycle classes induced by the identity on points. -/
noncomputable def classMap [Fintype α] (π : Perm α) (x y : α)
    (kx ky : ℕ)
    (hkxpos : 0 < kx) (hkxx : (π ^ kx) x = x)
    (hkxmin : ∀ i, 0 < i → i < kx → (π ^ i) x ≠ x)
    (hyoff : ∀ i : ℕ, (π ^ i) x ≠ y)
    (hkypos : 0 < ky) (hkyy : (π ^ ky) y = y)
    (hkymin : ∀ i, 0 < i → i < ky → (π ^ i) y ≠ y)
    (hxoff : ∀ i : ℕ, (π ^ i) y ≠ x) :
    Quotient (sameCycleSetoid π) → Quotient (sameCycleSetoid (swap x y * π)) :=
  Quotient.map id (fun _ _ h =>
    sameCycle_mono π x y kx ky hkxpos hkxx hkxmin hyoff hkypos hkyy hkymin hxoff h)

/-- **The merge strictly lowers the cycle count.**  This is the hypothesis
`MergeDescent.min_count_eq_one` consumes, and the last piece of `thm:nogap`. -/
theorem orbitCount_swap_mul_lt [Fintype α] (π : Perm α) (x y : α)
    (kx ky : ℕ)
    (hkxpos : 0 < kx) (hkxx : (π ^ kx) x = x)
    (hkxmin : ∀ i, 0 < i → i < kx → (π ^ i) x ≠ x)
    (hyoff : ∀ i : ℕ, (π ^ i) x ≠ y)
    (hkypos : 0 < ky) (hkyy : (π ^ ky) y = y)
    (hkymin : ∀ i, 0 < i → i < ky → (π ^ i) y ≠ y)
    (hxoff : ∀ i : ℕ, (π ^ i) y ≠ x)
    (hxy : ¬ π.SameCycle x y) :
    orbitCount (swap x y * π) < orbitCount π := by
  classical
  set f := classMap π x y kx ky hkxpos hkxx hkxmin hyoff hkypos hkyy hkymin hxoff with hf
  have hsurj : Function.Surjective f := by
    intro b
    induction b using Quotient.inductionOn with
    | _ z => exact ⟨Quotient.mk _ z, rfl⟩
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have hmerged : (swap x y * π).SameCycle x y :=
      CycleMerge.sameCycle_of_not_sameCycle π x y hxy
    have : (Quotient.mk (sameCycleSetoid π) x) = (Quotient.mk (sameCycleSetoid π) y) :=
      hinj (Quotient.sound hmerged)
    exact hxy (Quotient.exact this)
  exact card_lt_of_surjective_not_injective f hsurj hnotinj

-- Certification (Rule 5).
#print axioms OrbitCount.classMap
#print axioms OrbitCount.orbitCount_swap_mul_lt

-- Certification (Rule 5).
#print axioms OrbitCount.card_lt_of_surjective_not_injective
#print axioms OrbitCount.sameCycleSetoid
#print axioms OrbitCount.orbitCount
#print axioms OrbitCount.sameCycle_of_mem_orbit
#print axioms OrbitCount.pow_apply_mod
#print axioms OrbitCount.sameCycle_swap_mul_left
#print axioms OrbitCount.sameCycle_mono

end OrbitCount
