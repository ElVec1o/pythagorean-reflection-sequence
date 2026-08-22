/-
A transposition merges two cycles.

Mathlib carries only special cases (`IsCycle.swap_mul`,
`cycleType_swap_mul_swap_of_nodup`), so the general statement is proved here.

If `x` and `y` lie in different cycles of `π`, then they lie in the same cycle of
`swap x y * π`.  This is the fact `thm:nogap` needs: a 2-swap across two components
merges them.

Proof.  Let `k > 0` be least with `π^k x = x`.  For `0 < i < k` the point `π^i x`
is neither `x` (minimality) nor `y` (different cycles), so the swap acts trivially
along the orbit and `σ^i x = π^i x`.  At the last step `σ^k x = swap x y (π^k x)
= swap x y x = y`.
-/
import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Cycle.Basic

namespace CycleMerge

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Along the orbit of `x`, before returning to `x`, the swap acts trivially. -/
theorem pow_apply_eq_of_lt (π : Perm α) (x y : α) (k : ℕ)
    (hk : ∀ i, 0 < i → i < k → (π ^ i) x ≠ x)
    (hy : ∀ i : ℕ, (π ^ i) x ≠ y) :
    ∀ i, i < k → ((swap x y * π) ^ i) x = (π ^ i) x := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnk : n < k := Nat.lt_of_succ_lt hn
    have hstep := ih hnk
    have hcomp : ((swap x y * π) ^ (n + 1)) x = swap x y (π ((π ^ n) x)) := by
      rw [pow_succ']
      simp [Perm.mul_apply, hstep]
    rw [hcomp]
    have h1 : π ((π ^ n) x) = (π ^ (n + 1)) x := by
      rw [pow_succ']; simp [Perm.mul_apply]
    rw [h1]
    -- `π^(n+1) x` is neither `x` nor `y`, so the swap fixes it
    have hne_x : (π ^ (n + 1)) x ≠ x := hk (n + 1) (Nat.succ_pos n) hn
    have hne_y : (π ^ (n + 1)) x ≠ y := hy (n + 1)
    exact swap_apply_of_ne_of_ne hne_x hne_y

/-- The merge: different cycles of `π` become one cycle of `swap x y * π`. -/
theorem sameCycle_swap_mul (π : Perm α) (x y : α) (k : ℕ) (hkpos : 0 < k)
    (hkx : (π ^ k) x = x)
    (hk : ∀ i, 0 < i → i < k → (π ^ i) x ≠ x)
    (hy : ∀ i : ℕ, (π ^ i) x ≠ y) :
    ((swap x y * π) ^ k) x = y := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hstep := pow_apply_eq_of_lt π x y (m + 1) hk hy m (Nat.lt_succ_self m)
  have hcomp : ((swap x y * π) ^ (m + 1)) x = swap x y (π ((π ^ m) x)) := by
    rw [pow_succ']
    simp [Perm.mul_apply, hstep]
  rw [hcomp]
  have h1 : π ((π ^ m) x) = (π ^ (m + 1)) x := by
    rw [pow_succ']; simp [Perm.mul_apply]
  rw [h1, hkx, swap_apply_left]

/-- Points in different cycles of `π` are in the same cycle of `swap x y * π`.
This is the usable form: the hypothesis is `¬ π.SameCycle x y` and the cycle length
is produced internally. -/
theorem sameCycle_of_not_sameCycle (π : Perm α) (x y : α) (h : ¬ π.SameCycle x y) :
    (swap x y * π).SameCycle x y := by
  classical
  -- `y` is off the forward orbit of `x`
  have hy : ∀ i : ℕ, (π ^ i) x ≠ y := by
    intro i hi
    exact h ⟨(i : ℤ), by simpa [zpow_natCast] using hi⟩
  -- the forward orbit returns to `x`
  have hex : ∃ n : ℕ, 0 < n ∧ (π ^ n) x = x := by
    refine ⟨orderOf π, ?_, ?_⟩
    · exact orderOf_pos π
    · rw [pow_orderOf_eq_one]; rfl
  classical
  let k := Nat.find (by exact ⟨orderOf π, orderOf_pos π, by rw [pow_orderOf_eq_one]; rfl⟩ :
    ∃ n : ℕ, 0 < n ∧ (π ^ n) x = x)
  have hkspec := Nat.find_spec (by
    exact ⟨orderOf π, orderOf_pos π, by rw [pow_orderOf_eq_one]; rfl⟩ :
      ∃ n : ℕ, 0 < n ∧ (π ^ n) x = x)
  have hkpos : 0 < k := hkspec.1
  have hkx : (π ^ k) x = x := hkspec.2
  have hkmin : ∀ i, 0 < i → i < k → (π ^ i) x ≠ x := by
    intro i hipos hik hcon
    exact absurd ⟨hipos, hcon⟩ (Nat.find_min _ hik)
  exact ⟨(k : ℤ), by simpa [zpow_natCast] using sameCycle_swap_mul π x y k hkpos hkx hkmin hy⟩

-- Certification (Rule 5).
#print axioms CycleMerge.pow_apply_eq_of_lt
#print axioms CycleMerge.sameCycle_swap_mul
#print axioms CycleMerge.sameCycle_of_not_sameCycle

end CycleMerge
