/-
Cost across the merge.

`EndData.transCost` sums `pcostF a (π a)` over *arrivals only*.  The re-pairing
changes the turn at the two arrivals `a, a'` and at the two departures `d, d'`, so
only the arrival terms are visible to the cost.

On arrivals the re-paired turn agrees with `swap d d' ∘ t`: both send `a ↦ d'` and
`a' ↦ d`, and away from the four ends neither moves anything, since `t x ∈ {d, d'}`
forces `x ∈ {a, a'}`.  They differ only at `d` and `d'` themselves, which are
departures.  So `EndData.transCost_swap_free` applies to the involutive re-pairing
even though `swapT ≠ swap ∘ t` as functions.
-/
import Mathlib.Tactic
import EndData
import WalkGraph

namespace CostMerge

open WalkGraph

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The turn of a walk-graph datum as a permutation; it is its own inverse. -/
def turnPerm (D : Data α) : Equiv.Perm α :=
  ⟨D.t, D.t, fun x => D.t_invol x, fun x => D.t_invol x⟩

omit [Fintype α] [DecidableEq α] in
@[simp] theorem turnPerm_apply (D : Data α) (x : α) : turnPerm D x = D.t x := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem turnPerm_symm (D : Data α) (x : α) : (turnPerm D).symm x = D.t x := rfl

/-- The cost of a walk-graph datum against end data. -/
noncomputable def costOf (d : EndData.Data α) (D : Data α) : ℤ :=
  EndData.transCost d (turnPerm D)

omit [DecidableEq α] in
/-- **The cost sees only the turn's values at arrivals.** -/
theorem cost_congr (d : EndData.Data α) (D₁ D₂ : Data α)
    (h : ∀ a, d.isArr a = true → D₁.t a = D₂.t a) :
    costOf d D₁ = costOf d D₂ := by
  unfold costOf EndData.transCost
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_filter] at ha
  rw [turnPerm_apply, turnPerm_apply, h a ha.2]

omit [Fintype α] in
/-- **On arrivals, the re-paired turn is the transposition of the two departures.**
Away from the four ends nothing moves, because `t x ∈ {d, d'}` forces `x ∈ {a, a'}`. -/
theorem swapT_eq_on_arr (d : EndData.Data α) (t : α → α) (a a' : α)
    (hinv : ∀ x, t (t x) = x)
    (hd : d.isArr (t a) = false) (hd' : d.isArr (t a') = false)
    (x : α) (hx : d.isArr x = true) :
    swapT t a (t a) a' (t a') x = Equiv.swap (t a) (t a') (t x) := by
  have hxd : x ≠ t a := fun h => by rw [h, hd] at hx; exact Bool.noConfusion hx
  have hxd' : x ≠ t a' := fun h => by rw [h, hd'] at hx; exact Bool.noConfusion hx
  unfold swapT
  by_cases h1 : x = a
  · subst h1; rw [if_pos rfl, Equiv.swap_apply_left]
  by_cases h3 : x = a'
  · subst h3
    rw [if_neg h1, if_neg hxd', if_pos rfl, Equiv.swap_apply_right]
  rw [if_neg h1, if_neg hxd', if_neg h3, if_neg hxd]
  refine (Equiv.swap_apply_of_ne_of_ne ?_ ?_).symm
  · intro hc; exact h1 (by rw [← hinv x, hc, hinv])
  · intro hc; exact h3 (by rw [← hinv x, hc, hinv])

/-- **The merge is cost-neutral.**  The re-pairing of two arrivals sharing a side --
or whose departures share one -- leaves the transition cost unchanged.

This is `EndData.transCost_swap_free` transported along `swapT_eq_on_arr`: the cost
cannot tell the involutive re-pairing from the transposition of the two departures,
because they differ only at departures. -/
theorem cost_swapData (d : EndData.Data α) (D : Data α) (a a' : α)
    (harr : d.isArr a = true) (harr' : d.isArr a' = true)
    (hd : d.isArr (D.t a) = false) (hd' : d.isArr (D.t a') = false)
    (hne : a ≠ a')
    (hshared : d.side a = d.side a' ∨ d.side (D.t a) = d.side (D.t a'))
    (h1 h2 h3) :
    costOf d (swapData D a (D.t a) a' (D.t a') h1 h2 h3) = costOf d D := by
  have hsa : (turnPerm D).symm (D.t a) = a := by
    rw [turnPerm_symm, D.t_invol]
  have hsa' : (turnPerm D).symm (D.t a') = a' := by
    rw [turnPerm_symm, D.t_invol]
  have key : costOf d (swapData D a (D.t a) a' (D.t a') h1 h2 h3)
      = EndData.transCost d (Equiv.swap (D.t a) (D.t a') * turnPerm D) := by
    unfold costOf EndData.transCost
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_filter] at hx
    show EndData.pcostF d x (swapT D.t a (D.t a) a' (D.t a') x) = _
    rw [swapT_eq_on_arr d D.t a a' D.t_invol hd hd' x hx.2]
    rfl
  rw [key]
  exact EndData.transCost_swap_free d (turnPerm D) (D.t a) (D.t a') hd hd'
    (by rw [hsa]; exact harr) (by rw [hsa']; exact harr')
    (by rw [hsa, hsa']; exact hne)
    (by rw [hsa, hsa']; exact hshared)

-- Certification (Rule 5).
#print axioms CostMerge.cost_swapData
