/-
The cost of a transition system, and the effect of a 2-swap on it.

An end carries a side and is either an arrival or a departure.  Its **sign is not
free**: by `NoGapMerge.split_forced_pos`/`split_forced_neg`, at minimum crossing
multiplicity every up-crossing of an edge carries the sign opposite to its deposit
and every down-crossing carries the deposit's sign.  Left arrivals are up-crossings
of the left edge and left departures its down-crossings, and on the right the roles
exchange.  So the sign is a function of the side, the arrival/departure role, and
the sign of that edge's deposit, and it is *defined* that way here rather than
assumed.

An earlier version of this file instead carried a hypothesis
`∀ a b, side a = side b → sign a ≠ sign b`, which at `a = b` asserts
`sign a ≠ sign a`.  That is contradictory, so every theorem depending on it was
vacuous.  Deriving the sign removes the possibility.

`pcost_eq_of_arr_dep` is the payoff: on an arrival/departure pair the cost sees
only the side pattern, `2` for a bounce and `1` for a pass, which is exactly the
specialisation `NoGapMerge.swap_free_iff` is stated for.
-/
import Mathlib.Tactic
import NoGapMerge

namespace EndData

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Side and role of each end, and the deposit sign carried by each side. -/
structure Data (α : Type*) where
  side : α → Bool
  isArr : α → Bool
  depSign : Bool → Bool

/-- The forced sign of an end.  On the left an arrival is an up-crossing and takes
the opposite of the deposit sign, a departure a down-crossing and takes it; on the
right the two roles exchange. -/
def sgn (d : Data α) (a : α) : Bool :=
  if d.side a then
    (if d.isArr a then d.depSign true else !d.depSign true)
  else
    (if d.isArr a then !d.depSign false else d.depSign false)

/-- The pairing cost: `1` across sides, else `0` or `2` by sign. -/
def pcostF (d : Data α) (a b : α) : ℤ :=
  if d.side a = d.side b then (if sgn d a = sgn d b then 0 else 2) else 1

/-- **On an arrival/departure pair the cost sees only the side pattern.**  This is
not vacuous: it is the consequence of the sign being forced. -/
theorem pcost_eq_of_arr_dep (d : Data α) (a b : α)
    (ha : d.isArr a = true) (hb : d.isArr b = false) :
    pcostF d a b = if d.side a = d.side b then 2 else 1 := by
  unfold pcostF sgn
  by_cases hs : d.side a = d.side b
  · rw [hs]
    simp only [hs, ha, hb, if_true]
    cases hsb : d.side b <;> simp [hsb, ha, hb] <;> cases d.depSign _ <;> simp
  · simp [hs]

/-- Two arrivals on the same side carry the same sign. -/
theorem sgn_eq_of_both_arr (d : Data α) (a b : α)
    (hs : d.side a = d.side b) (ha : d.isArr a = true) (hb : d.isArr b = true) :
    sgn d a = sgn d b := by
  unfold sgn; rw [hs]; simp [ha, hb]

/-- Two departures on the same side carry the same sign. -/
theorem sgn_eq_of_both_dep (d : Data α) (a b : α)
    (hs : d.side a = d.side b) (ha : d.isArr a = false) (hb : d.isArr b = false) :
    sgn d a = sgn d b := by
  unfold sgn; rw [hs]; simp [ha, hb]

/-- The cost of a transition system, summed over the arrivals. -/
def transCost (d : Data α) (π : Perm α) : ℤ :=
  ∑ a ∈ Finset.univ.filter (fun a => d.isArr a = true), pcostF d a (π a)

-- Certification (Rule 5).
#print axioms EndData.sgn
#print axioms EndData.pcostF
#print axioms EndData.pcost_eq_of_arr_dep
#print axioms EndData.sgn_eq_of_both_arr
#print axioms EndData.sgn_eq_of_both_dep
#print axioms EndData.transCost

end EndData
