/-
Non-vacuity witness for `EndData`.

A previous version of `EndData` carried a hypothesis that was contradictory, so
every theorem using it held vacuously.  This file exhibits a concrete `Data` with
an arrival and a departure, so the hypotheses of `pcost_eq_of_arr_dep` are
satisfiable and the theorem has content.  It also computes both branches of the
conclusion, a bounce and a pass.
-/
import EndData
import NoGapCapstone

namespace NonVacuity

open EndData

/-- Four ends: `0` and `1` on the left, `2` and `3` on the right; the even ones are
arrivals. -/
def d4 : Data (Fin 4) where
  side := fun a => decide (2 ≤ a.val)
  isArr := fun a => decide (a.val % 2 = 0)
  depSign := fun _ => true

theorem arr0 : d4.isArr 0 = true := by decide
theorem dep1 : d4.isArr 1 = false := by decide
theorem dep3 : d4.isArr 3 = false := by decide

/-- Same side: the pair costs `2`, a bounce with opposite signs. -/
theorem bounce_cost : pcostF d4 0 1 = 2 := by decide

/-- Opposite sides: the pair costs `1`, a pass. -/
theorem pass_cost : pcostF d4 0 3 = 1 := by decide

/-- The hypotheses of `pcost_eq_of_arr_dep` are satisfiable, and it agrees with the
computed values, so the theorem is not vacuous. -/
theorem not_vacuous :
    pcostF d4 0 1 = (if d4.side 0 = d4.side 1 then 2 else 1) ∧
    pcostF d4 0 3 = (if d4.side 0 = d4.side 3 then 2 else 1) :=
  ⟨pcost_eq_of_arr_dep d4 0 1 arr0 dep1, pcost_eq_of_arr_dep d4 0 3 arr0 dep3⟩

/-- And the sign really is non-degenerate: an arrival and a departure on the same
side differ, which is what the old contradictory hypothesis was trying to say. -/
theorem sign_differs : sgn d4 0 ≠ sgn d4 1 := by decide

/-- A witness for `transCost_swap_free`: four ends, `0` and `2` arrivals, `1` and
`3` departures, sides `L, L, L, R`.  The permutation pairs `0` with `1` and `2`
with `3`.  Swapping the departures `1` and `3` shares the arrival side, so the cost
must be unchanged, and it is: `2 + 1` before and `1 + 2` after. -/
def dW : Data (Fin 4) where
  side := fun a => decide (a.val = 3)
  isArr := fun a => decide (a.val % 2 = 0)
  depSign := fun _ => true

/-- The pairing: `0 ↔ 1` and `2 ↔ 3`. -/
def piW : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem w_arr0 : dW.isArr (piW.symm 1) = true := by decide
theorem w_arr2 : dW.isArr (piW.symm 3) = true := by decide
theorem w_dep1 : dW.isArr 1 = false := by decide
theorem w_dep3 : dW.isArr 3 = false := by decide
theorem w_ne : piW.symm 1 ≠ piW.symm 3 := by decide
theorem w_shared : dW.side (piW.symm 1) = dW.side (piW.symm 3) ∨ dW.side 1 = dW.side 3 := by decide

/-- Every hypothesis of `transCost_swap_free` is met here, so it is not vacuous. -/
theorem swap_free_not_vacuous :
    transCost dW (Equiv.swap 1 3 * piW) = transCost dW piW :=
  transCost_swap_free dW piW 1 3 w_dep1 w_dep3 w_arr0 w_arr2 w_ne w_shared

/-- And the common value is genuinely non-zero, so the statement is not trivially
`0 = 0`. -/
theorem swap_free_value : transCost dW piW = 3 := by decide

/-- `1` and `3` lie in different cycles of the witness pairing: its cycles are
`{0,1}` and `{2,3}`.  The pairing is an involution, so `pow_apply_mod` with period
`2` reduces every power to one of two, neither of which sends `1` to `3`. -/
theorem w_not_sameCycle : ¬ piW.SameCycle 1 3 := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have h2 : (piW ^ 2) 1 = 1 := by decide
  have hmod := OrbitCount.pow_apply_mod piW 1 2 (by norm_num) h2 n
  rw [hmod] at hn
  have : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases this with h0 | h1
  · rw [h0] at hn; revert hn; decide
  · rw [h1] at hn; revert hn; decide

/-- Every hypothesis of `merge_free_and_lowers` is met by the witness, so it is not
vacuous: the swap is free and the component count really falls. -/
theorem capstone_not_vacuous :
    transCost dW (Equiv.swap 1 3 * piW) = transCost dW piW ∧
      OrbitCount.orbitCount (Equiv.swap 1 3 * piW) < OrbitCount.orbitCount piW :=
  NoGapCapstone.merge_free_and_lowers dW piW 1 3 w_dep1 w_dep3 w_arr0 w_arr2
    w_ne w_shared w_not_sameCycle

-- Certification (Rule 5).
#print axioms NonVacuity.bounce_cost
#print axioms NonVacuity.pass_cost
#print axioms NonVacuity.not_vacuous
#print axioms NonVacuity.sign_differs
#print axioms NonVacuity.swap_free_not_vacuous
#print axioms NonVacuity.swap_free_value
#print axioms NonVacuity.w_not_sameCycle
#print axioms NonVacuity.capstone_not_vacuous

end NonVacuity
