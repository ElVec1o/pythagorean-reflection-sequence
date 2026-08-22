/-
Non-vacuity witness for `EndData`.

A previous version of `EndData` carried a hypothesis that was contradictory, so
every theorem using it held vacuously.  This file exhibits a concrete `Data` with
an arrival and a departure, so the hypotheses of `pcost_eq_of_arr_dep` are
satisfiable and the theorem has content.  It also computes both branches of the
conclusion, a bounce and a pass.
-/
import EndData

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

-- Certification (Rule 5).
#print axioms NonVacuity.bounce_cost
#print axioms NonVacuity.pass_cost
#print axioms NonVacuity.not_vacuous
#print axioms NonVacuity.sign_differs

end NonVacuity
