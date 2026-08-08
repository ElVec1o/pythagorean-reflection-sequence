/-
  MooreCriterion.lean
  ===================
  The finite-state principle at the heart of paper 1's metric lower bound, and its refutation.

  The withdrawn proof of the lower bound rested on:

      "Two finite-state functions of a profile agree on all profiles if and only if they
       agree on every state transition, that is, on a set of profiles that drives A through
       each transition at least once."

  This file does two things.

    * `not_agree_of_transition_cover` exhibits two functions, each computed by a finite-state
      reading of the input, that AGREE on a set of inputs driving the first machine through
      every one of its transitions, and yet DIFFER.  So the quoted principle is false, and
      the lower bound does not follow from the depth-24 enumeration by that route.

    * `agree_of_same_machine` proves the principle that IS true and that the argument would
      have needed: if two output functions are read off the SAME state machine, and agree at
      every state reachable from the start, then the induced functions agree on all inputs.
      The gap between the two is exactly the gap in the paper: the true defect was never shown
      to be computed by the same machine as the closed form, and the earlier proof of that
      assumed the conclusion.

  Nothing here formalises the metric theorem.  What is formalised is why one route to it fails.
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum

namespace MooreCriterion

/-! ### A machine is a state, a step, and an output -/

/-- Run a step function over an input list, from a start state. -/
def run {S A : Type} (step : S → A → S) (s0 : S) : List A → S :=
  List.foldl step s0

/-- The function a machine computes: run, then read the output at the final state. -/
def eval {S A O : Type} (step : S → A → S) (s0 : S) (out : S → O) (l : List A) : O :=
  out (run step s0 l)

/-! ### The principle that is true: one machine, two output maps -/

/-- A state is reachable if some input drives the machine to it. -/
def Reachable {S A : Type} (step : S → A → S) (s0 : S) (s : S) : Prop :=
  ∃ l : List A, run step s0 l = s

theorem reachable_start {S A : Type} (step : S → A → S) (s0 : S) :
    Reachable step s0 s0 := ⟨[], rfl⟩

/-- **The valid principle.**  Two readings of the *same* machine that agree at every
    reachable state agree on every input.  This is what the withdrawn argument needed, and it
    requires the two functions to share a machine, not merely to be finite-state each. -/
theorem agree_of_same_machine {S A O : Type} (step : S → A → S) (s0 : S) (out1 out2 : S → O)
    (h : ∀ s, Reachable step s0 s → out1 s = out2 s) :
    ∀ l : List A, eval step s0 out1 l = eval step s0 out2 l := by
  intro l
  exact h (run step s0 l) ⟨l, rfl⟩

/-! ### The principle that is false: two machines, a transition-covering set for one

    Machine `A` has a single state and therefore exactly two transitions, one per letter.
    The two singleton inputs drive it through both.  Machine `B` counts length modulo three.
    They agree on the empty input and on both singletons, hence on a set covering every
    transition of `A`, and they differ at length two. -/

/-- Machine `A`: one state, output always `0`. -/
def stepA : Unit → Bool → Unit := fun _ _ => ()
def outA : Unit → ℕ := fun _ => 0
def fA : List Bool → ℕ := eval stepA () outA

/-- Machine `B`: three states, counting length modulo three; outputs `1` exactly at state 2. -/
def stepB : Fin 3 → Bool → Fin 3 := fun s _ => s + 1
def outB : Fin 3 → ℕ := fun s => if s = 2 then 1 else 0
def fB : List Bool → ℕ := eval stepB 0 outB

/-- Every input drives `A` through the only transitions it has, so `{[], [true], [false]}`
    is a transition-covering set for `A`. -/
theorem A_transitions_covered :
    (∀ b : Bool, stepA () b = ()) ∧ ([([] : List Bool), [true], [false]]).length = 3 := by
  refine ⟨fun b => rfl, rfl⟩

/-- On that covering set the two machines agree. -/
theorem agree_on_cover :
    fA [] = fB [] ∧ fA [true] = fB [true] ∧ fA [false] = fB [false] := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The refutation.**  They differ at length two, so agreement on a set covering every
    transition of the first machine does not imply agreement everywhere. -/
theorem not_agree_of_transition_cover :
    (fA [] = fB [] ∧ fA [true] = fB [true] ∧ fA [false] = fB [false])
      ∧ fA [true, true] ≠ fB [true, true] := by
  refine ⟨agree_on_cover, by decide⟩

/-- Moore's bound is consistent with this: with `1 + 3 = 4` states in total one must test all
    inputs of length `< 4`, and the distinguishing input has length `2 < 4`.  The failure is
    of the quoted principle, not of Moore's. -/
theorem moore_bound_consistent : ([true, true].length) < 1 + 3 := by decide

end MooreCriterion
