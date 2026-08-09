/-
  PaperExtraMod2.lean
  ===================
  Paper "extra", Proposition `prop:mod2-automaton`: the mod-2 reduction of the growth
  sequence u_d (OEIS A396406) is eventually 3-periodic with pre-period 1, is not purely
  periodic, and satisfies the order-2 Fibonacci recurrence from d = 3 onwards but not at
  d = 2.

  Every assertion below is a statement about the 39 published terms u_0, ..., u_38, so each
  is decidable and is discharged by kernel evaluation.  No `native_decide` is used, hence no
  compiler-evaluation axiom is incurred.  Note that for a `decide`-proved theorem the axiom
  audit legitimately prints an EMPTY list: kernel evaluation appeals to no axiom at all.  The
  certificate for this file is therefore that it compiles with zero errors and that no
  constant depends on `sorryAx`.

  SCOPE.  The proposition's closing sentence, that U(t) in F_2[[t]] is therefore algebraic
  over F_2(t) via a 4-state automaton, is NOT formalised here.  That step is the standard
  equivalence "eventually periodic implies rational implies algebraic" for power series over
  a finite field; it needs the formal power series machinery and is not a statement about the
  39 terms.  What is formalised is the eventual periodicity that feeds it, which is the part
  the paper establishes by computation.

  This file also discharges the mod-2 half of `prop:no-recurrence-strong` (iii), which
  restates the same two facts about the Fibonacci recurrence at d >= 3 and its failure at
  d = 2.

  Core Lean 4 only, no Mathlib.
-/

namespace PaperExtraMod2

/-- The first 39 terms of A396406, indexed `u_0, ..., u_38` (offset 0). -/
def uList : List Nat :=
  [1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066,
   3203, 4971, 7574, 11543, 17683, 27108, 41067, 62263, 94622, 143881,
   217101, 327832, 495443, 749195, 1127236, 1697179, 2554961, 3848384,
   5777651, 8679441, 13031206, 19574659, 29338781]

/-- `u n` is the `n`-th published term; out of range it is `0`, and every statement below
    is explicitly guarded by `n < 39` so the padding is never consulted. -/
def u (n : Nat) : Nat := uList.getD n 0

theorem uList_length : uList.length = 39 := by decide

/-- The published terms agree with Fibonacci on `1 <= n <= 9`, which is the regime the
    paper contrasts with the first deviation. -/
theorem agrees_with_fib_to_nine :
    u 1 = 3 ∧ u 2 = 5 ∧ u 3 = 8 ∧ u 4 = 13 ∧ u 5 = 21 ∧
    u 6 = 34 ∧ u 7 = 55 ∧ u 8 = 89 ∧ u 9 = 144 := by decide

/-- **The first deviation from Fibonacci**, at `n = 10`: `u_10 = 225 = F(13) - 8 = 233 - 8`. -/
theorem first_deviation : u 10 = 225 ∧ 233 - 8 = 225 ∧ u 10 ≠ 233 := by decide

/-- **The closed form mod 2.**  `u_d` is even exactly when `d` is a positive multiple of 3;
    at `d = 0` the pattern is broken, `u_0 = 1` being odd. -/
theorem mod2_closed_form :
    ∀ d, d < 39 → u d % 2 = (if 3 ≤ d ∧ d % 3 = 0 then 0 else 1) := by decide

/-- **Eventual 3-periodicity with pre-period 1.**  From `d = 1` onwards the mod-2 sequence
    repeats with period 3. -/
theorem eventually_three_periodic :
    ∀ d, d < 36 → 1 ≤ d → u (d + 3) % 2 = u d % 2 := by decide

/-- **It is not purely periodic.**  Period 3 from `d = 0` would force `u_0` even, since
    `0 % 3 = 0` and `u_3` is even; but `u_0 = 1`. -/
theorem not_purely_periodic : u 3 % 2 = 0 ∧ u 0 % 2 = 1 ∧ u 0 % 2 ≠ u 3 % 2 := by decide

/-- **The order-2 Fibonacci recurrence holds mod 2 from `d = 3` onwards.** -/
theorem fib_recurrence_from_three :
    ∀ d, d < 39 → 3 ≤ d → u d % 2 = (u (d - 1) + u (d - 2)) % 2 := by decide

/-- **And it fails at `d = 2`**, which is why the pre-period is 1 and not 0:
    `u_0 + u_1 = 4` is even while `u_2 = 5` is odd. -/
theorem fib_recurrence_fails_at_two :
    u 0 + u 1 = 4 ∧ (u 0 + u 1) % 2 = 0 ∧ u 2 % 2 = 1 ∧
    u 2 % 2 ≠ (u 0 + u 1) % 2 := by decide

/-- **The mod-2 sequence takes only the two values 0 and 1 on the published range**, and
    both occur, so the reduction is genuinely non-constant. -/
theorem mod2_nonconstant :
    (∀ d, d < 39 → u d % 2 = 0 ∨ u d % 2 = 1) ∧
    (∃ d, d < 39 ∧ u d % 2 = 0) ∧ (∃ d, d < 39 ∧ u d % 2 = 1) := by decide

/-- **u is strictly increasing across the published range.**  This is the evidence for the
    unboundedness used by `prop:height-gap`; it is not a proof of unboundedness, which is a
    statement about all `d` and comes from the exponential growth rate proved elsewhere.  The
    consequence drawn from unboundedness is formalised in
    `PaperExtraCounts.not_automatic_of_unbounded`. -/
theorem u_strictly_increasing : ∀ d, d < 38 → u d < u (d + 1) := by decide

/-! ### Axiom audit (Rule 5)

    For `decide`-proved theorems an EMPTY axiom list is the expected and correct output, so
    here the certificate is a clean compile with no `sorryAx` rather than a non-empty list.
    Beware that a constant which failed to elaborate also prints "does not depend on any
    axioms", so the empty line must never be read as a certificate on its own. -/

#print axioms uList_length
#print axioms agrees_with_fib_to_nine
#print axioms first_deviation
#print axioms mod2_closed_form
#print axioms eventually_three_periodic
#print axioms not_purely_periodic
#print axioms fib_recurrence_from_three
#print axioms fib_recurrence_fails_at_two
#print axioms mod2_nonconstant
#print axioms u_strictly_increasing

end PaperExtraMod2
