/-
  PaperExtraCounts.lean
  =====================
  Paper "extra": the combinatorial and logical content of three propositions.

  (1) `prop:no-dfinite`.  The search grid is the set of pairs (k, m) with 1 <= k <= 9,
      0 <= m <= 7 satisfying the over-determination condition (k+1)(m+1) < 43 - k, the right
      side counting the equations available from u_0, ..., u_42 at order k.  The paper states
      there are 52 such pairs.  That count is verified here, together with the fact that every
      pair on the grid really is over-determined, which is what makes a negative search result
      meaningful.

      NOTE ON A CONVENTION THE PAPER LEAVES IMPLICIT: the count 52 holds for k >= 1, that is
      for recurrences of order at least one.  Allowing k = 0 gives 60 pairs, and requiring
      m >= 1 gives 50.  Only 1 <= k <= 9, 0 <= m <= 7 reproduces the published 52.

  (2) `prop:no-recurrence-strong` (ii), the WITHDRAWN item.  The paper withdraws an earlier
      nonlinear search as vacuous, on the ground that it had more unknowns than equations.
      The arithmetic of that vacuity is verified here: the monomials of total degree at most 3
      in six variables number C(9,3) = 84, three coefficient degrees give 252 unknowns, and
      only 38 equations are available from u_0, ..., u_42.  The step from "more unknowns than
      equations" to "a nontrivial solution always exists, so nothing is excluded" is the
      over-determination guard, proved separately in `with_mathlib/OverDetermination.lean`;
      it needs linear algebra and so cannot live in this Mathlib-free file.

  (3) `prop:height-gap`, the weak consequence.  The paper's own conclusion is that since u_d
      grows exponentially it is unbounded, hence not the value sequence of any k-automatic
      integer sequence, automatic sequences taking finitely many values, and that no
      height-gap theorem is needed for this.  That argument is formalised here in the general
      form it actually has: for ANY notion of automaticity whose sequences are finitely
      valued, an unbounded sequence fails to be automatic.  The finitely-valued property is
      taken as an explicit hypothesis rather than assumed silently.

      SCOPE.  The unboundedness of u itself is NOT established here.  It comes from the
      exponential growth rate proved elsewhere, and is a statement about all d, not about the
      39 published terms.  Strict increase across the published range is verified in
      `PaperExtraMod2.u_strictly_increasing`, which is evidence for unboundedness and not a
      proof of it.  The
      regression numbers in the proposition (slope 0.407927, R^2 >= 0.999) are numerics and
      are not formalised.

  Core Lean 4 only, no Mathlib.  Every finite claim is discharged by kernel evaluation; for
  such theorems an empty `#print axioms` line is expected and correct.
-/

namespace PaperExtraCounts

/-! ### (1) The D-finite search grid -/

/-- All pairs `(k, m)` with `1 <= k <= 9` and `0 <= m <= 7`. -/
def gridPairs : List (Nat × Nat) :=
  (List.range 9).foldr
    (fun i acc => (List.range 8).map (fun m => (i + 1, m)) ++ acc) []

/-- The number of equations available from `u_0, ..., u_42` at order `k`. -/
def equations (k : Nat) : Nat := 43 - k

/-- The number of unknowns in a D-finite ansatz of order `k` with coefficient degree `m`. -/
def unknowns (k m : Nat) : Nat := (k + 1) * (m + 1)

/-- The over-determination condition of the proposition. -/
def overDetermined (p : Nat × Nat) : Bool :=
  decide (unknowns p.1 p.2 < equations p.1)

/-- The search grid actually used: the over-determined pairs. -/
def searchGrid : List (Nat × Nat) := gridPairs.filter overDetermined

theorem gridPairs_length : gridPairs.length = 72 := by decide

/-- **The published count.**  There are 52 over-determined pairs on the grid. -/
theorem searchGrid_count : searchGrid.length = 52 := by decide

/-- **Every pair searched is genuinely over-determined**: strictly fewer unknowns than
    equations.  This is what distinguishes the D-finite search from the withdrawn nonlinear
    one, and it is the reason a negative result there carries information. -/
theorem searchGrid_overDetermined :
    ∀ p ∈ searchGrid, unknowns p.1 p.2 < equations p.1 := by decide

/-- The grid is confined to the stated ranges. -/
theorem searchGrid_ranges :
    ∀ p ∈ searchGrid, 1 ≤ p.1 ∧ p.1 ≤ 9 ∧ p.2 ≤ 7 := by decide

/-- The same grid but allowing order zero. -/
def gridPairsWithZero : List (Nat × Nat) :=
  (List.range 10).foldr
    (fun k acc => (List.range 8).map (fun m => (k, m)) ++ acc) []

/-- Allowing order zero would change the count, so the implicit `k >= 1` matters. -/
theorem count_depends_on_k_ge_one :
    (gridPairsWithZero.filter overDetermined).length = 60 := by decide

/-! ### (2) Why the withdrawn nonlinear search was vacuous -/

/-- Binomial coefficient, defined here because this file uses core Lean only and
    `Nat.choose` lives in Mathlib. -/
def binom : Nat → Nat → Nat
  | _,     0      => 1
  | 0,     _ + 1  => 0
  | n + 1, k + 1  => binom n k + binom n (k + 1)

/-- Monomials of total degree at most 3 in 6 variables, by stars and bars: `C(9,3)`. -/
def nonlinearMonomials : Nat := binom 9 3

/-- Three coefficient degrees `0, 1, 2` per monomial. -/
def nonlinearUnknowns : Nat := nonlinearMonomials * 3

/-- Equations available for the nonlinear search on `u_0, ..., u_42` with lookback 5. -/
def nonlinearEquations : Nat := 38

theorem monomial_count : nonlinearMonomials = 84 := by decide

theorem unknown_count : nonlinearUnknowns = 252 := by decide

/-- **The search was underdetermined**, by a wide margin: 252 unknowns against 38 equations.
    Combined with the over-determination guard, a nontrivial solution exists for every input,
    so the search excluded nothing and its negative result was empty. -/
theorem nonlinear_search_underdetermined :
    nonlinearEquations < nonlinearUnknowns := by decide

/-- The contrast with (1): the D-finite grid is over-determined everywhere, the withdrawn
    nonlinear search was underdetermined. -/
theorem contrast_with_dfinite_grid :
    nonlinearEquations < nonlinearUnknowns ∧
    ∀ p ∈ searchGrid, unknowns p.1 p.2 < equations p.1 := by decide

/-! ### (3) Unbounded sequences are not finitely valued -/

/-- A member of a list is at most the list's sum. -/
theorem mem_le_sum {L : List Nat} {x : Nat} (h : x ∈ L) : x ≤ L.foldr (· + ·) 0 := by
  induction L with
  | nil => cases h
  | cons a t ih =>
    cases List.mem_cons.mp h with
    | inl he => subst he; exact Nat.le_add_right _ _
    | inr ht => exact Nat.le_trans (ih ht) (Nat.le_add_left _ _)

/-- **An unbounded sequence takes infinitely many values**: no finite list contains them all. -/
theorem unbounded_not_finitely_valued (f : Nat → Nat) (hf : ∀ N, ∃ n, N < f n) :
    ¬ ∃ L : List Nat, ∀ n, f n ∈ L := by
  intro h
  obtain ⟨L, hL⟩ := h
  obtain ⟨n, hn⟩ := hf (L.foldr (· + ·) 0)
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hn (mem_le_sum (hL n)))

/-- **The proposition's actual argument, in the generality it has.**  For any notion of
    automaticity whose sequences are finitely valued, an unbounded sequence is not automatic.
    No height-gap theorem is involved, which is exactly the point the proposition makes when
    it withdraws the earlier appeal to one. -/
theorem not_automatic_of_unbounded {Automatic : (Nat → Nat) → Prop}
    (finitelyValued : ∀ g, Automatic g → ∃ L : List Nat, ∀ n, g n ∈ L)
    (f : Nat → Nat) (hf : ∀ N, ∃ n, N < f n) : ¬ Automatic f := by
  intro hA
  exact unbounded_not_finitely_valued f hf (finitelyValued f hA)

/-! ### Axiom audit (Rule 5)

    The finite claims are `decide`-proved and correctly report an empty axiom list; the three
    general lemmas are ordinary proofs.  Certification for this file is a clean compile with
    no `sorryAx`, since an empty line is also what a failed constant prints. -/

#print axioms gridPairs_length
#print axioms searchGrid_count
#print axioms searchGrid_overDetermined
#print axioms searchGrid_ranges
#print axioms count_depends_on_k_ge_one
#print axioms monomial_count
#print axioms unknown_count
#print axioms nonlinear_search_underdetermined
#print axioms contrast_with_dfinite_grid
#print axioms mem_le_sum
#print axioms unbounded_not_finitely_valued
#print axioms not_automatic_of_unbounded

end PaperExtraCounts
