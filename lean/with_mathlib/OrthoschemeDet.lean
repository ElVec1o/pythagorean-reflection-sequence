/-
  OrthoschemeDet.lean
  ===================
  The uniform Schur-complement determinant identity for the n-dimensional
  right-corner orthoscheme (paper 1b, Lemma "uniform-detQ"):

      det Q_n  =  - ∏_{i=1}^n a_i^2.

  `SchurGeneral.lean` proves the individual polynomial steps by `ring`.
  This file ASSEMBLES them: the leading principal minors D_k are pinned by
  a two-step induction to the closed form

      D_k = (∏_{i=1}^k a_i^2) * (1 - ∑_{i=1}^{k+1} a_i^2),

  and the boundary row then yields the determinant.  The point of the file
  is that the paper's appeal to a computer-algebra expansion
  ("SymPy verifies expand(LHS - RHS) = 0") is replaced by a checked proof.

  Everything is stated over an arbitrary commutative ring: no positivity,
  no ordering, no characteristic assumption is used.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OrthoschemeDet

open Finset

variable {R : Type*} [CommRing R]

/-- `SS a k = ∑_{i=1}^k a i ^ 2`. -/
def SS (a : ℕ → R) (k : ℕ) : R := ∑ i ∈ Finset.Icc 1 k, (a i) ^ 2

/-- `PP a k = ∏_{i=1}^k a i ^ 2`. -/
def PP (a : ℕ → R) (k : ℕ) : R := ∏ i ∈ Finset.Icc 1 k, (a i) ^ 2

@[simp] lemma SS_zero (a : ℕ → R) : SS a 0 = 0 := by simp [SS]

@[simp] lemma PP_zero (a : ℕ → R) : PP a 0 = 1 := by simp [PP]

lemma SS_succ (a : ℕ → R) (k : ℕ) : SS a (k + 1) = SS a k + (a (k + 1)) ^ 2 := by
  unfold SS
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]

lemma PP_succ (a : ℕ → R) (k : ℕ) : PP a (k + 1) = PP a k * (a (k + 1)) ^ 2 := by
  unfold PP
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]

/-- **The closed form for the leading principal minors.**
    `D` is any sequence satisfying the two initial conditions and the interior
    tridiagonal recurrence; the conclusion holds for every index. -/
theorem minor_closed_form (a D : ℕ → R)
    (h0 : D 0 = 1 - (a 1) ^ 2)
    (h1 : D 1 = (a 1) ^ 2 * (1 - (a 1) ^ 2 - (a 2) ^ 2))
    (hrec : ∀ k : ℕ, D (k + 2) =
      ((a (k + 2)) ^ 2 + (a (k + 3)) ^ 2) * D (k + 1)
        - ((a (k + 1)) * (a (k + 3))) ^ 2 * D k) :
    ∀ k : ℕ, D k = PP a k * (1 - SS a (k + 1)) := by
  have key : ∀ k : ℕ, D k = PP a k * (1 - SS a (k + 1))
      ∧ D (k + 1) = PP a (k + 1) * (1 - SS a (k + 2)) := by
    intro k
    induction k with
    | zero =>
      have hs1 : SS a 1 = (a 1) ^ 2 := by simpa using SS_succ a 0
      have hp1 : PP a 1 = (a 1) ^ 2 := by simpa using PP_succ a 0
      have hs2 : SS a 2 = (a 1) ^ 2 + (a 2) ^ 2 := by simpa [hs1] using SS_succ a 1
      constructor
      · rw [h0, PP_zero, hs1]; ring
      · rw [h1, hp1, hs2]; ring
    | succ n ih =>
      obtain ⟨ihn, ihn1⟩ := ih
      refine ⟨ihn1, ?_⟩
      rw [hrec n, ihn, ihn1, PP_succ (a := a) (k := n + 1), PP_succ (a := a) (k := n),
          SS_succ (a := a) (k := n + 2), SS_succ (a := a) (k := n + 1)]
      ring
  exact fun k => (key k).1

/-- **The determinant identity.**  The boundary row of `Q_n` contributes
    `D n = D (n-1) - a_{n-1}^2 * D (n-2)`; combined with the closed form this
    gives `det Q_n = - ∏_{i=1}^n a_i^2`.  Stated at index `n+2` to keep the
    boundary indices literal. -/
theorem det_Q (a D : ℕ → R) (n : ℕ)
    (hclosed : ∀ k : ℕ, D k = PP a k * (1 - SS a (k + 1)))
    (Dtop : R)
    (hbdry : Dtop = D (n + 1) - (a (n + 1)) ^ 2 * D n) :
    Dtop = - PP a (n + 2) := by
  rw [hbdry, hclosed, hclosed, PP_succ (a := a) (k := n + 1), PP_succ (a := a) (k := n),
      SS_succ (a := a) (k := n + 1), SS_succ (a := a) (k := n)]
  ring

/-- The two combined: the hypotheses of the paper's lemma give its conclusion. -/
theorem det_Q_of_recurrence (a D : ℕ → R) (n : ℕ) (Dtop : R)
    (h0 : D 0 = 1 - (a 1) ^ 2)
    (h1 : D 1 = (a 1) ^ 2 * (1 - (a 1) ^ 2 - (a 2) ^ 2))
    (hrec : ∀ k : ℕ, D (k + 2) =
      ((a (k + 2)) ^ 2 + (a (k + 3)) ^ 2) * D (k + 1)
        - ((a (k + 1)) * (a (k + 3))) ^ 2 * D k)
    (hbdry : Dtop = D (n + 1) - (a (n + 1)) ^ 2 * D n) :
    Dtop = - PP a (n + 2) :=
  det_Q a D n (minor_closed_form a D h0 h1 hrec) Dtop hbdry

end OrthoschemeDet

-- Rule 5 axiom check.
#print axioms OrthoschemeDet.minor_closed_form
#print axioms OrthoschemeDet.det_Q
#print axioms OrthoschemeDet.det_Q_of_recurrence
