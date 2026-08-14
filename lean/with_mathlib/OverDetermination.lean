/-
  OverDetermination.lean
  ======================
  The guard lemma for finite-horizon exclusion searches.

  Several results in this project have the shape

      "on the terms u_0, ..., u_{L}, no relation of shape S exists",

  proved by setting up the homogeneous linear system that a relation of shape S would have to
  satisfy and finding its solution set empty.  Such a search is only informative when the
  system is over-determined.  A homogeneous system with strictly more unknowns than equations
  has a nontrivial solution for EVERY coefficient matrix, hence for every input sequence, so
  the search reports "a relation exists" no matter what the data are and excludes nothing.

  This actually happened.  In the supplementary note, the D-finite exclusion quantified over
  all pairs (k,m) with k <= 9 and m <= 7 without the guard; twenty of those seventy-two pairs
  are underdetermined, the extreme case (9,7) having 80 unknowns against 34 equations.  A
  nonlinear exclusion in the same section had 252 unknowns against 38 equations.  Both are
  vacuous, and the counts below are proved rather than asserted.

  The guard is NECESSARY, not sufficient: `unknowns <= equations` does not make a search
  informative, since one still needs the coefficient matrix to have full column rank.  What is
  proved here is exactly the negative direction, which is what catches the error.
-/

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

namespace OverDetermination

open Module

/-! ### 1. The abstract statement -/

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]

omit [FiniteDimensional K V] in
/-- **A map to a smaller space has a nonzero kernel vector.**  This is the whole content: if
    the target has strictly smaller dimension than the source, no linear map between them is
    injective, so the homogeneous system `f v = 0` has a nontrivial solution. -/
theorem exists_ne_zero_of_finrank_lt (f : V →ₗ[K] W)
    (h : finrank K W < finrank K V) :
    ∃ v : V, v ≠ 0 ∧ f v = 0 := by
  by_contra hc
  rw [not_exists] at hc
  simp only [not_and] at hc
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    by_contra hm0
    exact hc m hm0 hm
  exact absurd (LinearMap.finrank_le_finrank_of_injective hinj) (not_le.mpr h)

/-! ### 2. The matrix form, which is how a search is actually set up

    `equations` rows, `unknowns` columns; the unknown is the coefficient vector `c`. -/

/-- **The guard.**  With strictly more unknowns than equations, the homogeneous system
    `A c = 0` has a nontrivial solution for every matrix `A` whatsoever.  In particular the
    solution set is never empty, and an exclusion search over such a shape reports nothing
    about the data it was run on. -/
theorem exists_nonzero_solution
    {equations unknowns : ℕ} (A : Matrix (Fin equations) (Fin unknowns) K)
    (h : equations < unknowns) :
    ∃ c : Fin unknowns → K, c ≠ 0 ∧ A.mulVec c = 0 := by
  have hV : finrank K (Fin unknowns → K) = unknowns := Module.finrank_fin_fun K
  have hW : finrank K (Fin equations → K) = equations := Module.finrank_fin_fun K
  have hlt : finrank K (Fin equations → K) < finrank K (Fin unknowns → K) := by
    rw [hV, hW]; exact h
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_of_finrank_lt (Matrix.mulVecLin A) hlt
  exact ⟨c, hc0, hc⟩

/-- The contrapositive, in the form a referee wants: if a search over a shape with `unknowns`
    free coefficients, run against `equations` data constraints, reports that no nontrivial
    relation exists, then necessarily `unknowns <= equations`.  Failing that, the report is
    false. -/
theorem le_of_exclusion
    {equations unknowns : ℕ} (A : Matrix (Fin equations) (Fin unknowns) K)
    (hexcl : ∀ c : Fin unknowns → K, A.mulVec c = 0 → c = 0) :
    unknowns ≤ equations := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  obtain ⟨c, hc0, hc⟩ := exists_nonzero_solution A hlt
  exact hc0 (hexcl c hc)

/-! ### 3. The two searches that failed the guard

    Counts are over the terms `u_0, ..., u_42`, so `43` terms in all. -/

/-- Unknowns in a D-finite ansatz of order `k` with coefficient degree `m`. -/
def dfiniteUnknowns (k m : ℕ) : ℕ := (k + 1) * (m + 1)

/-- Equations available at order `k` from 43 terms. -/
def dfiniteEquations (k : ℕ) : ℕ := 43 - k

/-- The pairs searched in the note: `1 <= k <= 9`, `0 <= m <= 7`. -/
def searched : Finset (ℕ × ℕ) := (Finset.Icc 1 9) ×ˢ (Finset.range 8)

/-- Those among them for which the system is not over-determined, so that the exclusion is
    vacuous. -/
def vacuous : Finset (ℕ × ℕ) :=
  searched.filter (fun p => dfiniteEquations p.1 ≤ dfiniteUnknowns p.1 p.2)

theorem searched_card : searched.card = 72 := by decide

/-- **Twenty of the seventy-two pairs are vacuous.**  The note excluded on all of them. -/
theorem vacuous_card : vacuous.card = 20 := by decide

/-- The extreme case: at `(k,m) = (9,7)` there are 80 unknowns against 34 equations. -/
theorem worst_case :
    dfiniteUnknowns 9 7 = 80 ∧ dfiniteEquations 9 = 34 ∧
    dfiniteEquations 9 < dfiniteUnknowns 9 7 := by
  refine ⟨rfl, rfl, by decide⟩

/-- The nonlinear search: monomials of total degree at most 3 in the six variables
    `u_n, ..., u_{n-5}` number `C(9,3) = 84`, and with three coefficient degrees that is 252
    unknowns, against the 38 equations a lookback of 5 leaves. -/
theorem nonlinear_vacuous :
    Nat.choose 9 3 = 84 ∧ 84 * 3 = 252 ∧ (43 - 5 = 38) ∧ 38 < 252 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The linear search, by contrast, passes the guard, and order 19 is exactly the largest
    order it can pass: at order `k` on 39 terms there are `k` unknowns and `39 - k`
    equations. -/
theorem linear_order_19_ok : 19 ≤ 39 - 19 := by decide

theorem linear_order_20_vacuous : 39 - 20 < 20 := by decide

/-! ### 4. What the guard does and does not give

    `le_of_exclusion` says the inequality is forced by a correct exclusion, so its failure
    convicts the exclusion.  The converse fails: a system can be square or tall and still have
    a nontrivial kernel, so passing the guard leaves the rank computation to be done.  The
    lemma is a filter on claims, not a substitute for the linear algebra. -/

theorem guard_not_sufficient :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℚ), (∃ c : Fin 2 → ℚ, c ≠ 0 ∧ A.mulVec c = 0) := by
  refine ⟨0, fun _ => 1, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    simp [Matrix.mulVec]

end OverDetermination

-- Rule 5 axiom audit.
#print axioms OverDetermination.exists_ne_zero_of_finrank_lt
#print axioms OverDetermination.exists_nonzero_solution
#print axioms OverDetermination.le_of_exclusion
#print axioms OverDetermination.searched_card
#print axioms OverDetermination.vacuous_card
#print axioms OverDetermination.worst_case
#print axioms OverDetermination.nonlinear_vacuous
#print axioms OverDetermination.linear_order_19_ok
#print axioms OverDetermination.linear_order_20_vacuous
#print axioms OverDetermination.guard_not_sufficient
