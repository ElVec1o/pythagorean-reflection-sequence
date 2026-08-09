/-
  StratumGeneric.lean
  ===================
  Paper 4, Proposition `prop:cylcensus`: why the tabulated stratum census is the generic value
  and not merely the value at the samples that were run.

  The tabulated counts were computed at two leg samples and the proposition offered a
  monotonicity argument for them, which is false: the table is of sphere counts, and those are
  not monotone under specialisation, since an element of generic length 18 can have length 16
  at a special shape and so move between rows.  What is true, and is the argument already used
  for the census theorem, is a genericity statement.

  The setting is a ONE-PARAMETER stratum.  Fix a length bound; there are finitely many reduced
  words up to that length, hence finitely many ordered pairs of them.  Each pair contributes a
  coincidence condition, a polynomial equation in the stratum parameter.  Every such polynomial
  either vanishes identically, in which case the coincidence holds at every shape of the
  stratum and is part of the generic picture, or it does not, in which case it vanishes only on
  a finite set.  Hence off a finite set of parameters the set of coincidences is exactly the set
  of identically-vanishing ones, and every count read off from it is the generic count.

  That is the content formalised here.  It is stated for an arbitrary index type and an
  arbitrary field, since nothing about triangles enters: what is used is that a nonzero
  polynomial over a field has finitely many roots, and that a finite union of finite sets is
  finite.  The geometry, namely that the coincidence conditions are polynomial in the
  parameter, is supplied by the paper and is not formalised.
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Basic

namespace StratumGeneric

open Polynomial

variable {K : Type*} [Field K] {ι : Type*}

/-- The parameters at which some non-identically-vanishing condition degenerates. -/
def badSet (S : Finset ι) (P : ι → K[X]) : Set K :=
  ⋃ i ∈ (S : Set ι), {t : K | P i ≠ 0 ∧ (P i).IsRoot t}

/-- **The bad set is finite.**  Only the conditions that do not vanish identically contribute,
    and each contributes finitely many parameters. -/
theorem badSet_finite (S : Finset ι) (P : ι → K[X]) : (badSet S P).Finite := by
  refine Set.Finite.biUnion S.finite_toSet ?_
  intro i _
  by_cases h : P i = 0
  · simp [h]
  · exact (finite_setOf_isRoot h).subset (fun t ht => ht.2)

/-- **Off the bad set, the vanishing pattern is exactly the identical one.**  At any parameter
    outside it, a condition holds if and only if it holds identically.  This is what makes the
    census a property of the stratum rather than of the sample. -/
theorem eval_eq_zero_iff_of_not_mem {S : Finset ι} {P : ι → K[X]} {t : K}
    (ht : t ∉ badSet S P) {i : ι} (hi : i ∈ S) :
    (P i).eval t = 0 ↔ P i = 0 := by
  constructor
  · intro h
    by_contra hne
    exact ht (Set.mem_biUnion (by simpa using hi) ⟨hne, h⟩)
  · intro h; simp [h]

/-- **The generic parameter exists**, provided the field is infinite: the bad set is finite and
    so cannot exhaust `K`.  For a one-parameter stratum over `ℚ` this is what guarantees that a
    shape realising the generic census exists at all. -/
theorem exists_generic [Infinite K] (S : Finset ι) (P : ι → K[X]) :
    ∃ t : K, t ∉ badSet S P := by
  by_contra h
  rw [not_exists] at h
  have huniv : (Set.univ : Set K) ⊆ badSet S P := fun x _ => not_not.mp (h x)
  exact Set.infinite_univ ((badSet_finite S P).subset huniv)

/-- **The census is constant off the bad set.**  If a quantity is determined by which
    conditions hold, then it takes the same value at every parameter outside the bad set: the
    generic value.  `count` is any readout of the vanishing pattern. -/
theorem count_eq_of_not_mem {S : Finset ι} {P : ι → K[X]} {t u : K}
    (ht : t ∉ badSet S P) (hu : u ∉ badSet S P)
    (count : (ι → Prop) → ℕ) :
    count (fun i => i ∈ S ∧ (P i).eval t = 0) = count (fun i => i ∈ S ∧ (P i).eval u = 0) := by
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp only [hi, true_and, eq_iff_iff]
    rw [eval_eq_zero_iff_of_not_mem ht hi, eval_eq_zero_iff_of_not_mem hu hi]
  · simp [hi]

/-! ### What this does and does not give

    It gives that the tabulated counts are the generic ones, attained off a finite set of
    parameters, and that two parameters outside that set necessarily agree.  It does NOT
    certify that either of the two leg samples actually used lies outside the bad set; that
    remains a computation, and the paper says so.  What the proposition may now assert is the
    genericity statement, which is what its table is a table of. -/

#print axioms badSet_finite
#print axioms eval_eq_zero_iff_of_not_mem
#print axioms exists_generic
#print axioms count_eq_of_not_mem

end StratumGeneric
