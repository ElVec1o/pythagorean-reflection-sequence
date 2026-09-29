/-
NosquareLemma.lean
==================
Formalises the algebraic core of `lem:nosquare` from
`paper/journal/merged_novel_paper.tex`:

    If H has at least one edge then f_H is not the square of a polynomial.

The paper's argument: pick an edge e = uv; viewing f_H as a polynomial in c_e,
its degree in c_e is 2 and the c_e²-coefficient is -f_{H-u-v}.  If f_H = s²
then s has c_e-degree 1, say s = α·c_e + β, and comparing c_e²-coefficients
gives α² = -f_{H-u-v}.  Evaluating at all other variables = 0 yields
α(0)² = -1, impossible in ℝ.

We capture the impossible step abstractly:
  (1) MvPolynomial form: constantCoeff P < 0  ⟹  P is not a perfect square.
  (2) Polynomial form:   eval x P < 0         ⟹  P is not a perfect square.

Both follow immediately from `sq_nonneg` and the fact that `constantCoeff` /
`eval` are ring homomorphisms.

No sorry.
-/

import Mathlib.Tactic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace NosquareLemma

/-! ## MvPolynomial form -/

/-- Algebraic core of lem:nosquare (MvPolynomial form).
    If the constant coefficient of P is negative, then P is not a perfect square.
    Applied to P = -f_{H-u-v}: `MvPolynomial.constantCoeff (-f_{H-u-v}) = -1 < 0`. -/
theorem mvpoly_not_isSquare_of_neg_constantCoeff
    {σ : Type*} {P : MvPolynomial σ ℝ}
    (h : MvPolynomial.constantCoeff P < 0) : ¬IsSquare P := by
  intro ⟨Q, hQ⟩
  have heval : MvPolynomial.constantCoeff P = (MvPolynomial.constantCoeff Q) ^ 2 := by
    rw [hQ, map_mul, sq]
  linarith [sq_nonneg (MvPolynomial.constantCoeff Q)]

/-! ## Polynomial form -/

/-- Algebraic core of lem:nosquare (Polynomial ℝ form).
    If the evaluation of P at some real x is negative, then P is not a perfect square.
    Covers the evaluation step `α(0)² = -1` that rules out f_H being a square. -/
theorem poly_not_isSquare_of_eval_neg
    {P : Polynomial ℝ} {x : ℝ} (h : Polynomial.eval x P < 0) : ¬IsSquare P := by
  intro ⟨Q, hQ⟩
  have heval : Polynomial.eval x P = (Polynomial.eval x Q) ^ 2 := by
    rw [hQ, Polynomial.eval_mul, sq]
  linarith [sq_nonneg (Polynomial.eval x Q)]

end NosquareLemma

-- Rule 5 axiom audit.
#print axioms NosquareLemma.mvpoly_not_isSquare_of_neg_constantCoeff
#print axioms NosquareLemma.poly_not_isSquare_of_eval_neg
