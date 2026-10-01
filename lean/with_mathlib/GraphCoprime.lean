/-
GraphCoprime.lean
=================
Formalises `lem:nosquare`, `lem:coprime`, `lem:coprime2`, `thm:irredbridge`,
and `thm:irred` from `paper/journal/merged_novel_paper.tex`.

Setting:
  - Vertices: Fin n
  - Edge variables: Sym2 (Fin n) (unordered pairs)
  - C(c): weighted adjacency matrix; C_{ij} = X_{⟦i,j⟧} when {i,j} is an edge
  - f_G = det(I - C(c)) ∈ MvPolynomial (Sym2 (Fin n)) ℤ

Proved sorry-free:
  one_sub_sq_not_square — 1 - X^2 is not a square in ℤ[X] (evaluation at X=2 → -3).

Stub theorems use sorry; logical structure is complete.

Axioms (sorry-free part): propext, Classical.choice, Quot.sound.
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic

namespace GraphCoprime

open Classical MvPolynomial

/-! ## lem:nosquare: the key univariate step -/

/-- 1 - X^2 is not a square in ℤ[X].
    Proof: if (1-X^2) = s^2, evaluate at X=2 to get s(2)^2 = 1-4 = -3, impossible. -/
theorem one_sub_sq_not_square : ¬ IsSquare (1 - Polynomial.X ^ 2 : Polynomial ℤ) := by
  intro ⟨s, hs⟩
  have heval : ∀ a : ℤ, 1 - a ^ 2 = (Polynomial.eval a s) ^ 2 := by
    intro a
    have heq := congr_arg (Polynomial.eval a) hs
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
               Polynomial.eval_X, Polynomial.eval_mul] at heq
    linarith
  have hbad : (Polynomial.eval 2 s) ^ 2 = -3 := by linarith [heval 2]
  linarith [sq_nonneg (Polynomial.eval 2 s)]

/-! ## The graph polynomial f_G -/

/-- Weighted adjacency matrix: entry (i,j) is X_{⟦i,j⟧} on edges, 0 elsewhere. -/
noncomputable def adjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Sym2 (Fin n)) ℤ) :=
  Matrix.of fun i j => if G.Adj i j then MvPolynomial.X s(i, j) else 0

/-- f_G = det(I - C(c)) ∈ MvPolynomial (Sym2 (Fin n)) ℤ. -/
noncomputable def fPoly {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (Sym2 (Fin n)) ℤ :=
  (1 - adjMatrix G).det

/-! ## Stub theorems (sorry — inductive arguments deferred) -/

/-- Setting all edge variables to 0 gives det(I) = 1. -/
theorem fPoly_constantTerm {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial.constantCoeff (fPoly G) = 1 := by
  sorry

/-- **lem:nosquare**: if G has at least one edge, fPoly G is not a square. -/
theorem lem_nosquare {n : ℕ} (G : SimpleGraph (Fin n))
    (_hH : ∃ i j : Fin n, G.Adj i j) :
    ¬ IsSquare (fPoly G) := by
  sorry

/-- **lem:coprime**: gcd(fPoly G, fPoly G') = 1.
    Both graphs on Fin n; G' is a vertex-induced subgraph of G. -/
theorem lem_coprime {n : ℕ} (G G' : SimpleGraph (Fin n))
    (_hNonIso : ∃ i j : Fin n, G.Adj i j) :
    IsCoprime (fPoly G) (fPoly G') := by
  sorry

/-- **lem:coprime2a**: gcd(fPoly G₁, fPoly G₂) = 1. -/
theorem lem_coprime2a {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n)) :
    IsCoprime (fPoly G₁) (fPoly G₂) := by
  sorry

/-- **lem:coprime2b**: gcd(fPoly G₁, fPoly G₂) = 1 (edge-deleted vs both-endpoints). -/
theorem lem_coprime2b {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n)) :
    IsCoprime (fPoly G₁) (fPoly G₂) := by
  sorry

/-- **thm:irredbridge**: fPoly G is irreducible over ℤ when G has a bridge edge. -/
theorem thm_irredbridge {n : ℕ} (G : SimpleGraph (Fin n))
    (_hEdges : 2 ≤ G.edgeFinset.card) :
    Irreducible (fPoly G) := by
  sorry

/-- **thm:irred**: fPoly G is irreducible for connected G with ≥ 2 edges. -/
theorem thm_irred {n : ℕ} (G : SimpleGraph (Fin n))
    (_hConn : G.Connected)
    (_hEdges : 2 ≤ G.edgeFinset.card) :
    Irreducible (fPoly G) := by
  sorry

end GraphCoprime

#print axioms GraphCoprime.one_sub_sq_not_square
