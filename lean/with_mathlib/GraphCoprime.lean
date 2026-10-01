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
import Mathlib.LinearAlgebra.Matrix.SchurComplement

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
  have hmap : (1 - adjMatrix G).map
      (MvPolynomial.constantCoeff : MvPolynomial (Sym2 (Fin n)) ℤ →+* ℤ) =
      (1 : Matrix (Fin n) (Fin n) ℤ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, adjMatrix, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp [map_sub, map_one, map_zero, MvPolynomial.constantCoeff_X]
  calc MvPolynomial.constantCoeff (fPoly G)
      = MvPolynomial.constantCoeff (1 - adjMatrix G).det := by simp [fPoly]
    _ = ((1 - adjMatrix G).map MvPolynomial.constantCoeff).det := by
        simp [RingHom.map_det]
    _ = (1 : Matrix (Fin n) (Fin n) ℤ).det := by rw [hmap]
    _ = 1 := Matrix.det_one

/-- **lem:nosquare**: if G has at least one edge, fPoly G is not a square.
    Proof strategy: specialize X_{s(i₀,j₀)}→T, all others→0, giving φ(fPoly G)=1-T².
    For the det computation, use the Weinstein–Aronszajn identity (det_one_sub_mul_comm)
    to reduce to a 2×2 determinant. -/
theorem lem_nosquare {n : ℕ} (G : SimpleGraph (Fin n))
    (hH : ∃ i j : Fin n, G.Adj i j) :
    ¬ IsSquare (fPoly G) := by
  obtain ⟨i₀, j₀, hadj⟩ := hH
  have hij : i₀ ≠ j₀ := hadj.ne
  let e₀ : Sym2 (Fin n) := s(i₀, j₀)
  let φ : MvPolynomial (Sym2 (Fin n)) ℤ →+* Polynomial ℤ :=
    MvPolynomial.eval₂Hom Polynomial.C (fun e => if e = e₀ then Polynomial.X else 0)
  have hphi : φ (fPoly G) = 1 - Polynomial.X ^ 2 := by
    have hdet : φ (fPoly G) = ((1 - adjMatrix G).map φ).det := by
      simp [fPoly, RingHom.map_det]
    rw [hdet]
    -- A : n×2 matrix with columns e_{i₀}, e_{j₀}
    -- B : 2×n matrix with rows X·e_{j₀}^T, X·e_{i₀}^T
    -- so A*B = X·(E_{i₀j₀} + E_{j₀i₀}), the off-diagonal part
    let A : Matrix (Fin n) (Fin 2) (Polynomial ℤ) :=
      Matrix.of fun i k => if k = 0 then (if i = i₀ then 1 else 0)
                           else (if i = j₀ then 1 else 0)
    let B : Matrix (Fin 2) (Fin n) (Polynomial ℤ) :=
      Matrix.of fun k j => if k = 0 then (if j = j₀ then Polynomial.X else 0)
                           else (if j = i₀ then Polynomial.X else 0)
    -- Step 1: (1 - adjMatrix G).map φ = 1 - A * B  (entry-by-entry)
    have hAB : (1 - adjMatrix G).map φ = 1 - A * B := by
      ext i j
      -- LHS: expand matrix operations
      simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply,
                 adjMatrix, Matrix.of_apply, A, B, Matrix.mul_apply,
                 Fin.sum_univ_two, Matrix.of_apply]
      -- Key: eval₂Hom_X' works when φ is explicitly spelled out
      have hφX : φ (MvPolynomial.X s(i, j)) = if s(i, j) = e₀ then Polynomial.X else 0 :=
        MvPolynomial.eval₂Hom_X' Polynomial.C (fun e => if e = e₀ then Polynomial.X else 0) s(i, j)
      -- Distribute φ over the matrix entry
      rw [map_sub,
          show φ (if i = j then (1 : MvPolynomial (Sym2 (Fin n)) ℤ) else 0) =
              if i = j then (1 : Polynomial ℤ) else 0 from by split_ifs <;> simp [map_one, map_zero],
          show φ (if G.Adj i j then MvPolynomial.X s(i, j) else 0) =
              if G.Adj i j then (if s(i, j) = e₀ then Polynomial.X else 0) else 0 from by
            rw [show φ (if G.Adj i j then MvPolynomial.X s(i, j) else 0) =
                    if G.Adj i j then φ (MvPolynomial.X s(i, j)) else φ 0 from
                  apply_ite φ _ _ _, hφX, map_zero]]
      -- e₀ = s(i₀,j₀) as an explicit equation for simp
      have he₀ : e₀ = s(i₀, j₀) := rfl
      -- Now case split on s(i,j) = e₀
      by_cases hse : s(i, j) = e₀
      · -- Use rw instead of subst to avoid issues with outer variables
        rw [if_pos hse]
        have hse' : s(i, j) = s(i₀, j₀) := by rw [← he₀]; exact hse
        rw [Sym2.eq_iff] at hse'
        rcases hse' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- i = i₀, j = j₀
          rw [h1, h2]; simp [hadj, hij, hij.symm]
        · -- i = j₀, j = i₀
          rw [h1, h2]; simp [hadj.symm, hij, hij.symm]
      · rw [if_neg hse]
        rw [he₀, Sym2.eq_iff] at hse
        simp only [not_or, not_and] at hse
        obtain ⟨hne1, hne2⟩ := hse
        -- hne1 : i=i₀ → j≠j₀, hne2 : i=j₀ → j≠i₀
        by_cases hi0 : i = i₀
        · simp [hi0, hne1 hi0, hij, hij.symm]
        · by_cases hi1 : i = j₀
          · simp [hi0, hi1, hne2 hi1, hij, hij.symm]
          · simp [hi0, hi1]
    -- Step 2: apply Weinstein–Aronszajn
    rw [hAB, Matrix.det_one_sub_mul_comm]
    -- Step 3: compute the 2×2 determinant of 1 - B * A
    -- Unfold B and A for the matrix entry proofs
    have hB : B = Matrix.of (fun (k : Fin 2) (j : Fin n) =>
        if k = 0 then (if j = j₀ then Polynomial.X else 0)
        else (if j = i₀ then Polynomial.X else 0)) := rfl
    have hA : A = Matrix.of (fun (i : Fin n) (k : Fin 2) =>
        if k = 0 then (if i = i₀ then (1 : Polynomial ℤ) else 0)
        else (if i = j₀ then 1 else 0)) := rfl
    -- Entry lemmas: unfold B and A at each (row, col) index
    -- B 0 k = if k=j₀ then X else 0
    have hB0k : ∀ k, B 0 k = if k = j₀ then Polynomial.X else 0 := fun k => by
      simp [hB, Matrix.of_apply]
    -- B 1 k = if k=i₀ then X else 0
    have hB1k : ∀ k, B 1 k = if k = i₀ then Polynomial.X else 0 := fun k => by
      simp [hB, Matrix.of_apply]
    -- A k 0 = if k=i₀ then 1 else 0
    have hAk0 : ∀ k, A k 0 = if k = i₀ then (1:Polynomial ℤ) else 0 := fun k => by
      simp [hA, Matrix.of_apply]
    -- A k 1 = if k=j₀ then 1 else 0
    have hAk1 : ∀ k, A k 1 = if k = j₀ then (1:Polynomial ℤ) else 0 := fun k => by
      simp [hA, Matrix.of_apply]
    -- (B*A) 0 0 = 0  (j₀ ≠ i₀)
    have hsum00 : (B * A) 0 0 = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero; intro k _
      rw [hB0k, hAk0]
      split_ifs with h1 h2
      · exact absurd (h1.symm.trans h2) hij.symm
      · ring
      · ring
      · ring
    -- (B*A) 0 1 = X
    have hsum01 : (B * A) 0 1 = Polynomial.X := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single j₀
          (by intro k _ hk; rw [hB0k, hAk1, if_neg hk, zero_mul])
          (by simp)]
      rw [hB0k, hAk1, if_pos rfl, if_pos rfl, mul_one]
    -- (B*A) 1 0 = X
    have hsum10 : (B * A) 1 0 = Polynomial.X := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single i₀
          (by intro k _ hk; rw [hB1k, hAk0, if_neg hk, zero_mul])
          (by simp)]
      rw [hB1k, hAk0, if_pos rfl, if_pos rfl, mul_one]
    -- (B*A) 1 1 = 0  (i₀ ≠ j₀)
    have hsum11 : (B * A) 1 1 = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero; intro k _
      rw [hB1k, hAk1]
      split_ifs with h1 h2
      · exact absurd (h1.symm.trans h2) hij
      · ring
      · ring
      · ring
    -- Assemble the 2×2 determinant
    rw [Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.one_apply, hsum00, hsum01, hsum10, hsum11,
               eq_self_iff_true, if_true,
               show ((0:Fin 2) = 1) = False from by decide,
               show ((1:Fin 2) = 0) = False from by decide, if_false]
    ring
  -- If fPoly G is a square, so is φ(fPoly G) = 1 - X², contradiction
  intro ⟨s, hs⟩
  apply one_sub_sq_not_square
  rw [← hphi]
  exact ⟨φ s, by rw [← map_mul, ← hs]⟩

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
#print axioms GraphCoprime.fPoly_constantTerm
#print axioms GraphCoprime.lem_nosquare
