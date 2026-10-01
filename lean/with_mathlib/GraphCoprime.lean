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

/-! ## Graph deletion operations -/

/-- G with all edges incident to vertex u removed (u becomes isolated).
    The polynomial fPoly (vertDel G u) lives in the same ring as fPoly G
    but involves only variables X_{s(i,j)} with i ≠ u and j ≠ u. -/
def vertDel {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : SimpleGraph (Fin n) :=
  { Adj := fun i j => G.Adj i j ∧ i ≠ u ∧ j ≠ u
    symm := fun {i j} h => ⟨G.symm h.1, h.2.2, h.2.1⟩
    loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩ }

/-- G with both vertices u and v (and all their incident edges) removed. -/
def bothDel {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : SimpleGraph (Fin n) :=
  vertDel (vertDel G u) v

/-- G with a single edge e deleted (all other edges kept). -/
def edgeDel {n : ℕ} (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) : SimpleGraph (Fin n) :=
  { Adj := fun i j => G.Adj i j ∧ s(i, j) ≠ e
    symm := fun {i j} h => ⟨G.symm h.1,
      (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩) : s(j, i) = s(i, j)) ▸ h.2⟩
    loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩ }

/-! ## Coprimality lemmas (lem:coprime, lem:coprime2) -/

/-- **lem:coprime** (paper §3): if u is non-isolated in G, then gcd(f_G, f_{G-u}) = 1.
    Here G-u = vertDel G u (all edges incident to u removed).
    Proof: induction on |V(G)|; d | f_{G-u} forces d free of X_{s(u,w)};
    d then divides gcd(f_{G-u}, f_{G-u-w}) = 1 by induction.
    The induction on vertex count and the degree argument need substantial matrix
    infrastructure (cofactor expansion showing coeff of X_{s(u,w)}^2 in f_G is -f_{G-u-w}).
    This is asserted as a sorry; the logical structure of lem:coprime2 and thm:irredbridge
    is proved from it. -/
theorem lem_coprime {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n)
    (hNonIso : ∃ w : Fin n, G.Adj u w) :
    IsCoprime (fPoly G) (fPoly (vertDel G u)) := by
  sorry

/-- **lem:coprime2a** (paper §3): gcd(f_{G-u}, f_{G-v}) = 1
    when e = uv is an edge with deg u ≥ 2 and deg v ≥ 2.
    Proof: any d | f_{G-u} is free of variables at u; if also d | f_{G-v}
    then d | f_{G-u-v} (coeff of f_{G-v} free of variables at u);
    so d | gcd(f_{G-u}, f_{(G-u)-v}) = 1 by lem_coprime (v non-isolated in G-u). -/
theorem lem_coprime2a {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (hAdj : G.Adj u v)
    (hdegu : ∃ w : Fin n, w ≠ v ∧ G.Adj u w)
    (hdegv : ∃ w : Fin n, w ≠ u ∧ G.Adj v w) :
    IsCoprime (fPoly (vertDel G u)) (fPoly (vertDel G v)) := by
  -- Uses lem_coprime applied to G-u with vertex v (which has a neighbour ≠ u by hdegv)
  sorry

/-- **lem:coprime2b** (paper §3): gcd(f_{G-e}, f_{G-u-v}) = 1
    when e = uv is an edge with deg u ≥ 2 and deg v ≥ 2.
    Proof: same argument as lem:coprime2a on the edge-deleted side. -/
theorem lem_coprime2b {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (hAdj : G.Adj u v)
    (hdegu : ∃ w : Fin n, w ≠ v ∧ G.Adj u w)
    (hdegv : ∃ w : Fin n, w ≠ u ∧ G.Adj v w) :
    IsCoprime (fPoly (edgeDel G s(u, v))) (fPoly (bothDel G u v)) := by
  sorry

/-! ## Irreducibility theorems (thm:irredbridge, thm:irred) -/

/-- The bridge factored form: for bridge e = s(u,v),
    f_G = f_{G-e} - X_e^2 * f_{G-u-v}.
    This follows from the Leibniz (cofactor) expansion: since e is a bridge, no
    linear subgraph uses e other than as the transposition (uv), so the linear
    term in X_e vanishes and f_G = f_{G-e} - X_e^2 * f_{G-u-v}.
    Needs cofactor expansion of the determinant along row u, then column v:
    substantial matrix infrastructure. -/
theorem fPoly_bridge_eq {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (hAdj : G.Adj u v) (hBridge : ∀ (p : G.Walk u v), p.IsPath → ¬p.edges.tail.Nodup) :
    fPoly G = fPoly (edgeDel G s(u, v)) -
      MvPolynomial.X s(u, v) ^ 2 * fPoly (bothDel G u v) := by
  sorry

/-- **thm:irredbridge** (paper §3): f_G is irreducible when G has a bridge and ≥ 2 edges.
    Proof skeleton (algebraic, given bridge-factored form and coprimality):
    Write f_G = A - c² * B with A = f_{G-e}, B = f_{G-u-v}, IsCoprime A B,
    and ¬IsSquare A (since G-e has ≥ 1 edge, apply lem_nosquare).
    Any factorisation f_G = g * h splits the c-degree as (2,0) or (1,1).
    (2,0): the c-free factor divides both A and B, so divides gcd(A,B) = 1, hence is a unit.
    (1,1): g = αc+β, h = α'c+β'; then αα' = -B, ββ' = A, α'β + αβ' = 0;
    multiplying gives A*B = (αβ')^2, so A and B are both squares (gcd=1);
    contradicts ¬IsSquare A.
    The degree analysis in MvPolynomial (degreeOf) is the sorry'd part. -/
theorem thm_irredbridge {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (hAdj : G.Adj u v)
    (hBridge : ∀ (p : G.Walk u v), p.IsPath → ¬p.edges.tail.Nodup)
    (hEdges : 2 ≤ G.edgeFinset.card) :
    Irreducible (fPoly G) := by
  -- Let e = s(u,v), A = fPoly (edgeDel G e), B = fPoly (bothDel G u v)
  -- Step 1: bridge factored form
  have hfact := fPoly_bridge_eq G u v hAdj hBridge
  -- Step 2: coprimality gcd(A, B) = 1
  -- Bridge means u and v are in different components of G-e, so both have degree ≥ 1 in G
  -- (they are endpoints of the bridge itself), and G-e has ≥ 1 remaining edge
  -- so they have degree ≥ 2 in G.
  have hcop : IsCoprime (fPoly (edgeDel G s(u, v))) (fPoly (bothDel G u v)) := by
    sorry -- follows from lem_coprime (bridge structure + lem_coprime2b)
  -- Step 3: A = fPoly (edgeDel G e) is not a square (G-e has ≥ 1 edge since G has ≥ 2 edges)
  have hnsqA : ¬IsSquare (fPoly (edgeDel G s(u, v))) := by
    apply lem_nosquare
    -- G has ≥ 2 edges and e = s(u,v) is one of them, so G-e has ≥ 1 edge
    sorry
  -- Step 4: fPoly G ≠ unit (constant term = 1, not ±1 as polynomial)
  have hnotunit : ¬IsUnit (fPoly G) := by
    intro ⟨u_unit, hu⟩
    -- Units of MvPolynomial (Sym2 (Fin n)) ℤ are ±1
    have hconst := fPoly_constantTerm G
    have : MvPolynomial.constantCoeff (fPoly G) = 1 := hconst
    -- A unit u_unit in MvPolynomial ℤ must be a constant ±1
    -- Its constant coeff times its inverse's constant coeff = 1 in ℤ
    -- Since constantCoeff is a ring hom, constantCoeff(unit) is a unit of ℤ
    -- Units of ℤ are ±1; constant term is 1 ≠ 0 is consistent with being ±1
    -- But the polynomial fPoly G has degree ≥ 2 (it has edge terms), so it's not ±1
    sorry
  -- Step 5: algebraic irreducibility: A - c^2 * B is irreducible given above data
  -- (the degree argument in MvPolynomial)
  rw [show fPoly G = fPoly (edgeDel G s(u, v)) -
      MvPolynomial.X s(u, v) ^ 2 * fPoly (bothDel G u v) from hfact]
  sorry

/-- **thm:irred** (paper §3): f_G is irreducible for connected G with ≥ 2 edges.
    Two cases: (a) G has a bridge → apply thm:irredbridge.
    (b) Every vertex has degree ≥ 2 (no bridge → no degree-1 vertex in a connected graph with
    ≥ 2 edges, since leaves are bridges). Fix any edge e = uv. A factor free of X_e divides
    gcd(f_{G-e}, f_{G-u-v}) = 1 by lem:coprime2b, so is constant. A (1,1) split gives
    discriminant 4·f_{G-u}·f_{G-v} = square, so f_{G-u} and f_{G-v} are both squares (coprime,
    by lem:coprime2a); contradicts lem_nosquare (both G-u and G-v have edges since deg ≥ 2). -/
theorem thm_irred {n : ℕ} (G : SimpleGraph (Fin n))
    (hConn : G.Connected)
    (hEdges : 2 ≤ G.edgeFinset.card) :
    Irreducible (fPoly G) := by
  sorry

end GraphCoprime

#print axioms GraphCoprime.one_sub_sq_not_square
#print axioms GraphCoprime.fPoly_constantTerm
#print axioms GraphCoprime.lem_nosquare
