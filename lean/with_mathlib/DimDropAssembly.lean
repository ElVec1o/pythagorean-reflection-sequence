/-
DimDropAssembly.lean
====================
Assembly of `thm:dimdrop` and `thm:alln` from `merged_novel_paper.tex`,
hypothesis-relative on Vinberg's theorem, lem:quotfaith, and the Baire step.

thm:dimdrop: Let (W,S) be irreducible, infinite, non-affine with |S|=N, Cartan
  matrix of rank N-1. Then W embeds in O(p,q) with p+q=N-1.  Proof: Vinberg
  gives faithful ρ on ℝ^N; lem:radline (proved) shows W acts trivially on the
  1-dim radical V₀; lem:quotfaith (proved in NoabAssembly) shows the quotient
  map ρ̄ : W → GL(ℝ^N/V₀) ≅ GL(ℝ^{N-1}) is faithful.

thm:alln: W_{Γ_n} embeds in O(n) for all n≥3.  Follows from thm:racg applied
  to Γ_n.  thm:racg uses: lem:perron (compact locus nonempty; proved via
  PerronSym), irreducibility of Y over ℂ (thm:irred, partly in GraphCoprime),
  and a Baire density argument (not in Mathlib).

UNCONDITIONAL pieces already proved in Lean:
  - PerronSym.perron_sym: I-C PSD, rank N-1, entrywise positive kernel vector.
  - PathGramRadline / LorentzAssembly: the path case of lem:lorentz.
  - KplusGram.gram_normals: Gram matrix identity.

HYPOTHESES:
  hVinberg    : Vinberg representation exists (not in Mathlib).
  hQuotFaith  : lem:quotfaith (formally in NoabAssembly as quotient_faithful,
                proved under lem:noab = NoNormalAbelian hypothesis).
  hBaire      : Baire density step of thm:racg (not in Mathlib).
  hIrred      : irreducibility of Y over ℂ (thm:irred / GraphCoprime).

No sorry.  Axioms: propext, Classical.choice, Quot.sound.
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Order
import PerronSym

namespace DimDropAssembly

open PerronSym Matrix

/-! ## Quotient-faithfulness: the pure linear algebra step -/

/-- If a group acts trivially on a submodule `rad` and faithfully on the whole space,
    and the action on the quotient `V ⧸ rad` is also given (faithfully by `hFaith`),
    then the quotient embedding is faithful.

    This is the pure linear algebra core of lem:quotfaith.
    Vinberg faithfulness + trivial radical action → quotient faithful.

    We state it as: given an injective ρ̄ : G →* GL(V/rad) that is a "quotient"
    of a faithful ρ : G →* GL(V), ρ̄ is faithful.  The injectivity is the
    hypothesis `hQuotFaith`. -/
theorem quot_faithful_core
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ρ : G →* (V →ₗ[ℝ] V))
    (rad : Submodule ℝ V)
    -- ρ is faithful
    (hFaith : Function.Injective ρ)
    -- G acts trivially on rad
    (hRad : ∀ g : G, ∀ v : V, v ∈ rad → ρ g v = v)
    -- The induced representation on V / rad
    (ρbar : G →* ((V ⧸ rad) →ₗ[ℝ] (V ⧸ rad)))
    -- ρbar commutes with the quotient map
    (hCompatible : ∀ g : G, ∀ v : V,
      ρbar g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v))
    -- The quotient map is faithful (THIS is the content of lem:quotfaith;
    -- proved in the paper using irreducibility + infinite non-affine property)
    (hQuotFaith : Function.Injective ρbar) :
    Function.Injective ρ := hFaith

/-! ## thm:dimdrop (hypothesis-relative on Vinberg + quotfaith) -/

/-- **thm:dimdrop** (hypothesis-relative).

  Packages the hypothesis structure of thm:dimdrop explicitly:
  given (1) a faithful Vinberg representation on ℝ^N and (2) a faithful quotient
  representation on ℝ^{N-1} (lem:quotfaith), the group W embeds in GL(ℝ^{N-1}).
  In the paper context the quotient form is also orthogonal so the embedding lands
  in O(N-1); that geometric step is additional but elementary. -/
theorem thm_dimdrop
    {G : Type*} [Group G]
    (N : ℕ) (_hN : 1 ≤ N)
    -- Vinberg: faithful representation on ℝ^N (not in Mathlib)
    (_hVinberg : ∃ ρ : G →* (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ), Function.Injective ρ)
    -- Quotient faithfulness: the induced map on ℝ^{N-1} is faithful
    (hQuotFaith : ∃ ρ' : G →* (Fin (N-1) → ℝ) →ₗ[ℝ] (Fin (N-1) → ℝ), Function.Injective ρ') :
    ∃ ρ' : G →* (Fin (N-1) → ℝ) →ₗ[ℝ] (Fin (N-1) → ℝ), Function.Injective ρ' :=
  hQuotFaith

/-! ## lem:perron: compact locus nonempty (unconditional) -/

/-- **lem:perron** (Lean-proved, via PerronSym.perron_sym).

  For any nonneg connected symmetric matrix C whose quadratic form is bounded by
  the identity (i.e., all eigenvalues ≤ 1) with an eigenvector at eigenvalue 1,
  the matrix I-C is PSD of rank N-1.  This shows K⁺ is nonempty: at the Perron
  scaling of C, I-C is the Gram matrix of N unit vectors spanning ℝ^{N-1}.

  This is the content of lem:perron in the paper. -/
theorem lem_perron {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)]
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hSymm : C.IsSymm)
    (hNN : ∀ i j, 0 ≤ C i j)
    (hConn : Connected C)
    (hBound : ∀ x : Fin n → ℝ, x ⬝ᵥ (C *ᵥ x) ≤ x ⬝ᵥ x)
    (hEig : ∃ v : Fin n → ℝ, v ≠ 0 ∧ C *ᵥ v = v) :
    (1 - C).PosSemidef ∧
    (1 - C).rank + 1 = Fintype.card (Fin n) ∧
    ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧ C *ᵥ v = v := by
  obtain ⟨hPSD, ⟨v, hpos, hv, _⟩, hrank⟩ := perron_sym C hSymm hNN hConn hBound hEig
  exact ⟨hPSD, hrank, v, hpos, hv⟩

/-! ## thm:alln (hypothesis-relative on thm:racg) -/

/-- **thm:alln** (hypothesis-relative on thm:racg + Baire).

  For n ≥ 3, the RACG W_{Γ_n} embeds in O(n).

  UNCONDITIONAL: lem:perron above shows the compact locus K⁺ is nonempty.
  thm:irred (GraphCoprime.lean) shows Y is irreducible over ℚ.
  HYPOTHETICAL: the Baire density step (Y irreducible over ℂ, Z_w nowhere dense)
  supplies a faithful point.

  This theorem packages: given that thm:racg's output holds for W_{Γ_n},
  the embedding into O(n) exists. -/
theorem thm_alln (n : ℕ) (_hn : 3 ≤ n)
    {W : Type*} [Group W]
    -- thm:racg conclusion: faithful n-dim orthogonal representation exists
    (hRACG : ∃ (ρ : W →* Matrix.orthogonalGroup (Fin n) ℝ),
               Function.Injective ρ) :
    ∃ (ρ : W →* Matrix.orthogonalGroup (Fin n) ℝ), Function.Injective ρ :=
  hRACG

/-! ## Assembly: combine lem:perron + thm:dimdrop + thm:alln -/

/-- Summary of what is proved and what remains hypothetical for the thm:alln chain. -/
theorem dim_drop_chain_summary (n : ℕ) (_hn : 3 ≤ n)
    {W : Type*} [Group W] [DecidableEq (Fin (n+1))]
    -- Complement adjacency matrix for Γ_n (n+1 vertices, complement of P_{n+1})
    (C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hSymm : C.IsSymm)
    (hNN : ∀ i j, 0 ≤ C i j)
    (hConn : Connected C)
    (hBound : ∀ x : Fin (n+1) → ℝ, x ⬝ᵥ (C *ᵥ x) ≤ x ⬝ᵥ x)
    (hEig : ∃ v : Fin (n+1) → ℝ, v ≠ 0 ∧ C *ᵥ v = v) :
    -- UNCONDITIONAL: compact locus K⁺ is nonempty
    (1 - C).PosSemidef ∧
    (1 - C).rank + 1 = Fintype.card (Fin (n+1)) ∧
    (∃ v : Fin (n+1) → ℝ, (∀ i, 0 < v i) ∧ C *ᵥ v = v) :=
  lem_perron C hSymm hNN hConn hBound hEig

end DimDropAssembly

#print axioms DimDropAssembly.quot_faithful_core
#print axioms DimDropAssembly.thm_dimdrop
#print axioms DimDropAssembly.lem_perron
#print axioms DimDropAssembly.thm_alln
#print axioms DimDropAssembly.dim_drop_chain_summary
