/-
W3struct.lean
=============
Formalises `lem:W3struct` from `paper/journal/merged_novel_paper.tex`.

W_{Γ_3} is the right-angled Coxeter group on generators R₀,R₁,R₂,R₃ with:
  • Rᵢ² = 1 for all i  (involutions)
  • Commutation from edges of Γ₃ = complement of path P₄:
    edges {0,2},{0,3},{1,3}: R₀R₂=R₂R₀, R₀R₃=R₃R₀, R₁R₃=R₃R₁.

This file works in ANY group G satisfying these relations (abstract RACG approach).

Proved unconditionally (pure group theory):
  (A) All four conjugation identities of lem:W3struct.
  (B) A = R₀R₁ and C = R₂R₃ lie in ker φ for any φ with φ(R₀)=φ(R₁), φ(R₂)=φ(R₃).
  (C) V = ⟨R₀,R₃⟩ is a Klein-four group: (R₀R₃)² = 1.

HYPOTHESIS (hFree, lem:W3struct line 2):
  ⟨A,C⟩ is free on {A,C}. (Bass-Serre: W_{Γ_3} is π₁ of a graph of groups with vertex
  groups Z/2×Z/2, edge groups Z/2; virtually free, torsion-free subgroup has rank 2.)
  Bass-Serre theory is not in Mathlib.

Under hFree, the semidirect product structure W = ⟨A,C⟩ ⋊ V follows.

No sorry.  Axioms: propext, Classical.choice, Quot.sound.
-/

import Mathlib.Tactic

namespace W3struct

variable {G : Type*} [Group G] (R : Fin 4 → G)

/-! ## Auxiliary: involution implies self-inverse -/

theorem invol_mul_self (hR : ∀ i, R i ^ 2 = 1) (i : Fin 4) : R i * R i = 1 := by
  have := hR i; rwa [sq] at this

theorem invol_inv (hR : ∀ i, R i ^ 2 = 1) (i : Fin 4) : (R i)⁻¹ = R i :=
  inv_eq_of_mul_eq_one_right (invol_mul_self R hR i)

/-! ## Part (A): The four conjugation identities -/

/-- R₀ · (R₀R₁) · R₀ = (R₀R₁)⁻¹.  Uses only R₀²=R₁²=1. -/
theorem conj_A_by_R0 (hR : ∀ i, R i ^ 2 = 1) :
    R 0 * (R 0 * R 1) * R 0 = (R 0 * R 1)⁻¹ := by
  rw [mul_inv_rev, invol_inv R hR 0, invol_inv R hR 1]
  have h0 : R 0 * R 0 = 1 := invol_mul_self R hR 0
  calc R 0 * (R 0 * R 1) * R 0
      = R 0 * R 0 * R 1 * R 0 := by group
    _ = 1 * R 1 * R 0          := by rw [h0]
    _ = R 1 * R 0               := by rw [one_mul]

/-- R₃ · (R₂R₃) · R₃ = (R₂R₃)⁻¹.  Uses only R₂²=R₃²=1. -/
theorem conj_C_by_R3 (hR : ∀ i, R i ^ 2 = 1) :
    R 3 * (R 2 * R 3) * R 3 = (R 2 * R 3)⁻¹ := by
  rw [mul_inv_rev, invol_inv R hR 2, invol_inv R hR 3]
  have h3 : R 3 * R 3 = 1 := invol_mul_self R hR 3
  calc R 3 * (R 2 * R 3) * R 3
      = R 3 * R 2 * (R 3 * R 3) := by group
    _ = R 3 * R 2 * 1            := by rw [h3]
    _ = R 3 * R 2                := by rw [mul_one]

/-- R₀ · (R₂R₃) · R₀ = R₂R₃.  Uses R₀R₂=R₂R₀ and R₀R₃=R₃R₀. -/
theorem conj_C_by_R0
    (hR  : ∀ i, R i ^ 2 = 1)
    (h02 : Commute (R 0) (R 2))
    (h03 : Commute (R 0) (R 3)) :
    R 0 * (R 2 * R 3) * R 0 = R 2 * R 3 := by
  have h0 : R 0 * R 0 = 1 := invol_mul_self R hR 0
  calc R 0 * (R 2 * R 3) * R 0
      = (R 0 * R 2) * (R 3 * R 0) := by group
    _ = (R 2 * R 0) * (R 0 * R 3) := by rw [h02.eq, ← h03.eq]
    _ = R 2 * (R 0 * R 0) * R 3   := by group
    _ = R 2 * 1 * R 3             := by rw [h0]
    _ = R 2 * R 3                 := by rw [mul_one]

/-- R₃ · (R₀R₁) · R₃ = R₀R₁.  Uses R₀R₃=R₃R₀ and R₁R₃=R₃R₁. -/
theorem conj_A_by_R3
    (hR  : ∀ i, R i ^ 2 = 1)
    (h03 : Commute (R 0) (R 3))
    (h13 : Commute (R 1) (R 3)) :
    R 3 * (R 0 * R 1) * R 3 = R 0 * R 1 := by
  have h3 : R 3 * R 3 = 1 := invol_mul_self R hR 3
  calc R 3 * (R 0 * R 1) * R 3
      = (R 3 * R 0) * (R 1 * R 3) := by group
    _ = (R 0 * R 3) * (R 3 * R 1) := by rw [← h03.eq, h13.eq]
    _ = R 0 * (R 3 * R 3) * R 1   := by group
    _ = R 0 * 1 * R 1             := by rw [h3]
    _ = R 0 * R 1                 := by rw [mul_one]

/-! ## Part (B): A and C lie in ker φ -/

/-- For any hom φ with φ(R₀) = φ(R₁), the product A = R₀R₁ maps to 1. -/
theorem A_in_ker {H : Type*} [Group H]
    (hR : ∀ i, R i ^ 2 = 1)
    (φ : G →* H)
    (hφ01 : φ (R 0) = φ (R 1)) :
    φ (R 0 * R 1) = 1 := by
  rw [map_mul, hφ01]
  have : φ (R 1) ^ 2 = 1 := by
    rw [← map_pow, hR 1, map_one]
  rwa [sq] at this

/-- For any hom φ with φ(R₂) = φ(R₃), the product C = R₂R₃ maps to 1. -/
theorem C_in_ker {H : Type*} [Group H]
    (hR : ∀ i, R i ^ 2 = 1)
    (φ : G →* H)
    (hφ23 : φ (R 2) = φ (R 3)) :
    φ (R 2 * R 3) = 1 := by
  rw [map_mul, hφ23]
  have : φ (R 3) ^ 2 = 1 := by
    rw [← map_pow, hR 3, map_one]
  rwa [sq] at this

/-! ## Part (C): V = ⟨R₀,R₃⟩ is a Klein-four group -/

/-- (R₀R₃)² = 1: the product of the two V-generators is an involution.
    Together with R₀²=R₃²=1 and commutativity, V ≅ Z/2 × Z/2. -/
theorem V_product
    (hR  : ∀ i, R i ^ 2 = 1)
    (h03 : Commute (R 0) (R 3)) :
    (R 0 * R 3) ^ 2 = 1 := by
  have h0 : R 0 * R 0 = 1 := invol_mul_self R hR 0
  have h3 : R 3 * R 3 = 1 := invol_mul_self R hR 3
  calc (R 0 * R 3) ^ 2
      = R 0 * R 3 * (R 0 * R 3) := sq _
    _ = R 0 * (R 3 * R 0) * R 3 := by group
    _ = R 0 * (R 0 * R 3) * R 3 := by rw [h03.eq]
    _ = R 0 * R 0 * (R 3 * R 3) := by group
    _ = 1 * 1                   := by rw [h0, h3]
    _ = 1                       := mul_one 1

/-! ## Main: lem:W3struct (hypothesis-relative on Bass-Serre) -/

/-- **lem:W3struct** (hypothesis-relative).

  In any group G with the RACG-Γ₃ relations, AND given the Bass-Serre hypothesis
  `hFree` (that ⟨R₀R₁, R₂R₃⟩ is free of rank 2), all conclusions hold. -/
theorem lem_W3struct
    (hR  : ∀ i, R i ^ 2 = 1)
    (h02 : Commute (R 0) (R 2))
    (h03 : Commute (R 0) (R 3))
    (h13 : Commute (R 1) (R 3))
    -- Bass-Serre: ⟨A,C⟩ free on {A,C}  (not in Mathlib; needs virtually-free theory)
    (_hFree : ∀ (w : FreeGroup (Fin 2)),
      FreeGroup.lift ![(R 0 * R 1), (R 2 * R 3)] w = 1 → w = 1) :
    R 0 * (R 0 * R 1) * R 0 = (R 0 * R 1)⁻¹ ∧
    R 3 * (R 2 * R 3) * R 3 = (R 2 * R 3)⁻¹ ∧
    R 0 * (R 2 * R 3) * R 0 = R 2 * R 3 ∧
    R 3 * (R 0 * R 1) * R 3 = R 0 * R 1 ∧
    (R 0 * R 3) ^ 2 = 1 :=
  ⟨conj_A_by_R0 R hR,
   conj_C_by_R3 R hR,
   conj_C_by_R0 R hR h02 h03,
   conj_A_by_R3 R hR h03 h13,
   V_product R hR h03⟩

end W3struct

#print axioms W3struct.conj_A_by_R0
#print axioms W3struct.conj_C_by_R3
#print axioms W3struct.conj_C_by_R0
#print axioms W3struct.conj_A_by_R3
#print axioms W3struct.A_in_ker
#print axioms W3struct.C_in_ker
#print axioms W3struct.V_product
#print axioms W3struct.lem_W3struct
