/-
SylvesterNeg.lean
=================
A Sylvester-type bound that replaces Cauchy interlacing in `lem:isolate`
(`merged_novel_paper.tex`):

  For a real symmetric matrix `A`, any subspace `U` on which the quadratic form is strictly
  negative (away from `0`) has `dim U <= #{negative eigenvalues of A}`.

Proof: the map `U -> R^{neg}`, `x |-> (<b_i,x>)_{mu_i < 0}` is injective, since an `x` killed by it
has `x^T A x = sum_{mu_i >= 0} mu_i <b_i,x>^2 >= 0` by the spectral expansion.  No sorry.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace SylvesterNeg

open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Spectral expansion of the quadratic form. -/
theorem quad_eq_sum_eigen (A : Matrix m m ℝ) (hA : A.IsHermitian) (x : m → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * (⇑(hA.eigenvectorBasis i) ⬝ᵥ x) ^ 2 := by
  have hbasis : ∀ y z : m → ℝ,
      ∑ i, (⇑(hA.eigenvectorBasis i) ⬝ᵥ y) * (⇑(hA.eigenvectorBasis i) ⬝ᵥ z) = y ⬝ᵥ z := by
    intro y z
    have := hA.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa [PiLp.inner_apply, dotProduct, mul_comm] using this
  have hsym : Aᵀ = A := by
    have := hA.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hcoef : ∀ i, ⇑(hA.eigenvectorBasis i) ⬝ᵥ (A *ᵥ x) =
      hA.eigenvalues i * (⇑(hA.eigenvectorBasis i) ⬝ᵥ x) := by
    intro i
    have hv : (⇑(hA.eigenvectorBasis i)) ᵥ* A = A *ᵥ ⇑(hA.eigenvectorBasis i) := by
      rw [← vecMul_transpose, hsym]
    rw [dotProduct_mulVec, hv, hA.mulVec_eigenvectorBasis i, smul_dotProduct, smul_eq_mul]
  rw [← hbasis x (A *ᵥ x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcoef i]; ring

/-- A negative-definite subspace is no larger than the number of negative eigenvalues. -/
theorem finrank_neg_le (A : Matrix m m ℝ) (hA : A.IsHermitian) (U : Submodule ℝ (m → ℝ))
    (hU : ∀ x ∈ U, x ≠ 0 → x ⬝ᵥ (A *ᵥ x) < 0) :
    Module.finrank ℝ U ≤ Fintype.card {i // hA.eigenvalues i < 0} := by
  let Φ : U →ₗ[ℝ] ({i // hA.eigenvalues i < 0} → ℝ) :=
    { toFun := fun x i => ⇑(hA.eigenvectorBasis i.1) ⬝ᵥ (x : m → ℝ)
      map_add' := fun x y => by funext i; simp [dotProduct_add]
      map_smul' := fun c x => by funext i; simp [dotProduct_smul] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have hx0 : (x : m → ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hneg := hU x x.2 hx0
    rw [quad_eq_sum_eigen A hA] at hneg
    have hnn : 0 ≤ ∑ i, hA.eigenvalues i * (⇑(hA.eigenvectorBasis i) ⬝ᵥ (x : m → ℝ)) ^ 2 := by
      refine Finset.sum_nonneg fun i _ => ?_
      by_cases hi : hA.eigenvalues i < 0
      · have : ⇑(hA.eigenvectorBasis i) ⬝ᵥ (x : m → ℝ) = 0 := congrFun hx ⟨i, hi⟩
        rw [this]; simp
      · exact mul_nonneg (not_lt.mp hi) (sq_nonneg _)
    linarith
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

end SylvesterNeg

#print axioms SylvesterNeg.finrank_neg_le
