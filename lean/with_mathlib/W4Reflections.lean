/-
  W4Reflections.lean
  ==================
  The explicit `5x5`-generator, `4x4`-matrix reflection representation of `W_4` used in
  `merged_novel_paper.tex` for Theorems `thm:family4`, `thm:family4b`, `thm:family4c`.

  Source of the construction (paper, `lem:Kplus`(ii), citing `lem:normals` of the `orthoscheme`
  paper, formalised combinatorially -- support pattern only, no matrices -- in
  `OrthoschemeNormals.lean`): for legs `a_1,...,a_4 > 0` the facet normals of the `4`-orthoscheme
  `O(a)` are

      m_0 = e_1,
      m_1 = a_2 e_1 - a_1 e_2,
      m_2 = a_3 e_2 - a_2 e_3,
      m_3 = a_4 e_3 - a_3 e_4,
      m_4 = e_4,

  in `R^4` with the *standard* inner product (the ambient reduction `prop:reduce` is precisely
  what lets the point-group generators be read as ordinary Householder reflections in `O(4)`,
  rather than as reflections for the `5x5` Lorentzian Gram form `G(c(a))` on the root space).  The
  generator `R_i in O(4)` is the Householder reflection in `m_i`:

      R_i (x) = x - 2 * (x . m_i) / (m_i . m_i) * m_i,

  i.e. as a matrix, `R_i = 1 - (2 / (m_i . m_i)) • (m_i m_i^T)`.  This is `pi(rho_a(R_i))`, the
  linear part of the point-group image of the `i`-th Coxeter generator, which is exactly the
  object `thm:family4`/`thm:family4b`/`thm:family4c` compute with.

  What is proved here:
  * a general Householder-reflection identity for any nonzero-norm vector in `Fin n -> K`
    (`reflectMatrix_mul_self`: the matrix squares to `1`), specialised to give `R_i * R_i = 1`
    for each of the five `W_4` generators;
  * `reflectMatrix` is symmetric, so `R_i` is orthogonal for the standard form:
    `R_i^T * R_i = 1` (`reflectMatrix_orthogonal`), the "preserves the form" sanity check;
  * the four generator instances `R0, R1, R2, R3, R4` as explicit `Matrix (Fin 4) (Fin 4) K`.

  The top-level claim of `thm:family4`/`4b`/`4c` -- multiplying out the two fixed words
  (length 8 and length 12 respectively) in these generators and checking that the entrywise
  difference of the linear parts is divisible by `famI`/`famII`/`famIII` from
  `OrthoschemeLoci.lean` -- is NOT attempted here: each word product is 8-12 `4x4` matrix
  multiplications with rational-function entries in `a1,...,a4` (division by three distinct
  quadratic norms), which is a large but mechanical `field_simp`/`ring` computation left for a
  follow-up session. What is banked is the generator infrastructure itself, so that computation
  can be stated and attempted directly against `R0,...,R4` below.
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

namespace W4Reflections

open Matrix

/-! ### 1. A general Householder-reflection identity -/

variable {K : Type*} [Field K] {n : ℕ}

/-- The outer product `v w^T` of two vectors, as a matrix. -/
def outerProd (v w : Fin n → K) : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => v i * w j

/-- The Householder reflection matrix in the vector `v`, given (not computed) its squared norm
    `c`. Intended use: `c = dotProduct v v`. -/
def reflectMatrix (v : Fin n → K) (c : K) : Matrix (Fin n) (Fin n) K :=
  (1 : Matrix (Fin n) (Fin n) K) - (2 / c) • outerProd v v

/-- `outerProd v v * outerProd v v = (dotProduct v v) • outerProd v v`: the outerProd product of a vector with
    itself is idempotent up to the scalar `dotProduct v v`. -/
theorem outer_mul_outer (v : Fin n → K) :
    outerProd v v * outerProd v v = (dotProduct v v) • outerProd v v := by
  ext i k
  simp only [outerProd, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct]
  rw [Finset.sum_mul]
  have : ∀ j, v i * v j * (v j * v k) = v j * v j * (v i * v k) := fun j => by ring
  simp_rw [this]

/-- **The Householder involution.** If `c` is the (nonzero) squared norm of `v`, the reflection
    matrix in `v` squares to the identity. -/
theorem reflectMatrix_mul_self (v : Fin n → K) (c : K) (hc : c ≠ 0)
    (hcv : c = dotProduct v v) :
    reflectMatrix v c * reflectMatrix v c = 1 := by
  have hO : outerProd v v * outerProd v v = c • outerProd v v := by
    rw [hcv]; exact outer_mul_outer v
  have hsc : (2 / c : K) * c = 2 := by field_simp
  simp only [reflectMatrix, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, hO, smul_smul, hsc]
  module

/-- `outerProd v v` is symmetric. -/
theorem outerProd_transpose (v : Fin n → K) : (outerProd v v)ᵀ = outerProd v v := by
  ext i j; simp only [outerProd, Matrix.transpose_apply, Matrix.of_apply]; ring

/-- `reflectMatrix v c` is a symmetric matrix. -/
theorem reflectMatrix_transpose (v : Fin n → K) (c : K) :
    (reflectMatrix v c)ᵀ = reflectMatrix v c := by
  simp [reflectMatrix, outerProd_transpose]

/-- **Preserves the standard form.** A Householder reflection is orthogonal for the standard
    inner product: `R^T * R = 1`. This is the "preserves the (identity) Gram form" sanity check
    for the ambient-`O(4)` reflections, since here `G = 1`. -/
theorem reflectMatrix_orthogonal (v : Fin n → K) (c : K) (hc : c ≠ 0)
    (hcv : c = dotProduct v v) :
    (reflectMatrix v c)ᵀ * reflectMatrix v c = 1 := by
  rw [reflectMatrix_transpose]
  exact reflectMatrix_mul_self v c hc hcv

/-! ### 2. The five `W_4` generators

    Legs `a1, a2, a3, a4`, facet normals `m_0, ..., m_4 : Fin 4 -> K`, generators
    `R_0, ..., R_4 : Matrix (Fin 4) (Fin 4) K`, matching `pi(rho_a(R_i))` of
    `merged_novel_paper.tex`, `lem:Kplus`(ii) / `lem:normals`. -/

variable (a1 a2 a3 a4 : K)

/-- `m_0 = e_1`. -/
def m0 : Fin 4 → K := ![1, 0, 0, 0]

/-- `m_1 = a_2 e_1 - a_1 e_2`. -/
def m1 : Fin 4 → K := ![a2, -a1, 0, 0]

/-- `m_2 = a_3 e_2 - a_2 e_3`. -/
def m2 : Fin 4 → K := ![0, a3, -a2, 0]

/-- `m_3 = a_4 e_3 - a_3 e_4`. -/
def m3 : Fin 4 → K := ![0, 0, a4, -a3]

/-- `m_4 = e_4`. -/
def m4 : Fin 4 → K := ![0, 0, 0, 1]

/-- The squared norms of the five normals: `1`, `a1^2+a2^2`, `a2^2+a3^2`, `a3^2+a4^2`, `1`. -/
theorem dotProduct_m0 : dotProduct (m0 (K := K)) (m0 (K := K)) = 1 := by
  simp [m0, dotProduct, Fin.sum_univ_four]

theorem dotProduct_m1 : dotProduct (m1 a1 a2) (m1 a1 a2) = a1 ^ 2 + a2 ^ 2 := by
  simp [m1, dotProduct, Fin.sum_univ_four]; ring

theorem dotProduct_m2 : dotProduct (m2 a2 a3) (m2 a2 a3) = a2 ^ 2 + a3 ^ 2 := by
  simp [m2, dotProduct, Fin.sum_univ_four]; ring

theorem dotProduct_m3 : dotProduct (m3 a3 a4) (m3 a3 a4) = a3 ^ 2 + a4 ^ 2 := by
  simp [m3, dotProduct, Fin.sum_univ_four]; ring

theorem dotProduct_m4 : dotProduct (m4 (K := K)) (m4 (K := K)) = 1 := by
  simp [m4, dotProduct, Fin.sum_univ_four]

/-- `R_0`, the Householder reflection in `m_0 = e_1`. -/
def R0 : Matrix (Fin 4) (Fin 4) K := reflectMatrix (m0 (K := K)) 1

/-- `R_1`, the Householder reflection in `m_1 = a_2 e_1 - a_1 e_2`. -/
def R1 : Matrix (Fin 4) (Fin 4) K := reflectMatrix (m1 a1 a2) (a1 ^ 2 + a2 ^ 2)

/-- `R_2`, the Householder reflection in `m_2 = a_3 e_2 - a_2 e_3`. -/
def R2 : Matrix (Fin 4) (Fin 4) K := reflectMatrix (m2 a2 a3) (a2 ^ 2 + a3 ^ 2)

/-- `R_3`, the Householder reflection in `m_3 = a_4 e_3 - a_3 e_4`. -/
def R3 : Matrix (Fin 4) (Fin 4) K := reflectMatrix (m3 a3 a4) (a3 ^ 2 + a4 ^ 2)

/-- `R_4`, the Householder reflection in `m_4 = e_4`. -/
def R4 : Matrix (Fin 4) (Fin 4) K := reflectMatrix (m4 (K := K)) 1

/-! ### 3. Warmup: each generator is an involution preserving the standard form -/

theorem R0_sq : R0 (K := K) * R0 (K := K) = 1 :=
  reflectMatrix_mul_self _ 1 one_ne_zero (dotProduct_m0 (K := K)).symm

theorem R0_orthogonal : (R0 (K := K))ᵀ * R0 (K := K) = 1 :=
  reflectMatrix_orthogonal _ 1 one_ne_zero (dotProduct_m0 (K := K)).symm

theorem R1_sq (h : a1 ^ 2 + a2 ^ 2 ≠ 0) : R1 a1 a2 * R1 a1 a2 = 1 :=
  reflectMatrix_mul_self _ _ h (dotProduct_m1 a1 a2).symm

theorem R1_orthogonal (h : a1 ^ 2 + a2 ^ 2 ≠ 0) : (R1 a1 a2)ᵀ * R1 a1 a2 = 1 :=
  reflectMatrix_orthogonal _ _ h (dotProduct_m1 a1 a2).symm

theorem R2_sq (h : a2 ^ 2 + a3 ^ 2 ≠ 0) : R2 a2 a3 * R2 a2 a3 = 1 :=
  reflectMatrix_mul_self _ _ h (dotProduct_m2 a2 a3).symm

theorem R2_orthogonal (h : a2 ^ 2 + a3 ^ 2 ≠ 0) : (R2 a2 a3)ᵀ * R2 a2 a3 = 1 :=
  reflectMatrix_orthogonal _ _ h (dotProduct_m2 a2 a3).symm

theorem R3_sq (h : a3 ^ 2 + a4 ^ 2 ≠ 0) : R3 a3 a4 * R3 a3 a4 = 1 :=
  reflectMatrix_mul_self _ _ h (dotProduct_m3 a3 a4).symm

theorem R3_orthogonal (h : a3 ^ 2 + a4 ^ 2 ≠ 0) : (R3 a3 a4)ᵀ * R3 a3 a4 = 1 :=
  reflectMatrix_orthogonal _ _ h (dotProduct_m3 a3 a4).symm

theorem R4_sq : R4 (K := K) * R4 (K := K) = 1 :=
  reflectMatrix_mul_self _ 1 one_ne_zero (dotProduct_m4 (K := K)).symm

theorem R4_orthogonal : (R4 (K := K))ᵀ * R4 (K := K) = 1 :=
  reflectMatrix_orthogonal _ 1 one_ne_zero (dotProduct_m4 (K := K)).symm

/-- Over `ℝ` with positive legs (the actual setting of `thm:family4`/`4b`/`4c`), the three
    interior nonzero-norm hypotheses above hold automatically. Packaged once for convenience. -/
theorem interior_norms_ne_zero {a1 a2 a3 a4 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < a4) :
    a1 ^ 2 + a2 ^ 2 ≠ 0 ∧ a2 ^ 2 + a3 ^ 2 ≠ 0 ∧ a3 ^ 2 + a4 ^ 2 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> positivity

/-! ### 4. Status

    `R0,...,R4` above are exactly `pi(rho_a(R_i))` for the `W_4` point-group representation of
    `merged_novel_paper.tex`. The families `thm:family4`/`4b`/`4c` are the statement that

      w1 a1 a2 a3 a4 - w2 a1 a2 a3 a4 = 0  (entrywise, as elements of a field of fractions)

    is divisible, entrywise, by `OrthoschemeLoci.famI` / `famII` / `famIII` respectively, where
    `w1`, `w2` are the length-8 (resp. length-12, length-12) products of `R0,...,R4` given in the
    theorem statements. That computation -- literally substituting `R0,...,R4` above and
    multiplying out -- is not carried out in this file; it is the natural next step once this
    generator infrastructure is in place. -/

end W4Reflections

