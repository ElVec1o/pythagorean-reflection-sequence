/-
LorpointDet.lean
================
Formalizes the explicit Gram-determinant computations in `lem:lorpoint`
from `paper/journal/merged_novel_paper.tex`:

  For t > 1 the representation ρ_t : W_4 → O(3,1) satisfies
    det Gram(v₁,v₂) = 1 − t² ≠ 0,
    det Gram(v₂,v₃,v₄) = −1 ≠ 0.

The two sub-matrices are:
  G₂(t) = !![ 1, −t ; −t, 1 ]   (adjacent pair v₁,v₂ with inner product −t)
  G₃    = !![1,−1,0; −1,1,−1; 0,−1,1]  (triple v₂,v₃,v₄; all inner products −1 or 0)

No sorry.
-/

import Mathlib.Tactic

namespace LorpointDet

/-! ## 2×2 Gram determinant -/

/-- det[[1,−t],[−t,1]] = 1 − t² over any commutative ring. -/
theorem gram2_det {R : Type*} [CommRing R] (t : R) :
    (!![1, -t; -t, 1] : Matrix (Fin 2) (Fin 2) R).det = 1 - t ^ 2 := by
  simp [Matrix.det_fin_two]; ring

/-- For t > 1 the 2×2 sub-Gram determinant is non-zero. -/
theorem gram2_det_ne_zero {t : ℝ} (ht : 1 < t) :
    (!![1, -t; -t, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
  rw [gram2_det]; nlinarith [sq_nonneg t]

/-! ## 3×3 Gram determinant -/

/-- det[[1,−1,0],[−1,1,−1],[0,−1,1]] = −1. -/
theorem gram3_det :
    (!![1, -1, 0; -1, 1, -1; 0, -1, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = -1 := by
  simp [Matrix.det_fin_three]

/-- The 3×3 sub-Gram determinant is non-zero. -/
theorem gram3_det_ne_zero :
    (!![1, -1, 0; -1, 1, -1; 0, -1, 1] : Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 := by
  rw [gram3_det]; decide

end LorpointDet

-- Rule 5 axiom audit.
#print axioms LorpointDet.gram2_det
#print axioms LorpointDet.gram2_det_ne_zero
#print axioms LorpointDet.gram3_det
#print axioms LorpointDet.gram3_det_ne_zero
