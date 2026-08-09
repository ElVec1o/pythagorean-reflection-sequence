/-
  ModularRankCertificate.lean
  ===========================
  The bridge that turns a modular left inverse into a statement about rational solutions.

  This is the missing step of `prop:no-dfinite` in paper "extra".  A D-finite recurrence of
  order k and coefficient degree m is a nonzero solution of a HOMOGENEOUS linear system, so
  non-existence is exactly full column rank.  The certificates produced by
  `code/zeta_probe/tools/nodfinite` exhibit, for each parameter pair, a square submatrix M of
  the coefficient matrix together with an integer matrix Minv satisfying

      Minv * M = I    (mod p),      p = 2^31 - 1.

  What has to be established is that such a certificate forces M x = 0 to have only the zero
  solution OVER THE RATIONALS.  The argument is short and is proved here in full generality,
  for an arbitrary size and an arbitrary modulus greater than one:

    * reducing the identity modulo p and taking determinants gives
      det(Minv) * det(M) = 1 in ZMod p, so det M is nonzero mod p;
    * an integer whose reduction is nonzero is itself nonzero, so det M /= 0 in Z;
    * det M /= 0 persists under the embedding Z -> Q, and a square matrix over a field with
      nonzero determinant has trivial kernel.

  Reduction can only lower rank, which is why the implication runs in the useful direction: a
  MODULAR certificate PROVES a RATIONAL statement.  A modular search would only be evidence;
  a modular certificate is a proof.

  Worth recording, because an earlier plan got this wrong: NO DENOMINATOR CLEARING IS NEEDED.
  It is tempting to argue via a primitive integer solution and descent, which would require
  the denominator-clearing lemma that paper 5 also needs.  Going through the determinant
  avoids that entirely, so this file has no dependency on that lemma.

  The concrete certificates are not instantiated here; this file supplies the general
  implication that consumes them, and `DFiniteReduction.no_dfinite_of_maximal` supplies the
  reduction from 52 parameter pairs to 6.
-/

import Mathlib

namespace ModularRankCertificate

open Matrix

variable {n : ℕ} {p : ℕ}

/-- **A modular left inverse forces a nonzero determinant.**  If `Minv * M` reduces to the
    identity modulo `p`, then `det M` is nonzero as an integer. -/
theorem det_ne_zero_of_modular_left_inverse [Fact (1 < p)]
    (Minv M : Matrix (Fin n) (Fin n) ℤ)
    (h : (Minv * M).map (Int.castRingHom (ZMod p)) = 1) :
    M.det ≠ 0 := by
  intro hdet
  have hone : ((Int.castRingHom (ZMod p)).mapMatrix (Minv * M)).det = 1 := by
    rw [RingHom.mapMatrix_apply, h, Matrix.det_one]
  rw [← RingHom.map_det] at hone
  rw [Matrix.det_mul, hdet, mul_zero, map_zero] at hone
  exact zero_ne_one hone

/-- The determinant stays nonzero after embedding the integers in the rationals. -/
theorem det_ne_zero_rat (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det ≠ 0) :
    (M.map (Int.castRingHom ℚ)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simpa using hM

/-- **The certificate kills every rational solution.**  This is the statement the exclusion
    searches need: a modular left inverse certifies that the homogeneous system has only the
    trivial solution over `Q`. -/
theorem eq_zero_of_modular_left_inverse [Fact (1 < p)]
    (Minv M : Matrix (Fin n) (Fin n) ℤ)
    (h : (Minv * M).map (Int.castRingHom (ZMod p)) = 1)
    (x : Fin n → ℚ)
    (hx : (M.map (Int.castRingHom ℚ)).mulVec x = 0) :
    x = 0 := by
  have hdet : M.det ≠ 0 := det_ne_zero_of_modular_left_inverse Minv M h
  exact Matrix.eq_zero_of_mulVec_eq_zero (det_ne_zero_rat M hdet) hx

/-- Contrapositive form, which is how an exclusion result is usually stated: no NONZERO
    rational vector is annihilated. -/
theorem no_nonzero_solution [Fact (1 < p)]
    (Minv M : Matrix (Fin n) (Fin n) ℤ)
    (h : (Minv * M).map (Int.castRingHom (ZMod p)) = 1) :
    ¬ ∃ x : Fin n → ℚ, x ≠ 0 ∧ (M.map (Int.castRingHom ℚ)).mulVec x = 0 := by
  rintro ⟨x, hne, hx⟩
  exact hne (eq_zero_of_modular_left_inverse Minv M h x hx)

/-! ### Passing from a submatrix to the full system

    A certificate is exhibited on a square SUBMATRIX of the tall coefficient matrix `A`: the
    rows chosen by the search.  Any solution of the full system solves the subsystem, so
    triviality for the submatrix gives triviality for `A`.  `rows` is the chosen selection. -/

theorem no_nonzero_solution_of_submatrix [Fact (1 < p)] {r : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (rows : Fin n → Fin r)
    (Minv : Matrix (Fin n) (Fin n) ℤ)
    (h : (Minv * A.submatrix rows id).map (Int.castRingHom (ZMod p)) = 1)
    (x : Fin n → ℚ)
    (hx : (A.map (Int.castRingHom ℚ)).mulVec x = 0) :
    x = 0 := by
  refine eq_zero_of_modular_left_inverse Minv (A.submatrix rows id) h x ?_
  funext i
  have h2 := congrFun hx (rows i)
  simp only [Pi.zero_apply] at h2 ⊢
  exact h2

/-! ### Axiom audit (Rule 5) -/

#print axioms det_ne_zero_of_modular_left_inverse
#print axioms det_ne_zero_rat
#print axioms eq_zero_of_modular_left_inverse
#print axioms no_nonzero_solution
#print axioms no_nonzero_solution_of_submatrix

end ModularRankCertificate
