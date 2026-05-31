/-
  SchurGeneral.lean
  =================

  Toward a general-n proof of the Schur-complement determinant identity

      det Q_n  =  - prod (a_1^2, ..., a_n^2)

  for the (n+1) × (n+1) Lorentzian Gram matrix Q_n of the n-dim
  right-corner orthoscheme.

  Approach: derive a closed form D_k = P_k * (1 - S_{k+1}) for the
  leading principal minors D_k of Q_n, satisfying the tridiagonal
  recurrence

      D_k  =  (a_k^2 + a_{k+1}^2) * D_{k-1}  -  (a_{k-1} a_{k+1})^2 * D_{k-2}

  This file proves the uniform inductive step as a single polynomial
  identity in 5 variables (a_{k-1}, a_k, a_{k+1}, S_{k-1}, P_{k-2}),
  and the final boundary step that gives D_n = -P_n.

  The polynomial identities are dispatched by Mathlib's `ring` tactic.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring

namespace SchurGeneral

/-- The uniform inductive step of the closed-form proof.

    Substituting the closed form
        D_{k-1} = P_{k-2} a_{k-1}^2 (1 - S_k)        where S_k = S_{k-1} + a_k^2
        D_{k-2} = P_{k-2} (1 - S_{k-1})
    into the recurrence
        D_k = (a_k^2 + a_{k+1}^2) D_{k-1} - (a_{k-1} a_{k+1})^2 D_{k-2}
    we recover the claimed closed form
        D_k = P_k (1 - S_{k+1})    where S_{k+1} = S_{k-1} + a_k^2 + a_{k+1}^2
                                         and  P_k = P_{k-2} * a_{k-1}^2 * a_k^2.

    This is a uniform 5-variable polynomial identity. -/
theorem schur_inductive_step
    {R : Type*} [CommRing R]
    (a_km1 a_k a_kp1 S_km1 P_km2 : R) :
    -- LHS: D_k (claim)
    P_km2 * a_km1^2 * a_k^2 * (1 - (S_km1 + a_k^2 + a_kp1^2))
    =
    -- RHS of recurrence
    (a_k^2 + a_kp1^2) * (P_km2 * a_km1^2 * (1 - (S_km1 + a_k^2)))
    - (a_km1 * a_kp1)^2 * (P_km2 * (1 - S_km1)) := by
  ring

/-- The boundary step (k = n).

    For the last principal minor we use the boundary entries
        Q_n[n, n]   = 1     (not a_n^2 + a_{n+1}^2)
        Q_n[n-1, n] = a_{n-1}    (not a_{n-1} a_{n+1})
    so the recurrence reads
        D_n = 1 * D_{n-1} - a_{n-1}^2 * D_{n-2}.

    Substituting the closed forms
        D_{n-1} = P_{n-1} (1 - S_n) = P_{n-2} a_{n-1}^2 (1 - S_{n-1} - a_n^2)
        D_{n-2} = P_{n-2} (1 - S_{n-1})
    we get
        D_n = - P_{n-2} a_{n-1}^2 a_n^2 = - P_n.

    This is again a uniform polynomial identity. -/
theorem schur_boundary_step
    {R : Type*} [CommRing R]
    (a_nm1 a_n S_nm1 P_nm2 : R) :
    -- LHS: D_n (claim) = -P_n
    - (P_nm2 * a_nm1^2 * a_n^2)
    =
    -- RHS of boundary recurrence
    1 * (P_nm2 * a_nm1^2 * (1 - (S_nm1 + a_n^2)))
    - a_nm1^2 * (P_nm2 * (1 - S_nm1)) := by
  ring

/-- Base case k = 1:  D_1 = a_1^2 * (1 - a_1^2 - a_2^2) = P_1 * (1 - S_2). -/
theorem schur_base_step
    {R : Type*} [CommRing R]
    (a_1 a_2 : R) :
    a_1^2 * (1 - a_1^2 - a_2^2)
    =
    -- (a_1^2 + a_2^2) * D_0 - Q[0,1]^2 * D_{-1}
    -- D_0 = 1 - a_1^2, D_{-1} = 1, Q[0,1] = a_2
    (a_1^2 + a_2^2) * (1 - a_1^2) - a_2^2 * 1 := by
  ring

/-- Special case k = 2 (where Q[1,2] = a_1 a_3 enters):
    D_2 = a_1^2 a_2^2 (1 - a_1^2 - a_2^2 - a_3^2). -/
theorem schur_k2_step
    {R : Type*} [CommRing R]
    (a_1 a_2 a_3 : R) :
    a_1^2 * a_2^2 * (1 - a_1^2 - a_2^2 - a_3^2)
    =
    (a_2^2 + a_3^2) * (a_1^2 * (1 - a_1^2 - a_2^2)) - (a_1 * a_3)^2 * (1 - a_1^2) := by
  ring

end SchurGeneral

/-! ## Summary of what is proved here

  The four theorems above together formalize the algebraic content of
  the closed-form proof of the Schur-complement determinant identity:

      schur_base_step     :  D_1 closed form
      schur_k2_step       :  D_2 closed form (special case where
                              Q[1,2] = a_1 a_3 first enters)
      schur_inductive_step:  D_k closed form (uniform inductive step,
                              k >= 3, before the boundary)
      schur_boundary_step :  D_n = -P_n (final step using Q[n,n] = 1)

  All four are dispatched in milliseconds by the `ring` tactic.

  To convert these into a fully formalized det(Q_n) = -prod(a_i^2) one
  needs to additionally:

    (a) define Q_n as a Matrix (Fin (n+1)) (Fin (n+1)) over Z[a_1,...,a_n];
    (b) prove Q_n is symmetric tridiagonal with the claimed entries;
    (c) prove the tridiagonal expansion det(M[:k+1,:k+1]) = M[k,k] *
        det(M[:k,:k]) - M[k-1,k]^2 * det(M[:k-1,:k-1]) for symmetric
        tridiagonal matrices;
    (d) combine (a)-(c) with the four theorems above by induction on k.

  Steps (a) and (b) are straightforward in Mathlib.  Step (c) is the
  classical tridiagonal-determinant recurrence; Mathlib has the building
  blocks (Matrix.det_succ_row_zero etc.) but not the recurrence as a
  packaged lemma.  Step (d) is a Nat induction whose individual steps
  are the four theorems above.

  The four theorems machine-check the ALGEBRA of the proof.  The remaining
  matrix-theoretic plumbing is mechanical bookkeeping that does not
  introduce any additional content. -/
