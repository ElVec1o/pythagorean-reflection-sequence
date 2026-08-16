/-
  TransferChain.lean
  ==================
  The exact structure of the travel and bulk transfer chains.

  The travel recursion
      A_{s+1} = (1 + 2 q^{1+2s}) A_s + 2 q^{1+s} B_s
      B_{s+1} = -2 q^{1+3s} A_s + (1 - 2 q^{1+2s}) B_s
  and the bulk recursion, the same with the prefactor 2q replaced by 2, are transfer chains.
  This file proves, over an arbitrary commutative ring, the three facts the analysis rests on:

    * the transfer matrices have determinant 1, so the chain lies in SL_2 and the discrete
      Wronskian is conserved (this is what makes variation of parameters exact);
    * each is I + c N with N nilpotent of square zero, so the increments are unipotent;
    * the bulk matrix is the travel matrix at half-shifted index, conjugated by a CONSTANT
      diagonal.  This is the precise form of the statement that the zeros of S_e and of
      1 - Sigma_1 are those of one q-cosine sampled a half q-step apart.

  Everything here is polynomial identity, stated with the substitutions that make the half-step
  literal: writing the travel matrix in terms of  a = q^s  and the bulk in terms of  b = q^t,
  the half shift is  a = b / r  with  r^2 = q, i.e. r = q^{1/2}.  To keep the statement inside a
  ring with no square roots we carry r as a variable satisfying r^2 = q, which is exactly the
  x = q^{1/2} of the paper.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

namespace TransferChain

variable {R : Type*} [CommRing R]

/-- Travel transfer matrix, in terms of `q` and `a = q^s`.
    Entries: `1 + 2 q a^2`, `2 q a`, `-2 q a^3`, `1 - 2 q a^2`. -/
def travel (q a : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1 + 2*q*a^2, 2*q*a; -2*q*a^3, 1 - 2*q*a^2]

/-- Bulk transfer matrix, in terms of `q` and `b = q^t`.  Same shape with the prefactor `2q`
    replaced by `2`. -/
def bulk (b : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1 + 2*b^2, 2*b; -2*b^3, 1 - 2*b^2]

/-- **Determinant one.**  The travel chain lies in `SL_2`, so the discrete Wronskian is
    conserved along it. -/
theorem det_travel (q a : R) : (travel q a).det = 1 := by
  simp [travel, Matrix.det_fin_two_of]; ring

/-- **Determinant one** for the bulk chain. -/
theorem det_bulk (b : R) : (bulk b).det = 1 := by
  simp [bulk, Matrix.det_fin_two_of]; ring

/-- Increment form, written without inverses. -/
theorem travel_sub_one (q a : R) :
    travel q a - 1 = !![2*q*a^2, 2*q*a; -2*q*a^3, -(2*q*a^2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [travel, Matrix.one_apply] <;> ring

/-- **The increment squares to zero.**  With `N = !![a, 1; -a^2, -a]` scaled by `2 q a`, the
    travel matrix is `1 + (2 q a) • N`, and `N * N = 0`. -/
theorem nilpotent_travel (a : R) :
    (!![a, 1; -a^2, -a] : Matrix (Fin 2) (Fin 2) R) * !![a, 1; -a^2, -a] = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The travel matrix is `1` plus `2 q a` times that nilpotent. -/
theorem travel_eq (q a : R) :
    travel q a = 1 + (2*q*a) • (!![a, 1; -a^2, -a] : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [travel, Matrix.one_apply] <;> ring

/-- The bulk matrix is `1` plus `2 b` times the same nilpotent shape. -/
theorem bulk_eq (b : R) :
    bulk b = 1 + (2*b) • (!![b, 1; -b^2, -b] : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bulk, Matrix.one_apply] <;> ring

/-- **The half-shift identity.**  Write `r` for `q^{1/2}`, so `q = r*r`, and let `a = q^s` be
    the travel argument.  Then the bulk chain evaluated at `b = a*r`, that is at the argument
    shifted by half a step, is the travel chain at `a` conjugated by the CONSTANT diagonal
    `D = diag(1, r)`:
        `D * travel (r*r) a = bulk (a*r) * D`.
    No hypothesis is needed; this is an identity in the polynomial ring.  It is the precise form
    of the statement that the zeros of `S_e` and of `1 - Sigma_1` are those of one q-cosine
    sampled a half q-step apart: the two chains differ by a half step in the index and a
    constant conjugation, and by nothing else. -/
theorem half_shift (r a : R) :
    (!![1, 0; 0, r] : Matrix (Fin 2) (Fin 2) R) * travel (r*r) a
      = bulk (a*r) * !![1, 0; 0, r] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [travel, bulk, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-! ### Axiom audit (Rule 5) -/

#print axioms det_travel
#print axioms det_bulk
#print axioms nilpotent_travel
#print axioms travel_eq
#print axioms bulk_eq
#print axioms half_shift

end TransferChain
