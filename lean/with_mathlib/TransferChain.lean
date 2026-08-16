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


/-! ### The scalar three-term recursion

    Eliminating `B` between the two travel recursions leaves a three-term recursion for `A`
    alone.  This is exact: no continuum limit, no asymptotics.  It is a `q`-difference equation
    of Hahn--Exton type, which is why a `q`-cosine governs the chain.  Note the trailing
    coefficient is the constant `-q`, and the middle coefficient tends to `1+q` as the index
    grows, whose characteristic roots are `1` and `q`; that is why `A` converges, its limit
    being `Sigma_0`. -/

/-- One step of the travel chain on the pair `(A,B)`, with `a = q^s`. -/
def stepA (q a A B : R) : R := (1 + 2*q*a^2) * A + 2*q*a * B
/-- The `B` component of one step. -/
def stepB (q a A B : R) : R := -2*q*a^3 * A + (1 - 2*q*a^2) * B

/-- **The exact three-term recursion.**  Writing `A_s, A_{s+1}, A_{s+2}` for three consecutive
    values of the `A` component, with `a = q^s` so that the next argument is `q*a`,
        `A_{s+2} = (1 + q - 2 q^2 a^2 (1 - q)) A_{s+1} - q A_s`.
    Here `A_{s+1} = stepA q a A B` and `A_{s+2} = stepA q (q*a) A_{s+1} B_{s+1}` with
    `B_{s+1} = stepB q a A B`. -/
theorem three_term (q a A B : R) :
    stepA q (q*a) (stepA q a A B) (stepB q a A B)
      = (1 + q - 2*q^2*a^2*(1-q)) * (stepA q a A B) - q * A := by
  simp only [stepA, stepB]
  ring

#print axioms three_term


/-! ### The Casoratian of the scalar recursion

    For the three-term recursion `A_{s+2} = p_s A_{s+1} - q A_s`, the trailing coefficient is
    the CONSTANT `-q`, so the Casoratian of two solutions satisfies `W_{s+1} = q W_s`, hence
    `W_s = q^s W_0` exactly.  This is the discrete analogue of a Wronskian with constant
    logarithmic derivative, and it is the ingredient that makes variation of parameters explicit
    for the inhomogeneous (bulk) chain. -/

/-- **Casoratian identity.**  If `A2 = p*A1 - q*A0` and `B2 = p*B1 - q*B0` are the next values
    of two solutions of the same three-term recursion, then the Casoratian is multiplied by `q`
    at each step.  Note the middle coefficient `p` cancels, so this holds for every `p` and in
    particular for the `s`-dependent one of `three_term`. -/
theorem casoratian_step (q p A0 A1 B0 B1 : R) :
    (p*A1 - q*A0) * B1 - A1 * (p*B1 - q*B0) = q * (A1*B0 - A0*B1) := by
  ring

/-- Iterated form: after `n` steps the Casoratian has picked up `q^n`. -/
theorem casoratian_pow (q : R) (W : ℕ → R) (h : ∀ n, W (n+1) = q * W n) :
    ∀ n, W n = q^n * W 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih => rw [h k, ih]; ring

#print axioms casoratian_step
#print axioms casoratian_pow


/-! ### The bulk scalar recursion

    The same elimination on the bulk chain, which carries a source, gives the SAME three-term
    recursion with the index shifted by a half step (as `half_shift` predicts) plus a single
    geometric inhomogeneous term.  The source is one term, not a sum: that is what makes the
    Green's function for the bulk explicit. -/

/-- One step of the bulk chain on `(A,B)`, with `c = q^b` and source strength `f`. -/
def bstepA (q c A B f : R) : R := (1 + 2*c^2) * A + 2*c * B + 2*c*f
/-- The `B` component of one bulk step. -/
def bstepB (q c A B f : R) : R := -2*c^3 * A + (1 - 2*c^2) * B - 2*c^2*f

/-- **The bulk three-term recursion.**  With `c = q^b`, `f_b = 1 + g c beta` and
    `f_{b+1} = 1 + g q c beta`,
        `A_{b+2} = (1 + q - 2 q c^2 (1-q)) A_{b+1} - q A_b - 2 beta g q c^2 (1-q)`.
    The middle coefficient is the travel one at the half-shifted index and the source is the
    single geometric term shown. -/
theorem bulk_three_term (q c g beta A B : R) :
    bstepA q (q*c) (bstepA q c A B (1 + g*c*beta)) (bstepB q c A B (1 + g*c*beta))
      (1 + g*(q*c)*beta)
      = (1 + q - 2*q*c^2*(1-q)) * (bstepA q c A B (1 + g*c*beta)) - q * A
        - 2*beta*g*q*c^2*(1-q) := by
  simp only [bstepA, bstepB]
  ring

#print axioms bulk_three_term

/-! ### Axiom audit (Rule 5) -/

#print axioms det_travel
#print axioms det_bulk
#print axioms nilpotent_travel
#print axioms travel_eq
#print axioms bulk_eq
#print axioms half_shift

end TransferChain
