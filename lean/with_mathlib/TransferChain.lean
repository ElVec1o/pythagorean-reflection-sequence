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
  fin_cases i <;> fin_cases j <;> simp [travel]

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
  fin_cases i <;> fin_cases j <;> simp [travel] <;> ring

/-- The bulk matrix is `1` plus `2 b` times the same nilpotent shape. -/
theorem bulk_eq (b : R) :
    bulk b = 1 + (2*b) • (!![b, 1; -b^2, -b] : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bulk] <;> ring

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
def bstepA (_q c A B f : R) : R := (1 + 2*c^2) * A + 2*c * B + 2*c*f
/-- The `B` component of one bulk step. -/
def bstepB (_q c A B f : R) : R := -2*c^3 * A + (1 - 2*c^2) * B - 2*c^2*f

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


/-! ### The bulk source is absorbed by a constant

    The inhomogeneous term of the bulk recursion is `-2 beta g q c^2 (1-q)` with `c = q^b`, and
    the middle coefficient carries `-2 q c^2 (1-q)` against `A_{b+1}`.  Those match, so the
    CONSTANT `-beta g` is a particular solution.  No Green's function and no convolution are
    needed: the bulk solution is a homogeneous solution of the travel recursion, at the
    half-shifted index, minus the constant `beta g`. -/

/-- **A constant particular solution.**  `A_b = -beta*g` satisfies the bulk three-term
    recursion identically. -/
theorem const_particular (q c g beta : R) :
    (1 + q - 2*q*c^2*(1-q)) * (-(beta*g)) - q * (-(beta*g)) - 2*beta*g*q*c^2*(1-q)
      = -(beta*g) := by
  ring

/-- Consequently, shifting any bulk solution by `beta*g` produces a solution of the homogeneous
    recursion: if `A` satisfies the bulk recursion then `A + beta*g` satisfies the travel one at
    the same index. -/
theorem bulk_shift_homogeneous (q c g beta A0 A1 A2 : R)
    (h : A2 = (1 + q - 2*q*c^2*(1-q)) * A1 - q * A0 - 2*beta*g*q*c^2*(1-q)) :
    A2 + beta*g = (1 + q - 2*q*c^2*(1-q)) * (A1 + beta*g) - q * (A0 + beta*g) := by
  rw [h]; ring

#print axioms const_particular
#print axioms bulk_shift_homogeneous


/-! ### The bridge from `B` to the shifted variable, and why it is parameter-free

    Write `A_b = H_b - beta*g` for the shift of `bulk_shift_homogeneous`, and recall the bulk
    deposit is `P_b = 2 c (1 + c A_b + B_b + g c beta)` with `c = q^b`.  Substituting the shift,
    the `beta` and `g` terms cancel identically, leaving

        `H_{b+1} - H_b = 2 c (1 + c H_b + B_b)` ,

    which mentions neither `beta` nor `g`.  Consequently the condition `B_infinity = 0`, which
    is what selects the physical solution, reads `lim (H_{b+1} - H_b) / q^b = 2` and so pins the
    coefficient of the decaying mode to `-2/(1-q)` without any reference to the self-consistency
    parameter.  That is what makes the two-point problem for `H` closed. -/

/-- **The bridge is parameter-free.**  Substituting `A_b = H_b - beta*g` into the bulk deposit
    cancels every occurrence of `beta` and `g`. -/
theorem deposit_shift (c g beta H B : R) :
    2*c*(1 + c*(H - beta*g) + B + g*c*beta) = 2*c*(1 + c*H + B) := by
  ring

/-- Consequently, if `H_{b+1} - H_b` is the bulk deposit then it satisfies the parameter-free
    relation.  This is the identity that turns `B_infinity = 0` into a condition on `H` alone. -/
theorem bridge_eq (c g beta H0 H1 B : R)
    (hP : H1 - H0 = 2*c*(1 + c*(H0 - beta*g) + B + g*c*beta)) :
    H1 - H0 = 2*c*(1 + c*H0 + B) := by
  rw [hP, deposit_shift]

/-- Solved for `B`: `2 c B = (H_{b+1} - H_b) - 2c - 2 c^2 H_b`.  As `c = q^b -> 0` with `H`
    bounded, the last two terms vanish against `2c`, so `B_infinity = 0` is exactly
    `(H_{b+1} - H_b)/c -> 2`. -/
theorem bridge_solve (c g beta H0 H1 B : R)
    (hP : H1 - H0 = 2*c*(1 + c*(H0 - beta*g) + B + g*c*beta)) :
    2*c*B = (H1 - H0) - 2*c - 2*c^2*H0 := by
  rw [bridge_eq c g beta H0 H1 B hP]; ring

#print axioms deposit_shift
#print axioms bridge_eq
#print axioms bridge_solve


/-! ### Jacobi form of the travel recursion

    The trailing coefficient of the three-term recursion is the constant `-q`, so the recursion
    symmetrises.  Substituting `A_s = r^s z_s` with `r^2 = q` turns

        `A_{s+2} = p_s A_{s+1} - q A_s`   into   `z_{s+2} + z_s = (p_s / r) z_{s+1}` ,

    a JACOBI recursion with unit off-diagonals and diagonal `d_s = p_s / r`.  Writing
    `p_s = 1 + q - e_s` with `e_s = 2 q^2 a^2 (1-q) > 0` and `a = q^s`, the diagonal is
    `d_s = (r + 1/r) - e_s/r`.  Since `r + 1/r > 2` for `0 < r < 1` and the free Jacobi operator
    with unit off-diagonals has spectrum `[-2,2]`, the travel poles sit in the spectral gap, which
    is the regime in which discrete Sturm oscillation theory counts nodes. -/

/-- **Jacobi form.**  With `q = r*r`, the substitution `A_s = r^s z_s` converts the three-term
    recursion into the symmetric one `z_{s+2} + z_s = (p/r) z_{s+1}`, which has UNIT
    off-diagonals.  Stated inverse-free in both directions: `r*(z2 + z0) = p*z1` is exactly the
    `A`-recursion after scaling by `c = r^s`. -/
theorem jacobi_form (r p z0 z1 z2 c : R) (h : r*(z2 + z0) = p*z1) :
    (c*(r*r))*z2 = p*(c*r)*z1 - (r*r)*(c*z0) := by
  have : p*(c*r)*z1 = c*r*(p*z1) := by ring
  rw [this, ← h]; ring

/-- The converse, for `c` and `r` cancellable: the `A`-recursion forces the Jacobi relation. -/
theorem jacobi_form_conv (r p z0 z1 z2 : R)
    (h : (r*r)*z2 = p*r*z1 - (r*r)*z0) :
    r*(r*(z2 + z0)) = r*(p*z1) := by
  have : r*(r*(z2+z0)) = (r*r)*z2 + (r*r)*z0 := by ring
  rw [this, h]; ring

/-- The Jacobi diagonal is the constant `r + 1/r` minus a positive, geometrically decaying
    correction.  Inverse-free: multiplied through by `r`, the diagonal `p` satisfies
    `p = (r*r + 1) - e` with `e = 2 q^2 a^2 (1-q) > 0`, and `r*r + 1 > 2r` for `r != 1`, which is
    the statement that the constant part exceeds the edge `2` of the free spectrum. -/
theorem jacobi_diagonal (q r a : R) (hr : r*r = q) :
    1 + q - 2*q^2*a^2*(1-q) = (r*r + 1) - 2*q^2*a^2*(1-q) := by
  rw [hr]; ring

/-- `r*r + 1 - 2*r = (r-1)^2 >= 0`, with equality only at `r = 1`: the constant part of the
    Jacobi diagonal lies at or above the edge of the free spectrum, strictly above for `r < 1`. -/
theorem jacobi_gap (r : R) : (r*r + 1) - 2*r = (r - 1)^2 := by ring

#print axioms jacobi_form
#print axioms jacobi_form_conv
#print axioms jacobi_diagonal
#print axioms jacobi_gap

/-! ### Axiom audit (Rule 5) -/

#print axioms det_travel
#print axioms det_bulk
#print axioms nilpotent_travel
#print axioms travel_eq
#print axioms bulk_eq
#print axioms half_shift

end TransferChain
