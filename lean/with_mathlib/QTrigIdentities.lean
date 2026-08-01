/-
  QTrigIdentities.lean
  ====================
  The per-term algebraic identities underlying the q-trigonometric layer of paper 2
  (Sections "sec:qtrig", "sec:V" and Appendix A), and the Casoratian constancy that
  yields the half-step invariant.

  Every series identity used in that layer is proved by matching the j-th summand.
  What is machine-checked here is exactly that matching: the exponent bookkeeping,
  which is where such proofs actually go wrong.  Convergence and the interchange of
  summation are analytic and are not formalised.

  Conventions (paper 2):
      c(u) = sum_j (-1)^j q^{j^2+j}   u^{2j}   / (q;q)_{2j}
      s(u) = sum_j (-1)^j q^{j^2+2j}  u^{2j+1} / (q;q)_{2j+1}
      F(x) = sum_M q^{M^2/4} x^M / (q;q)_M
  Note (dictionary warning, cf. paper 2): s is NOT the Koornwinder-Swarttouw q-sine;
  s(u) = q^{-1/2} sin(q^{1/2} u; q^2).
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace QTrig

/-! ### Exponent bookkeeping

All half-integer exponents are cleared by doubling, so every statement below is an
identity of natural numbers and is closed by `ring`. -/

/-- **Half-step rule for `c`** (`c(qu) = c(u) + q^{3/2} u s(sqrt q u)`), exponent step.
    The `k`-th summand of `c(qu) - c(u)` carries `q^{(k+1)^2+(k+1)}`; the `k`-th summand
    of `q^{3/2} u s(sqrt q u)` carries `q^{3/2} q^{k^2+2k} q^{k+1/2}`.  Doubled: -/
theorem cshift_exponent (k : ℕ) :
    2 * ((k + 1) ^ 2 + (k + 1)) = 2 * (k ^ 2 + 2 * k) + 3 + (2 * k + 1) := by ring

/-- **Half-step rule for `s`** (`s(qu) = s(u) - u c(sqrt q u)`), exponent step:
    the `k`-th summand of `s(u) - s(qu)` carries `q^{k^2+2k}`, that of `u c(sqrt q u)`
    carries `q^{k^2+k} q^{k}`. -/
theorem sshift_exponent (k : ℕ) : k ^ 2 + 2 * k = (k ^ 2 + k) + k := by ring

/-- **Parity split** (`Re Phi = C(rho^2/q)`, `Im Phi = q^{1/4} rho T(rho^2/q)`):
    `(2j+1)^2/4 = j^2 + j + 1/4`, doubled by 4. -/
theorem parity_exponent (j : ℕ) : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring

/-- **q-Airy / functional equation** (`F(x) - F(qx) = q^{1/4} x F(sqrt q x)`):
    `(N+1)^2/4 = 1/4 + N^2/4 + N/2`, cleared by 4. -/
theorem qairy_exponent (N : ℕ) : (N + 1) ^ 2 = 1 + N ^ 2 + 2 * N := by ring

/-- **`P12` k-sum splitting, first branch**: `y^k q^{k^2+k} = q^{k^2+2k} (y/q)^k`,
    i.e. `k^2 + k + k = k^2 + 2k` after clearing the negative power. -/
theorem P12_split_lo (k : ℕ) : (k ^ 2 + k) + k = k ^ 2 + 2 * k := by ring

/-- **`P12` k-sum splitting, second branch**: `y^k q^{k^2+3k} = q^{k^2+2k} (yq)^k`. -/
theorem P12_split_hi (k : ℕ) : k ^ 2 + 3 * k = (k ^ 2 + 2 * k) + k := by ring

/-! ### The Casoratian constancy behind the half-step invariant

The ladder `Phi_j = Phi(q^{j/2} rho)` obeys `Phi_{j+2} = Phi_j - i c_j Phi_{j+1}` with
`c_j` REAL (this is the functional equation).  The real part of `Phi_{j+1} * conj (Phi_j)`
is then independent of `j`; since `Phi_j -> 1`, that constant is `1`, which is the
half-step invariant `c(u) c(sqrt q u) + q^{3/2} s(u) s(sqrt q u) = 1`.

Realness of `c_j` is what makes the added term purely imaginary, and is therefore the
whole content; it is stated as a hypothesis and used as such. -/

open Complex

/-- **Casoratian constancy.**  With a real ladder coefficient, `Re (Phi_{j+1} * conj Phi_j)`
    does not depend on `j`. -/
theorem casoratian_re_const (Φ : ℕ → ℂ) (c : ℕ → ℝ)
    (hrec : ∀ j, Φ (j + 2) = Φ j - Complex.I * (c j : ℂ) * Φ (j + 1)) (j : ℕ) :
    (Φ (j + 2) * (starRingEnd ℂ) (Φ (j + 1))).re
      = (Φ (j + 1) * (starRingEnd ℂ) (Φ j)).re := by
  rw [hrec j]
  simp only [sub_mul, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Every rung equals the zeroth.**  Iterating `casoratian_re_const`: the real part is
    the same at every level, so a value known in the limit pins it everywhere.  This is
    the step that turns constancy into the half-step invariant. -/
theorem casoratian_re_eq_zero (Φ : ℕ → ℂ) (c : ℕ → ℝ)
    (hrec : ∀ j, Φ (j + 2) = Φ j - Complex.I * (c j : ℂ) * Φ (j + 1)) :
    ∀ n, (Φ (n + 1) * (starRingEnd ℂ) (Φ n)).re
       = (Φ 1 * (starRingEnd ℂ) (Φ 0)).re := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => rw [← ih]; exact casoratian_re_const Φ c hrec k

end QTrig

-- Rule 5 axiom audit.
#print axioms QTrig.cshift_exponent
#print axioms QTrig.sshift_exponent
#print axioms QTrig.parity_exponent
#print axioms QTrig.qairy_exponent
#print axioms QTrig.P12_split_lo
#print axioms QTrig.P12_split_hi
#print axioms QTrig.casoratian_re_const
#print axioms QTrig.casoratian_re_eq_zero
