/-
  QCosineLattice.lean
  ===================
  The exponent and order bookkeeping of Sections 4 and 5 of
  `paper/journal/hahn_exton_qcosine.tex` (the Hahn-Exton q-cosine note).

  Companion to `QCosineExponents.lean`, which covers the Section 3 (Galois) exponent gap and
  the Diophantine core.  This file covers what those proofs consume in Sections 4 and 5:

    thm:zeroproduct     the reindexing identity of step (1) and the peak bound of step (2);
    lem:swap            the two Koornwinder-Swarttouw exponent identities;
    prop:latticevalues  strict monotonicity of the r-th term's q-order, which is what makes
                        "no cancellation can occur" a proof rather than an observation;
    thm:integrality     the Newton-polygon exponent identity, the residual shape at q = 0, its
                        derivative at u = 1, and the fact that 1/(q;q)_m really is an element
                        of Z[[q]];
    cor:hexagonal       the onset arithmetic and the quadratic gap to the next correction;
    prop:sinelattice    the sine-side order and onset arithmetic;
    prop:stablelaw      the agreement-depth arithmetic and the pairing weight.

  Two of these caught arithmetic errors in the note and are stated here in corrected form; both
  are flagged at the point of statement.

  Everything is an identity or an inequality between integers, so nothing here depends on any
  q-series analysis.  The analytic content of the Section 4 and 5 proofs (Rouche, dominated
  convergence, Hensel in Z[[q]]) is NOT formalised; see the note's machine-verification section.
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace QCosineLattice

/-! ## 1. `thm:zeroproduct`: the two exponent steps

Step (1) rearranges a double sum using `k(k-1) + 2kj = (k+j)(k+j-1) - j(j-1)`; step (2) bounds
the dressing factor using `2Nj - j(j-1)/2 >= Nj` on `1 <= j <= 2N`.  Both are stated doubled so
that no division occurs. -/

/-- **Step (1), the reindexing exponent.**  This is the identity that lets the double sum
    `sum_{k,j}` be collected on `m = k + j`. -/
theorem zeroproduct_reindex (k j : ℤ) :
    k * (k - 1) + 2 * k * j = (k + j) * (k + j - 1) - j * (j - 1) := by ring

/-- **Step (2), the peak bound.**  Doubled form of `2Nj - j(j-1)/2 >= Nj`, valid exactly on the
    stated range `1 <= j <= 2N`; this is what makes the dressing polynomial `P_m(1/z)` equal to
    `1 + O(q^N)` uniformly. -/
theorem zeroproduct_peak_bound (N j : ℤ) (h1 : 1 ≤ j) (h2 : j ≤ 2 * N) :
    2 * (N * j) ≤ 4 * (N * j) - j * (j - 1) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- The exact slack in `zeroproduct_peak_bound`.  It is `j(2N+1-j)`, so the bound holds precisely
    while `j <= 2N+1` and fails from `j = 2N+2` on: the range restriction is not an artifact. -/
theorem zeroproduct_peak_slack (N j : ℤ) :
    (4 * (N * j) - j * (j - 1)) - 2 * (N * j) = j * (2 * N + 1 - j) := by ring

/-! ## 2. `lem:swap`: the Koornwinder-Swarttouw exponent identities -/

/-- **The symmetry exponent.**  `binom(n,2) + binom(i,2) + ni = binom(n+i,2)`, doubled.  This is
    what makes the double sum in the proof of `lem:swap` manifestly symmetric in `(b, z)`. -/
theorem swap_symmetry_exponent (n i : ℤ) :
    n * (n - 1) + i * (i - 1) + 2 * (n * i) = (n + i) * (n + i - 1) := by ring

/-- **The base collapse.**  With `Q = q^2`, `Q^{binom(n,2)} q^n = q^{n^2}`; doubled, the exponent
    on the left is `n(n-1) + n`. -/
theorem swap_base_collapse (n : ℤ) : n * (n - 1) + n = n ^ 2 := by ring

/-! ## 3. `prop:latticevalues`: the order of the lattice sum

The `r`-th term of the lattice evaluation has `q`-order `(m+1+r)^2`.  The proposition asserts
`ord_q G(q, Q^{-m}) = (m+1)^2` *exactly*, and that assertion is legitimate only because the
orders are strictly increasing in `r`, so the `r = 0` term cannot be cancelled. -/

/-- The gap between the `r`-th and the leading term of the lattice sum. -/
theorem lattice_order_gap (m r : ℤ) :
    (m + 1 + r) ^ 2 - (m + 1) ^ 2 = r * (2 * (m + 1) + r) := by ring

/-- **Strict monotonicity in `r`.**  For `m >= 0` the orders `(m+1+r)^2` are strictly increasing
    on `r >= 0`, so the minimum is attained once, at `r = 0`: no cancellation can occur. -/
theorem lattice_order_strictMono (m r : ℤ) (hm : 0 ≤ m) (hr : 0 ≤ r) :
    (m + 1 + r) ^ 2 < (m + 1 + (r + 1)) ^ 2 := by nlinarith

/-- The leading term is strictly below every later one, which is the form the proposition uses. -/
theorem lattice_order_leading (m r : ℤ) (hm : 0 ≤ m) (hr : 1 ≤ r) :
    (m + 1) ^ 2 < (m + 1 + r) ^ 2 := by nlinarith

/-! ## 4. `thm:integrality`: Newton polygon, residual shape, and the integrality input -/

/-- **The rescaling exponent identity.**  `k'(k'-1) - 2(k-1)k' + k(k-1) = (k'-k)(k'-k+1)`: the
    exponent that appears after substituting `z = u q^{-2(k-1)}` and multiplying by `q^{k(k-1)}`.
    (`QCosineExponents.newtonExp` is the right-hand side; this is the identity that produces
    it.) -/
theorem integrality_exponent (k k' : ℤ) :
    k' * (k' - 1) - 2 * (k - 1) * k' + k * (k - 1) = (k' - k) * (k' - k + 1) := by ring

/-- **The residual at `q = 0`.**  Only the two indices `k' = k-1` and `k' = k` survive, and their
    contributions assemble into `(-1)^{k-1} u^{k-1} (1 - u)`.  Written with `k = j + 1` so that no
    truncated subtraction occurs. -/
theorem newton_residual_shape {R : Type*} [CommRing R] (j : ℕ) (u : R) :
    (-1 : R) ^ j * u ^ j + (-1) ^ (j + 1) * u ^ (j + 1)
      = (-1) ^ j * u ^ j * (1 - u) := by
  rw [pow_succ, pow_succ]; ring

/-- The residual polynomial of `thm:integrality`, at `q = 0`, as an integer polynomial. -/
noncomputable def residualPoly (j : ℕ) : Polynomial ℤ :=
  Polynomial.C ((-1) ^ j) * (Polynomial.X ^ j * (1 - Polynomial.X))

/-- **The residual vanishes at `u = 1`.** -/
theorem residualPoly_eval_one (j : ℕ) : (residualPoly j).eval 1 = 0 := by
  simp [residualPoly]

/-- **The derivative is a unit at `u = 1`.**  `d/du [(-1)^j u^j (1-u)]|_{u=1} = (-1)^{j+1}`, which
    is `+-1`; this is the simple-root hypothesis that the Hensel step consumes. -/
theorem residualPoly_derivative_eval_one (j : ℕ) :
    (Polynomial.derivative (residualPoly j)).eval 1 = (-1) ^ (j + 1) := by
  simp [residualPoly, Polynomial.derivative_mul, pow_succ]

/-- Consequently the derivative at the root is a unit in `Z`, which is the exact hypothesis
    shape required by a Hensel step. -/
theorem residualPoly_derivative_isUnit (j : ℕ) :
    IsUnit ((Polynomial.derivative (residualPoly j)).eval 1) := by
  rw [residualPoly_derivative_eval_one]
  exact (isUnit_one.neg).pow _

/-- **The integrality input.**  `(q;q)_m = prod_{i=1}^m (1 - q^i)` is a unit in `Z[[q]]`, so
    `1/(q;q)_m` lies in `Z[[q]]`.  This is the step of `thm:integrality` that says
    "`1/(q;q)_{2k'} in Z[[q]]` (partitions into parts `<= 2k'`)". -/
theorem qPochhammer_isUnit (m : ℕ) :
    IsUnit (∏ i ∈ Finset.Icc 1 m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, map_prod]
  have h : ∀ i ∈ Finset.Icc 1 m,
      PowerSeries.constantCoeff (1 - (PowerSeries.X : PowerSeries ℤ) ^ i) = 1 := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    simp
  rw [Finset.prod_congr rfl h, Finset.prod_const_one]
  exact isUnit_one

/-! ## 5. `cor:hexagonal`: the onset arithmetic -/

/-- **The cosine onset.**  `k(k-1) + k^2 = k(2k-1)`: the `q^{k(k-1)}` prefactor of `F_k` plus the
    lattice order `(m+1)^2` at `m = k-1` gives the `k`-th hexagonal number. -/
theorem hexagonal_onset (k : ℤ) : k * (k - 1) + k ^ 2 = k * (2 * k - 1) := by ring

/-- **The next Newton correction is quadratically further out.**  For `k >= 1` the second
    correction sits at `2k(2k-1)`, strictly beyond the first, which is why the leading
    coefficient of the deviation is decided by one Newton step. -/
theorem hexagonal_next_correction (k : ℤ) (hk : 1 ≤ k) :
    k * (2 * k - 1) < 2 * (k * (2 * k - 1)) := by nlinarith

/-! ## 6. `prop:sinelattice`: the sine-side order and onset

The note's displayed derivation of item (c) is wrong as written: it reads
`ord_q H(q, q^{1-2k}) + 1 - ((k+1)^2 - 1)`, which with `ord_q H = (k+1)^2 - 1` evaluates to `1`,
not to `k(2k+1)`.  The correct bookkeeping adds the `q^{k(k-1)}` prefactor of the rescaled sine
function, exactly as on the cosine side, and is the identity below.  The stated conclusion
`k(2k+1)` is unaffected. -/

/-- The sine-side reindexing shift `(m+r)^2 + 2(m+r) = (m+r+1)^2 - 1` of item (b). -/
theorem sine_shift (m r : ℤ) : (m + r) ^ 2 + 2 * (m + r) = (m + r + 1) ^ 2 - 1 := by ring

/-- **The sine onset, corrected.**  `k(k-1) + ((k+1)^2 - 1) = k(2k+1)`: the prefactor plus the
    sine-side lattice order gives the `2k`-th triangular number. -/
theorem sine_onset (k : ℤ) : k * (k - 1) + ((k + 1) ^ 2 - 1) = k * (2 * k + 1) := by ring

/-- The two onsets are consecutive triangular numbers, and differ by `2k`. -/
theorem onsets_differ (k : ℤ) : k * (2 * k + 1) - k * (2 * k - 1) = 2 * k := by ring

/-! ## 7. `prop:stablelaw`: agreement depth and the pairing weight

The note's numerator step is also misstated: it gives the `r`-th term's relative order as
`(k+r)^2 - k(2k-1)`, which at `r = 1`, `k = 2` is `3`, contradicting the stated depth `2k+1 = 5`.
The prefactor `q^{k(k-1)}` is missing; the correct relative order is `(k+r)^2 - k^2`, whose value
at `r = 1` is exactly `2k+1`.  The stated depth is unaffected. -/

/-- **The numerator agreement depth, corrected.**  Relative to the leading term, the `r`-th term
    of the lattice sum sits at order `(k+r)^2 - k^2`, which is at least `2k+1` for `r >= 1`. -/
theorem stablelaw_numerator_depth (k r : ℤ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    2 * k + 1 ≤ (k + r) ^ 2 - k ^ 2 := by nlinarith

/-- The depth is attained at `r = 1`, so `2k+1` is sharp. -/
theorem stablelaw_numerator_depth_sharp (k : ℤ) : (k + 1) ^ 2 - k ^ 2 = 2 * k + 1 := by ring

/-- **The denominator pairing.**  The indices `k' = k+j` and `k' = k-1-j` carry the same Newton
    exponent `j(j+1)`. -/
theorem stablelaw_pair_exponent (k j : ℤ) :
    ((k + j) - k) * ((k + j) - k + 1) = j * (j + 1) ∧
    ((k - 1 - j) - k) * ((k - 1 - j) - k + 1) = j * (j + 1) := by
  constructor <;> ring

/-- **The pairing weight.**  Their weights differ by `2j+1`, which is the coefficient appearing
    in Jacobi's identity `sum_j (-1)^j (2j+1) q^{j(j+1)} = (q^2;q^2)_inf^3`. -/
theorem stablelaw_pair_weight (k j : ℤ) : (k + j) - (k - 1 - j) = 2 * j + 1 := by ring

/-- **The pairing signs are opposite.**  The two indices have odd difference, hence opposite
    parity, which is why the pair contributes with the single weight `2j+1`. -/
theorem stablelaw_pair_parity (k j : ℤ) : Odd ((k + j) - (k - 1 - j)) := by
  exact ⟨j, by ring⟩

/-- **The denominator tail.**  `(Q;Q)_k = (Q;Q)_inf (1 + O(q^{2k+2}))`: the first omitted factor
    is `1 - q^{2(k+1)}`, so the agreement depth on that side is `2k+2`. -/
theorem stablelaw_denominator_depth (k : ℤ) : 2 * k + 1 < 2 * (k + 1) := by omega

/-! ## 8. The Euler splitting used to finish `thm:zeroproduct`

`(q;q)_inf = (q;q^2)_inf (q^2;q^2)_inf`: every positive integer is uniquely odd or even.  At
finite level this is the following product identity, valid in any commutative ring. -/

/-- **Euler's splitting, finite form.**  The product over `1..2n` factors as the product over the
    `n` odd indices times the product over the `n` even indices. -/
theorem euler_split {R : Type*} [CommRing R] (n : ℕ) (f : ℕ → R) :
    (∏ i ∈ Finset.range n, f (2 * i + 1)) * (∏ i ∈ Finset.range n, f (2 * i + 2))
      = ∏ i ∈ Finset.range (2 * n), f (i + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [Finset.prod_range_succ, Finset.prod_range_succ, h2,
        Finset.prod_range_succ, Finset.prod_range_succ, ← ih]
      ring

end QCosineLattice

/-! ### Axiom audit (Rule 5) -/

#print axioms QCosineLattice.zeroproduct_reindex
#print axioms QCosineLattice.zeroproduct_peak_bound
#print axioms QCosineLattice.zeroproduct_peak_slack
#print axioms QCosineLattice.swap_symmetry_exponent
#print axioms QCosineLattice.swap_base_collapse
#print axioms QCosineLattice.lattice_order_gap
#print axioms QCosineLattice.lattice_order_strictMono
#print axioms QCosineLattice.lattice_order_leading
#print axioms QCosineLattice.integrality_exponent
#print axioms QCosineLattice.newton_residual_shape
#print axioms QCosineLattice.residualPoly_eval_one
#print axioms QCosineLattice.residualPoly_derivative_eval_one
#print axioms QCosineLattice.residualPoly_derivative_isUnit
#print axioms QCosineLattice.qPochhammer_isUnit
#print axioms QCosineLattice.hexagonal_onset
#print axioms QCosineLattice.hexagonal_next_correction
#print axioms QCosineLattice.sine_shift
#print axioms QCosineLattice.sine_onset
#print axioms QCosineLattice.onsets_differ
#print axioms QCosineLattice.stablelaw_numerator_depth
#print axioms QCosineLattice.stablelaw_numerator_depth_sharp
#print axioms QCosineLattice.stablelaw_pair_exponent
#print axioms QCosineLattice.stablelaw_pair_weight
#print axioms QCosineLattice.stablelaw_pair_parity
#print axioms QCosineLattice.stablelaw_denominator_depth
#print axioms QCosineLattice.euler_split
