/-
  QCosineExponents.lean
  =====================
  The exponent arithmetic of the Hahn-Exton note.

  These are the identities that carry the note's two structural arguments, and they are exactly
  where a transcription slip hides: every one is a statement about integer exponents, none needs
  any q-series analysis, and an error in any of them is invisible to a numerical check that only
  ever samples one q.

  Tier 1 of the audit's formalisation list, plus the identity that repairs the SL2 theorem.

    1. `supermult_exponent` -- the exponent identity behind
           b_i b_{j-i} / b_j = q^{i(j-i)} * [j choose i]_q,
       whose consequence `gap_ge` (i(j-i) >= j-1 on 1 <= i <= j-1) is what replaces the note's
       one-point numerical check in the proof that the difference Galois group contains SL2.
    2. `newton_exponent_*` -- the Newton-polygon exponents, and their strict convexity, which is
       what makes the Hensel step apply on a single edge.
    3. `tail_sum` -- the truncation-ledger sum used for the degree bookkeeping.
    4. `triangular_onsets` -- the two deviation onsets are consecutive triangular numbers.
    5. `farey_separation` -- the Diophantine separation of two distinct rationals, the core of
       the note's only unconditional arithmetic result.
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

namespace QCosineExponents

/-! ### 1. The super-multiplicativity gap that repairs the SL2 proof

    With `b_j = q^{j - j(j-1)/2}/(q;q)_j`, the powers of `q` in `b_i b_{j-i} / b_j` contribute
    the exponent below.  Everything is stated doubled, to stay in the integers. -/

/-- **The exponent identity.**  `2 * [ (i - i(i-1)/2) + ((j-i) - (j-i)(j-i-1)/2) - (j - j(j-1)/2) ]
    = 2 * i * (j - i)`, written without division. -/
theorem supermult_exponent (i j : ℤ) :
    (2 * i - i * (i - 1)) + (2 * (j - i) - (j - i) * ((j - i) - 1))
      - (2 * j - j * (j - 1)) = 2 * (i * (j - i)) := by
  ring

/-- **The gap.**  For `1 <= i <= j-1` the exponent `i(j-i)` is at least `j-1`, so every product
    that splits off is smaller by at least `q^{j-1}`.  This is uniform in `j`, and in particular
    does not depend on `q`, which is the whole point: the note previously checked one value. -/
theorem gap_ge {i j : ℤ} (h1 : 1 ≤ i) (h2 : i ≤ j - 1) : j - 1 ≤ i * (j - i) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- The gap is attained exactly at the two ends, which is why `q^{j-1}` and not better. -/
theorem gap_eq_at_ends (j : ℤ) :
    1 * (j - 1) = j - 1 ∧ (j - 1) * (j - (j - 1)) = j - 1 := by
  constructor <;> ring

/-! ### 2. Newton-polygon exponents

    The cosine side has exponent `(k' - k)(k' - k + 1)` and the sine side the same shifted; both
    are strictly convex in `k'` with a unique minimiser, which is what puts a single edge of
    slope zero on the Newton polygon and lets Hensel run. -/

/-- The cosine-side exponent, as a function of the summation index. -/
def newtonExp (k k' : ℤ) : ℤ := (k' - k) * (k' - k + 1)

/-- It is nonnegative, and vanishes exactly at the two lattice points `k' = k` and `k' = k - 1`. -/
theorem newtonExp_nonneg (k k' : ℤ) : 0 ≤ newtonExp k k' := by
  unfold newtonExp
  rcases lt_trichotomy (k' - k) 0 with h | h | h
  · have h1 : k' - k ≤ -1 := by omega
    have h2 : k' - k + 1 ≤ 0 := by omega
    nlinarith
  · rw [h]; norm_num
  · have h2 : (0:ℤ) ≤ k' - k + 1 := by omega
    nlinarith

theorem newtonExp_eq_zero_iff (k k' : ℤ) : newtonExp k k' = 0 ↔ k' = k ∨ k' = k - 1 := by
  unfold newtonExp
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-- **Strict convexity**: the second difference is the constant `2`, so the exponent has a unique
    minimising edge and no two interior points are collinear with it. -/
theorem newtonExp_second_difference (k k' : ℤ) :
    newtonExp k (k' + 1) - 2 * newtonExp k k' + newtonExp k (k' - 1) = 2 := by
  unfold newtonExp; ring

/-- The sine-side exponent used in `prop:sinelattice`, and the shift that produces the displayed
    sum: `(m+r)^2 + 2(m+r) = (m+r+1)^2 - 1`. -/
theorem sine_shift (m r : ℤ) : (m + r) ^ 2 + 2 * (m + r) = (m + r + 1) ^ 2 - 1 := by ring

/-! ### 3. The truncation-ledger sum -/

/-- `sum_{i = 2k+1}^{2N} i + (2k^2 + k) = 2N^2 + N`, the degree bookkeeping of the ledger.
    Stated additively so that no truncated natural subtraction appears. -/
theorem tail_sum (N k : ℕ) (h : k ≤ N) :
    (∑ i ∈ Finset.Icc (2 * k + 1) (2 * N), i) + (2 * k ^ 2 + k) = 2 * N ^ 2 + N := by
  induction N with
  | zero =>
      have : k = 0 := Nat.le_zero.mp h
      subst this; simp
  | succ n ih =>
      rcases Nat.lt_or_ge k (n + 1) with hk | hk
      · have hkn : k ≤ n := by omega
        have hsplit : Finset.Icc (2 * k + 1) (2 * (n + 1))
            = insert (2 * n + 1) (insert (2 * n + 2) (Finset.Icc (2 * k + 1) (2 * n))) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have h1 : (2 * n + 1) ∉ Finset.Icc (2 * k + 1) (2 * n) := by
          simp only [Finset.mem_Icc]; omega
        have h2 : (2 * n + 2) ∉ Finset.Icc (2 * k + 1) (2 * n) := by
          simp only [Finset.mem_Icc]; omega
        have h3 : (2 * n + 1) ∉ insert (2 * n + 2) (Finset.Icc (2 * k + 1) (2 * n)) := by
          simp only [Finset.mem_insert, Finset.mem_Icc]; omega
        rw [hsplit, Finset.sum_insert h3, Finset.sum_insert h2]
        have := ih hkn
        ring_nf
        ring_nf at this
        omega
      · have hkeq : k = n + 1 := by omega
        subst hkeq
        have : Finset.Icc (2 * (n + 1) + 1) (2 * (n + 1)) = ∅ := by
          apply Finset.Icc_eq_empty; omega
        rw [this]; simp

/-! ### 4. The triangular law

    The two interleaved zero lattices have deviation onsets `k(2k-1)` and `k(2k+1)`, which are
    the consecutive triangular numbers `T_{2k-1}` and `T_{2k}`. -/

/-- Twice the `n`-th triangular number, stated so that no division occurs. -/
def twoT (n : ℤ) : ℤ := n * (n + 1)

/-- The cosine-side onset `k(2k-1)` is the triangular number `T_{2k-1}`. -/
theorem cosine_onset (k : ℤ) : twoT (2 * k - 1) = 2 * (k * (2 * k - 1)) := by
  unfold twoT; ring

/-- The sine-side onset `k(2k+1)` is the triangular number `T_{2k}`. -/
theorem sine_onset (k : ℤ) : twoT (2 * k) = 2 * (k * (2 * k + 1)) := by
  unfold twoT; ring

/-- **The triangular law**: the two onsets are consecutive triangular numbers, their difference
    being `2k`. -/
theorem onsets_consecutive (k : ℤ) : twoT (2 * k) - twoT (2 * k - 1) = 2 * (2 * k) := by
  unfold twoT; ring

/-! ### 5. Diophantine separation

    The core of the note's only unconditional arithmetic result: two distinct rationals with
    denominators `b` and `d` are at least `1/(b d)` apart.  The numerics that locate the interval
    stay outside Lean; this is the step that turns them into an exclusion. -/

/-- **The integer core.**  For `a/b /= c/d` with positive denominators, the cross-difference
    `a d - c b` is a nonzero integer, hence at least `1` in absolute value.  Dividing by `b d`
    turns this into the separation `|a/b - c/d| >= 1/(b d)`, which is the form used in the note:
    a rational root of a truncation can be excluded once the interval containing the true root is
    narrower than the separation its denominator would force. -/
theorem cross_difference_ge_one {a b c d : ℤ} (hne : a * d ≠ c * b) :
    1 ≤ |a * d - c * b| := by
  have h0 : a * d - c * b ≠ 0 := sub_ne_zero.mpr hne
  rcases lt_trichotomy (a * d - c * b) 0 with h | h | h
  · rw [abs_of_neg h]; omega
  · exact absurd h h0
  · rw [abs_of_pos h]; omega

/-- The separation in the form it is applied: distinct rationals with denominators `b` and `d`
    are at least `1/(b d)` apart.  Stated multiplicatively to keep it division-free. -/
theorem farey_separation {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d) (hne : a * d ≠ c * b) :
    1 ≤ |a * d - c * b| ∧ 0 < b * d := by
  exact ⟨cross_difference_ge_one hne, mul_pos hb hd⟩

end QCosineExponents

/-! ### Axiom audit (Rule 5)

This block was missing when the file was first written, so the file was cited by the note without
ever printing its axioms.  Absence of build errors is not a certificate: a constant that fails to
elaborate reports "does not depend on any axioms". -/

#print axioms QCosineExponents.supermult_exponent
#print axioms QCosineExponents.gap_ge
#print axioms QCosineExponents.gap_eq_at_ends
#print axioms QCosineExponents.newtonExp_nonneg
#print axioms QCosineExponents.newtonExp_eq_zero_iff
#print axioms QCosineExponents.newtonExp_second_difference
#print axioms QCosineExponents.sine_shift
#print axioms QCosineExponents.tail_sum
#print axioms QCosineExponents.cosine_onset
#print axioms QCosineExponents.sine_onset
#print axioms QCosineExponents.onsets_consecutive
#print axioms QCosineExponents.cross_difference_ge_one
#print axioms QCosineExponents.farey_separation
