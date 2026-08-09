/-
  QSiegelLedger.lean
  ==================
  The truncation ledger of Section 5 of `paper/journal/hahn_exton_qcosine.tex`:
  `prop:secondkind` (the degree bookkeeping), `prop:reduction` (denominator clearing and the
  Liouville reductio), `cor:suffices` and `rem:thetabarrier` (the margin arithmetic).

  DENOMINATOR CLEARING WITHOUT `MvPolynomial`.  The note's reduction step needs
  `t^{deg_q P_N} b^{deg_z P_N} P_N(s/t, a/b) in Z`.  Stated for a general two-variable integer
  polynomial that is a theorem about `MvPolynomial (Fin 2) Z` and its two total degrees, and it
  is a substantial piece of work.  It is not needed.  `P_N` is given in the note by an explicit
  product formula, so the cleared quantity can be WRITTEN DOWN as an integer,

      cleared N s t a b
        = sum_k (-1)^k s^{k(k-1)} a^k b^{N-k} t^{k^2+2k} prod_{i=2k+1}^{2N} (t^i - s^i),

  and the only thing to prove is that it equals `t^{2N^2+N} b^N P_N(s/t, a/b)`.  That is a
  termwise field identity whose entire content is the exponent ledger
  `k(k-1) + sum_{i=2k+1}^{2N} i + (k^2+2k) = 2N^2+N`.  This is the same move that
  `ModularRankCertificate.lean` makes for the D-finite exclusions: route around the general
  clearing lemma instead of proving it.

  What is formalised here is therefore the complete arithmetic of `prop:reduction`.  The
  analytic input it consumes (the remainder bound `|R_N| = q^{N^2(1+o(1))}` of
  `prop:secondkind`) is a hypothesis, as it must be: it is an estimate on a q-series tail, not
  an arithmetic fact.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import QCosineExponents

namespace QSiegelLedger

open Finset

/-! ## 1. The exponent ledger

`prop:secondkind` states `deg_q P_N = 2N^2+N`, attained only by the `k = 0` summand.  The `k`-th
summand has `q`-degree `k(k-1) + sum_{i=2k+1}^{2N} i`, and the ledger below says that this is
`2N^2+N` short by exactly `k^2+2k`. -/

/-- **The degree ledger.**  `k(k-1) + sum_{i=2k+1}^{2N} i + (k^2+2k) = 2N^2+N` for `k <= N`. -/
theorem degree_ledger (N k : ℕ) (h : k ≤ N) :
    k * (k - 1) + (∑ i ∈ Finset.Icc (2 * k + 1) (2 * N), i) + (k ^ 2 + 2 * k)
      = 2 * N ^ 2 + N := by
  have ht := QCosineExponents.tail_sum N k h
  cases k with
  | zero => simpa using ht
  | succ m =>
      have hsub : m + 1 - 1 = m := by omega
      rw [hsub]
      calc (m + 1) * m + (∑ i ∈ Finset.Icc (2 * (m + 1) + 1) (2 * N), i)
              + ((m + 1) ^ 2 + 2 * (m + 1))
          = (∑ i ∈ Finset.Icc (2 * (m + 1) + 1) (2 * N), i) + (2 * (m + 1) ^ 2 + (m + 1)) := by
            ring
        _ = 2 * N ^ 2 + N := ht

/-- **The maximum is attained at `k = 0`.** -/
theorem degree_at_zero (N : ℕ) :
    (∑ i ∈ Finset.Icc 1 (2 * N), i) = 2 * N ^ 2 + N := by
  have := degree_ledger N 0 (Nat.zero_le N)
  simpa using this

/-- **The maximum is attained only there.**  Every summand with `k >= 1` has strictly smaller
    `q`-degree, so no cancellation can lower `deg_q P_N` below `2N^2+N`. -/
theorem degree_lt_of_pos (N k : ℕ) (hk : k ≤ N) (hk0 : 1 ≤ k) :
    k * (k - 1) + (∑ i ∈ Finset.Icc (2 * k + 1) (2 * N), i) < 2 * N ^ 2 + N := by
  have h := degree_ledger N k hk
  have hpos : 0 < k ^ 2 + 2 * k := by positivity
  omega

/-! ## 2. `P_N` and its cleared integer numerator -/

/-- `P_N(q,z) = sum_{k=0}^N (-1)^k q^{k(k-1)} z^k prod_{i=2k+1}^{2N} (1-q^i)`, evaluated over the
    rationals.  This is the note's second-kind form. -/
def Pval (N : ℕ) (q z : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1),
    (-1 : ℚ) ^ k * q ^ (k * (k - 1)) * z ^ k *
      ∏ i ∈ Finset.Icc (2 * k + 1) (2 * N), (1 - q ^ i)

/-- The `k`-th cleared term: an integer by inspection. -/
def clearedTerm (N k : ℕ) (s t a b : ℤ) : ℤ :=
  (-1) ^ k * s ^ (k * (k - 1)) * a ^ k * b ^ (N - k) * t ^ (k ^ 2 + 2 * k) *
    ∏ i ∈ Finset.Icc (2 * k + 1) (2 * N), (t ^ i - s ^ i)

/-- The cleared integer numerator of `t^{2N^2+N} b^N P_N(s/t, a/b)`. -/
def cleared (N : ℕ) (s t a b : ℤ) : ℤ :=
  ∑ k ∈ Finset.range (N + 1), clearedTerm N k s t a b

/-- The product of `1 - (s/t)^i` over an index set, with the powers of `t` collected. -/
theorem prod_one_sub_div (s t : ℤ) (ht : (t : ℚ) ≠ 0) (I : Finset ℕ) :
    ∏ i ∈ I, (1 - ((s : ℚ) / t) ^ i)
      = (∏ i ∈ I, ((t : ℚ) ^ i - (s : ℚ) ^ i)) / (t : ℚ) ^ (∑ i ∈ I, i) := by
  have hfac : ∀ i ∈ I, (1 : ℚ) - ((s : ℚ) / t) ^ i
      = ((t : ℚ) ^ i - (s : ℚ) ^ i) / (t : ℚ) ^ i := by
    intro i _
    rw [div_pow]
    field_simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

/-- **The clearing identity, termwise.** -/
theorem clearedTerm_eq (N k : ℕ) (hk : k ≤ N) (s t a b : ℤ)
    (ht : (t : ℚ) ≠ 0) (hb : (b : ℚ) ≠ 0) :
    (clearedTerm N k s t a b : ℚ)
      = (t : ℚ) ^ (2 * N ^ 2 + N) * (b : ℚ) ^ N *
        ((-1 : ℚ) ^ k * ((s : ℚ) / t) ^ (k * (k - 1)) * ((a : ℚ) / b) ^ k *
          ∏ i ∈ Finset.Icc (2 * k + 1) (2 * N), (1 - ((s : ℚ) / t) ^ i)) := by
  have hS := degree_ledger N k hk
  have hprod := prod_one_sub_div s t ht (Finset.Icc (2 * k + 1) (2 * N))
  have hbk : (b : ℚ) ^ (N - k) * (b : ℚ) ^ k = (b : ℚ) ^ N := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have htpow : (t : ℚ) ^ (2 * N ^ 2 + N)
      = (t : ℚ) ^ (k * (k - 1)) * (t : ℚ) ^ (∑ i ∈ Finset.Icc (2 * k + 1) (2 * N), i) *
        (t : ℚ) ^ (k ^ 2 + 2 * k) := by
    rw [← pow_add, ← pow_add, hS]
  rw [hprod, htpow, clearedTerm]
  push_cast
  rw [div_pow, div_pow, ← hbk]
  field_simp

/-- **The clearing identity.**  `t^{2N^2+N} b^N P_N(s/t, a/b)` is the integer `cleared`. -/
theorem cleared_eq (N : ℕ) (s t a b : ℤ) (ht : (t : ℚ) ≠ 0) (hb : (b : ℚ) ≠ 0) :
    (cleared N s t a b : ℚ)
      = (t : ℚ) ^ (2 * N ^ 2 + N) * (b : ℚ) ^ N * Pval N ((s : ℚ) / t) ((a : ℚ) / b) := by
  rw [cleared, Pval, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact clearedTerm_eq N k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) s t a b ht hb

/-! ## 3. The Liouville floor and the reductio

This is `prop:reduction` in full: a nonzero integer has modulus at least one, so a nonzero
`P_N(q,z_0)` cannot be smaller than the reciprocal of its cleared denominator. -/

/-- A nonzero integer has rational modulus at least `1`. -/
theorem one_le_abs_of_ne_zero {m : ℤ} (hm : m ≠ 0) : (1 : ℚ) ≤ |(m : ℚ)| := by
  have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs (by omega)
  have : ((1 : ℤ) : ℚ) ≤ ((|m| : ℤ) : ℚ) := Int.cast_le.mpr h1
  simpa using this

/-- **prop:reduction.**  Let `q = s/t` and `z_0 = a/b` with `t, b > 0`, and suppose
    `G(q, z_0) = 0`, so that `P_N(q,z_0) = -R_N(q,z_0)`.  If `P_N(q,z_0) /= 0` and the remainder
    is below the Liouville floor `t^{-(2N^2+N)} b^{-N}`, then `False`.

    Every hypothesis is exactly one of the note's: `hzero` is `G(q,z_0)=0`, `hne` is the
    non-vanishing of the form, and `hsmall` is the remainder estimate of `prop:secondkind`. -/
theorem reduction (N : ℕ) (s t a b : ℤ) (ht : 0 < t) (hb : 0 < b) (R : ℚ)
    (hzero : Pval N ((s : ℚ) / t) ((a : ℚ) / b) = -R)
    (hne : Pval N ((s : ℚ) / t) ((a : ℚ) / b) ≠ 0)
    (hsmall : |R| < ((t : ℚ) ^ (2 * N ^ 2 + N) * (b : ℚ) ^ N)⁻¹) : False := by
  have ht' : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have hb' : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have htne : (t : ℚ) ≠ 0 := ne_of_gt ht'
  have hbne : (b : ℚ) ≠ 0 := ne_of_gt hb'
  set D : ℚ := (t : ℚ) ^ (2 * N ^ 2 + N) * (b : ℚ) ^ N with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hc : (cleared N s t a b : ℚ) = D * Pval N ((s : ℚ) / t) ((a : ℚ) / b) :=
    cleared_eq N s t a b htne hbne
  have hcne : cleared N s t a b ≠ 0 := by
    intro h
    rw [h] at hc
    simp only [Int.cast_zero] at hc
    exact hne (by
      have := (mul_eq_zero.mp hc.symm).resolve_left (ne_of_gt hDpos)
      exact this)
  have hlow : (1 : ℚ) ≤ |(cleared N s t a b : ℚ)| := one_le_abs_of_ne_zero hcne
  have hhigh : |(cleared N s t a b : ℚ)| < 1 := by
    rw [hc, hzero, abs_mul, abs_neg, abs_of_pos hDpos]
    calc D * |R| < D * D⁻¹ := mul_lt_mul_of_pos_left hsmall hDpos
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hDpos)
  linarith

/-! ## 4. The margin arithmetic

`prop:reduction` closes by observing that the criterion it produces, `log(t/s) > 2 log t`, is
equivalent to `st < 1` and therefore never holds; `rem:thetabarrier` makes the same observation
for a general theta-decay series, where the criterion reads `s < 1`. -/

/-- **The criterion of `prop:reduction`, in closed form.**  `log(t/s) > 2 log t` iff `st < 1`. -/
theorem margin_iff (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    2 * Real.log t < Real.log (t / s) ↔ s * t < 1 := by
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hs)]
  rw [show (s * t) = (s * t) from rfl]
  constructor
  · intro h
    have h1 : Real.log s + Real.log t < 0 := by linarith
    have h2 : Real.log (s * t) < 0 := by rwa [Real.log_mul (ne_of_gt hs) (ne_of_gt ht)]
    exact (Real.log_neg_iff (by positivity)).mp h2
  · intro h
    have h2 : Real.log (s * t) < 0 := Real.log_neg (by positivity) h
    rw [Real.log_mul (ne_of_gt hs) (ne_of_gt ht)] at h2
    linarith

/-- **The criterion never holds.**  For `q = s/t in (0,1)` with `s, t` positive integers we have
    `s >= 1` and `t >= 1`, hence `st >= 1`: the reduction cannot be closed. -/
theorem margin_fails (s t : ℝ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ¬ (2 * Real.log t < Real.log (t / s)) := by
  intro h
  rw [margin_iff s t (by linarith) (by linarith)] at h
  nlinarith

/-- **`rem:thetabarrier`.**  For a series with theta decay `q^{alpha k^2}` the degree and the
    decay are driven by the same factor, so the criterion reads `s < 1`; with `s >= 1` the
    inequality it needs is false, for every `alpha > 0` and every `N`. -/
theorem theta_barrier (α : ℝ) (hα : 0 < α) (N : ℕ) (s t : ℝ) (hs : 1 ≤ s) (ht : 0 < t) :
    ¬ (α * (N : ℝ) ^ 2 * Real.log t < α * (N : ℝ) ^ 2 * Real.log (t / s)) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hlog : Real.log (t / s) ≤ Real.log t := by
    rw [Real.log_div (ne_of_gt ht) (ne_of_gt hs0)]
    have : 0 ≤ Real.log s := Real.log_nonneg hs
    linarith
  have hcoef : 0 ≤ α * (N : ℝ) ^ 2 := by positivity
  exact not_lt.mpr (mul_le_mul_of_nonneg_left hlog hcoef)

/-- The integral form of the same obstruction: `st < 1` is impossible for positive integers. -/
theorem st_ge_one (s t : ℤ) (hs : 1 ≤ s) (ht : 1 ≤ t) : ¬ (s * t < 1) := by
  intro h
  nlinarith

end QSiegelLedger

/-! ### Axiom audit (Rule 5) -/

#print axioms QSiegelLedger.degree_ledger
#print axioms QSiegelLedger.degree_at_zero
#print axioms QSiegelLedger.degree_lt_of_pos
#print axioms QSiegelLedger.prod_one_sub_div
#print axioms QSiegelLedger.clearedTerm_eq
#print axioms QSiegelLedger.cleared_eq
#print axioms QSiegelLedger.one_le_abs_of_ne_zero
#print axioms QSiegelLedger.reduction
#print axioms QSiegelLedger.margin_iff
#print axioms QSiegelLedger.margin_fails
#print axioms QSiegelLedger.theta_barrier
#print axioms QSiegelLedger.st_ge_one
