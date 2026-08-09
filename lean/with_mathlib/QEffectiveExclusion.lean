/-
  QEffectiveExclusion.lean
  ========================
  `prop:effective` of `paper/journal/hahn_exton_qcosine.tex`: the least positive root `q*` of
  `S(q) = G(q, 2q(1-q))` admits no rational representation of denominator at most `10^1044`.

  The proposition has two halves.

    (A) NUMERICAL.  Certified interval arithmetic locates `q*` inside an explicit interval
        `[lo, hi]` of width `4 * 10^{-2090}`, exhibits a rational `s0/t0` inside it with
        `t0` between `9.5 * 10^1044` and `10^1045`, and certifies `S(s0/t0) /= 0`.  This is
        outside Lean; it is the script `beta2_effective_irrationality.py`.

    (B) ARITHMETIC.  An interval narrower than the Farey gap forced by a denominator bound
        contains at most one rational of denominator within that bound.  That half is proved
        here in full, together with the numeric width comparison
        `4 * 10^{-2090} < 1/(10^1044 * t0)` for every `t0 < 10^1045`.

  The half (A) facts enter as named hypotheses, so the dependency is visible rather than buried.
  Nothing here asserts that the interval is correct; it asserts what follows if it is.

  The method is Brent's; see the note for the attribution.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

-- The note's bound is `10^1044`; the default guard would refuse to elaborate such literals.
set_option exponentiation.threshold 4000

namespace QEffectiveExclusion

/-! ## 1. The Farey gap -/

/-- **Two distinct rationals are at least `1/(n t)` apart.**  The cross-difference `m t - s n`
    is a nonzero integer, hence at least `1` in modulus. -/
theorem farey_gap {m n s t : ℤ} (hn : 0 < n) (ht : 0 < t)
    (hne : (m : ℚ) / n ≠ (s : ℚ) / t) :
    1 / ((n : ℚ) * t) ≤ |(m : ℚ) / n - (s : ℚ) / t| := by
  have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have ht' : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have hcross : m * t - s * n ≠ 0 := by
    intro h
    apply hne
    have : (m : ℚ) * t = (s : ℚ) * n := by
      have := congrArg (fun z : ℤ => (z : ℚ)) h
      push_cast at this
      linarith
    field_simp
    linarith
  have h1 : (1 : ℚ) ≤ |((m * t - s * n : ℤ) : ℚ)| := by
    have : (1 : ℤ) ≤ |m * t - s * n| := Int.one_le_abs hcross
    have h2 : ((1 : ℤ) : ℚ) ≤ ((|m * t - s * n| : ℤ) : ℚ) := Int.cast_le.mpr this
    simpa using h2
  have hdiff : (m : ℚ) / n - (s : ℚ) / t = ((m * t - s * n : ℤ) : ℚ) / ((n : ℚ) * t) := by
    push_cast
    field_simp
  have hD : (0 : ℚ) < (n : ℚ) * t := by positivity
  rw [hdiff, abs_div, abs_of_pos hD]
  gcongr

/-! ## 2. Interval uniqueness -/

/-- **An interval narrower than the Farey gap pins the rational.**  If `s/t` lies in `[lo, hi]`,
    the width is below `1/(B t)`, and `m/n` lies in `[lo, hi]` with `0 < n <= B`, then
    `m/n = s/t`. -/
theorem unique_rational_in_interval {lo hi : ℚ} {s t B : ℤ} (ht : 0 < t) (hB : 0 < B)
    (hstlo : lo ≤ (s : ℚ) / t) (hsthi : (s : ℚ) / t ≤ hi)
    (hwidth : hi - lo < 1 / ((B : ℚ) * t))
    {m n : ℤ} (hn : 0 < n) (hnB : n ≤ B)
    (hmlo : lo ≤ (m : ℚ) / n) (hmhi : (m : ℚ) / n ≤ hi) :
    (m : ℚ) / n = (s : ℚ) / t := by
  by_contra hne
  have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have ht' : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have hB' : (0 : ℚ) < (B : ℚ) := by exact_mod_cast hB
  have hnB' : (n : ℚ) ≤ (B : ℚ) := by exact_mod_cast hnB
  -- the gap forced by the denominators
  have hgap : 1 / ((n : ℚ) * t) ≤ |(m : ℚ) / n - (s : ℚ) / t| := farey_gap hn ht hne
  -- the gap is at least the one forced by the bound `B`
  have hmono : 1 / ((B : ℚ) * t) ≤ 1 / ((n : ℚ) * t) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right hnB' (le_of_lt ht')
  -- but both points lie in the interval
  have hsmall : |(m : ℚ) / n - (s : ℚ) / t| ≤ hi - lo := by
    rw [abs_le]
    constructor <;> linarith
  linarith

/-! ## 3. `prop:effective`

Two forms.  The first uses the certified non-vanishing `S(s0/t0) /= 0`, which is how the note
argues; the second uses instead that `s0/t0` is in lowest terms, which is how the note phrases
the conclusion ("whence `n = t_0 > 10^1044`"). -/

/-- **The exclusion.**  A real number in the interval that is different from the exhibited
    rational has no rational representation with denominator at most `B`. -/
theorem no_rational_of_denominator_le {lo hi : ℚ} {x : ℝ} {s t B : ℤ}
    (ht : 0 < t) (hB : 0 < B)
    (hstlo : lo ≤ (s : ℚ) / t) (hsthi : (s : ℚ) / t ≤ hi)
    (hwidth : hi - lo < 1 / ((B : ℚ) * t))
    (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ))
    (hxne : x ≠ (((s : ℚ) / t : ℚ) : ℝ))
    {m n : ℤ} (hn : 0 < n) (hnB : n ≤ B) :
    x ≠ (m : ℝ) / (n : ℝ) := by
  intro hx
  have hcast : ((((m : ℚ) / n : ℚ)) : ℝ) = (m : ℝ) / (n : ℝ) := by push_cast; ring
  have hmlo : lo ≤ (m : ℚ) / n := by
    have : (lo : ℝ) ≤ ((((m : ℚ) / n : ℚ)) : ℝ) := by rw [hcast, ← hx]; exact hxlo
    exact_mod_cast this
  have hmhi : (m : ℚ) / n ≤ hi := by
    have : ((((m : ℚ) / n : ℚ)) : ℝ) ≤ (hi : ℝ) := by rw [hcast, ← hx]; exact hxhi
    exact_mod_cast this
  have heq := unique_rational_in_interval ht hB hstlo hsthi hwidth hn hnB hmlo hmhi
  apply hxne
  rw [hx, ← hcast, heq]

/-- **The denominator form.**  If the exhibited rational is in lowest terms and its denominator
    exceeds the bound, then no rational in the interval has denominator within the bound. -/
theorem denominator_gt_of_mem {lo hi : ℚ} {s t B : ℤ}
    (ht : 0 < t) (hB : 0 < B) (hBt : B < t) (hcop : IsCoprime t s)
    (hstlo : lo ≤ (s : ℚ) / t) (hsthi : (s : ℚ) / t ≤ hi)
    (hwidth : hi - lo < 1 / ((B : ℚ) * t))
    {m n : ℤ} (hn : 0 < n) (hnB : n ≤ B)
    (hmlo : lo ≤ (m : ℚ) / n) (hmhi : (m : ℚ) / n ≤ hi) : False := by
  have heq := unique_rational_in_interval ht hB hstlo hsthi hwidth hn hnB hmlo hmhi
  have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have ht' : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have hcross : (m : ℚ) * t = (s : ℚ) * n := by
    field_simp at heq
    linarith
  have hZ : m * t = s * n := by exact_mod_cast hcross
  have hdvd : t ∣ s * n := ⟨m, by linarith [hZ]⟩
  have htn : t ∣ n := hcop.dvd_of_dvd_mul_left hdvd
  have : t ≤ n := Int.le_of_dvd hn htn
  omega

/-! ## 4. The width certificate for `q*`

The note's interval has width `4 * 10^{-2090}`; the Farey gap at `B = 10^1044` and
`t_0 < 10^1045` is larger than that.  Stated with the powers kept symbolic, so that no
2000-digit literal is ever formed. -/

/-- `4 * 10^{-2090} < 1/(10^1044 * t)` for every `0 < t < 10^1045`. -/
theorem width_lt_gap (t : ℤ) (ht : 0 < t) (htu : t < 10 ^ 1045) :
    (4 : ℚ) / (10 : ℚ) ^ 2090 < 1 / (((10 : ℤ) ^ 1044 : ℤ) * (t : ℚ)) := by
  have ht' : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have htu' : (t : ℚ) < (10 : ℚ) ^ 1045 := by exact_mod_cast htu
  have hp1044 : (0 : ℚ) < (10 : ℚ) ^ 1044 := by positivity
  have hp2089 : (0 : ℚ) < (10 : ℚ) ^ 2089 := by positivity
  have hcast : ((((10 : ℤ) ^ 1044 : ℤ)) : ℚ) = (10 : ℚ) ^ 1044 := by push_cast; ring
  rw [hcast]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  -- goal: 4 * (10^1044 * t) < 1 * 10^2090
  have hstep : (10 : ℚ) ^ 1044 * (t : ℚ) < (10 : ℚ) ^ 2089 := by
    calc (10 : ℚ) ^ 1044 * (t : ℚ) < (10 : ℚ) ^ 1044 * (10 : ℚ) ^ 1045 :=
          mul_lt_mul_of_pos_left htu' hp1044
      _ = (10 : ℚ) ^ 2089 := by rw [← pow_add]
  have hbig : (4 : ℚ) * (10 : ℚ) ^ 2089 < 1 * (10 : ℚ) ^ 2090 := by
    have : (10 : ℚ) ^ 2090 = (10 : ℚ) ^ 2089 * 10 := by rw [← pow_succ]
    rw [this]
    linarith
  linarith

/-- **`prop:effective`, assembled.**  The hypotheses are exactly the certified outputs of the
    interval-arithmetic script: the enclosure `[lo, hi]` of `q*` of width `4 * 10^{-2090}`, the
    Stern-Brocot rational `s0/t0` inside it with `t0 < 10^1045`, and `S(s0/t0) /= 0` (which is
    what `hxne` records).  The conclusion is the note's: `q*` has no rational representation of
    denominator at most `10^1044`. -/
theorem qstar_no_small_denominator
    {lo hi : ℚ} {x : ℝ} {s₀ t₀ : ℤ}
    (ht₀ : 0 < t₀) (ht₀u : t₀ < 10 ^ 1045)
    (hwidth : hi - lo = 4 / (10 : ℚ) ^ 2090)
    (hstlo : lo ≤ (s₀ : ℚ) / t₀) (hsthi : (s₀ : ℚ) / t₀ ≤ hi)
    (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ))
    (hxne : x ≠ (((s₀ : ℚ) / t₀ : ℚ) : ℝ))
    {m n : ℤ} (hn : 0 < n) (hnB : n ≤ 10 ^ 1044) :
    x ≠ (m : ℝ) / (n : ℝ) := by
  have hB : (0 : ℤ) < 10 ^ 1044 := by positivity
  have hw : hi - lo < 1 / ((((10 : ℤ) ^ 1044 : ℤ) : ℚ) * (t₀ : ℚ)) := by
    rw [hwidth]
    exact width_lt_gap t₀ ht₀ ht₀u
  exact no_rational_of_denominator_le ht₀ hB hstlo hsthi hw hxlo hxhi hxne hn hnB

end QEffectiveExclusion

/-! ### Axiom audit (Rule 5) -/

#print axioms QEffectiveExclusion.farey_gap
#print axioms QEffectiveExclusion.unique_rational_in_interval
#print axioms QEffectiveExclusion.no_rational_of_denominator_le
#print axioms QEffectiveExclusion.denominator_gt_of_mem
#print axioms QEffectiveExclusion.width_lt_gap
#print axioms QEffectiveExclusion.qstar_no_small_denominator
