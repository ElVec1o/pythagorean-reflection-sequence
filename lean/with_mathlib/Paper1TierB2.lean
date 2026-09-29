/-
Paper1TierB2.lean  (2026-09-29)
================================
Tier-B: `lem:class-separation` (paper1).
  For coprime positive naturals a ≠ b, 2·arctan(b/a) is not a rational multiple of π.

Proof:
  (a) cos(2·arctan(x)) = (1 - x²)/(1 + x²)
  (b) (a²-b²)/(a²+b²) ∉ {-1,-1/2,0,1/2,1}  for coprime a≠b positives
  (c) Niven's theorem (Mathlib `Real.niven`) closes it.

No `sorry`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.NumberTheory.Niven
import Mathlib.Tactic

namespace Paper1TierB2

open Real

-- ─────────────────────────────────────────────────────────────────────────────
-- (a) double-angle cosine formula via arctan
-- ─────────────────────────────────────────────────────────────────────────────

theorem cos_two_arctan (x : ℝ) : cos (2 * arctan x) = (1 - x ^ 2) / (1 + x ^ 2) := by
  have h : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  rw [cos_two_mul, cos_sq_arctan]
  field_simp
  ring

theorem cos_two_arctan_ratio {a b : ℝ} (ha : a ≠ 0) :
    cos (2 * arctan (b / a)) = (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) := by
  rw [cos_two_arctan]
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  field_simp [ha2]

-- ─────────────────────────────────────────────────────────────────────────────
-- small helper
-- ─────────────────────────────────────────────────────────────────────────────

private lemma nat_eq_of_real_sq_eq {a b : ℕ} (ha : (a : ℝ) > 0) (hb : (b : ℝ) > 0)
    (h : (a : ℝ) ^ 2 = b ^ 2) : a = b := by
  have factored : ((a : ℝ) - b) * (a + b) = 0 := by nlinarith
  have sum_pos : (a : ℝ) + b > 0 := by linarith
  have hab_r : (a : ℝ) = b := by linarith [(mul_eq_zero.mp factored).resolve_right (by linarith)]
  exact_mod_cast hab_r

-- ─────────────────────────────────────────────────────────────────────────────
-- (b) none of the 5 Niven values is achieved
-- ─────────────────────────────────────────────────────────────────────────────

theorem arctan_ratio_cos_not_niven {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hcop : Nat.Coprime a b) :
    (a ^ 2 - b ^ 2 : ℝ) / (a ^ 2 + b ^ 2) ∉ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  have ha_r : (a : ℝ) > 0 := Nat.cast_pos.mpr ha
  have hb_r : (b : ℝ) > 0 := Nat.cast_pos.mpr hb
  have ha2 : (a : ℝ) ^ 2 > 0 := sq_pos_of_pos ha_r
  have hb2 : (b : ℝ) ^ 2 > 0 := sq_pos_of_pos hb_r
  have hS' : (a ^ 2 + b ^ 2 : ℝ) ≠ 0 := by positivity
  -- coprimeness: 3 cannot divide both a and b
  have cop_no_3 : ¬ (3 ∣ a ∧ 3 ∣ b) := fun ⟨h3a, h3b⟩ => by
    have : 3 ∣ Nat.gcd a b := Nat.dvd_gcd h3a h3b
    rw [hcop] at this; exact absurd this (by norm_num)
  -- Case -1: a²-b² = -(a²+b²) → 2a² = 0, impossible
  have h_neg1 : (a ^ 2 - b ^ 2 : ℝ) / (a ^ 2 + b ^ 2) ≠ -1 := by
    intro h
    have heq : (a : ℝ) ^ 2 - b ^ 2 = -(a ^ 2 + b ^ 2) := by
      rwa [div_eq_iff hS', neg_one_mul] at h
    linarith
  -- Case -1/2: 2(a²-b²) = -(a²+b²) → b² = 3a² → 3|b and 3|a → gcd ≥ 3
  have h_neg12 : (a ^ 2 - b ^ 2 : ℝ) / (a ^ 2 + b ^ 2) ≠ -1 / 2 := by
    intro h
    have heq : (b : ℝ) ^ 2 = 3 * a ^ 2 := by
      have := (div_eq_div_iff hS' (by norm_num : (2:ℝ) ≠ 0)).mp h
      linarith
    have h3n : b ^ 2 = 3 * a ^ 2 := by exact_mod_cast heq
    have h3b : 3 ∣ b := Nat.Prime.dvd_of_dvd_pow (by norm_num) ⟨a ^ 2, h3n⟩
    obtain ⟨c, hc⟩ := h3b
    have h3a : 3 ∣ a := by
      have hb2 : b ^ 2 = 9 * c ^ 2 := by rw [hc]; ring
      have hac : a ^ 2 = 3 * c ^ 2 := by omega
      exact Nat.Prime.dvd_of_dvd_pow (by norm_num) ⟨c ^ 2, hac⟩
    exact cop_no_3 ⟨h3a, ⟨c, hc⟩⟩
  -- Case 0: a² = b² → a = b, contradicts a ≠ b
  have h_zero : (a ^ 2 - b ^ 2 : ℝ) / (a ^ 2 + b ^ 2) ≠ 0 := by
    intro h
    rw [div_eq_zero_iff, or_iff_left hS'] at h
    exact hab (nat_eq_of_real_sq_eq ha_r hb_r (by linarith))
  -- Case 1/2: 2(a²-b²) = a²+b² → a² = 3b² → 3|a and 3|b → gcd ≥ 3
  have h_12 : (a ^ 2 - b ^ 2 : ℝ) / (a ^ 2 + b ^ 2) ≠ 1 / 2 := by
    intro h
    have heq : (a : ℝ) ^ 2 = 3 * b ^ 2 := by
      have := (div_eq_div_iff hS' (by norm_num : (2:ℝ) ≠ 0)).mp h
      linarith
    have h3n : a ^ 2 = 3 * b ^ 2 := by exact_mod_cast heq
    have h3a : 3 ∣ a := Nat.Prime.dvd_of_dvd_pow (by norm_num) ⟨b ^ 2, h3n⟩
    obtain ⟨c, hc⟩ := h3a
    have h3b : 3 ∣ b := by
      have ha2 : a ^ 2 = 9 * c ^ 2 := by rw [hc]; ring
      have hbc : b ^ 2 = 3 * c ^ 2 := by omega
      exact Nat.Prime.dvd_of_dvd_pow (by norm_num) ⟨c ^ 2, hbc⟩
    exact cop_no_3 ⟨⟨c, hc⟩, h3b⟩
  -- Case 1: a²-b² = a²+b² → 2b² = 0, impossible
  have h_1 : (a ^ 2 - b ^ 2 : ℝ) / (a ^ 2 + b ^ 2) ≠ 1 := by
    intro h
    have heq : (a : ℝ) ^ 2 - b ^ 2 = a ^ 2 + b ^ 2 := (div_eq_one_iff_eq hS').mp h
    linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  push Not
  exact ⟨h_neg1, h_neg12, h_zero, h_12, h_1⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- (c) Main: lem:class-separation
-- ─────────────────────────────────────────────────────────────────────────────

/-- `lem:class-separation`: for coprime positive naturals a ≠ b,
    2·arctan(b/a) is not a rational multiple of π. -/
theorem arctan_ratio_not_rat_mul_pi {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hcop : Nat.Coprime a b) :
    ∀ r : ℚ, 2 * arctan ((b : ℝ) / a) ≠ r * π := by
  intro r hr
  have ha_r : (a : ℝ) > 0 := Nat.cast_pos.mpr ha
  have hS : (a ^ 2 + b ^ 2 : ℝ) > 0 := by positivity
  have hS' := hS.ne'
  have hcos_val : cos (2 * arctan ((b : ℝ) / a)) = (a ^ 2 - b ^ 2 : ℝ) / (a ^ 2 + b ^ 2) :=
    cos_two_arctan_ratio ha_r.ne'
  -- cosine equals a rational; use ℚ arithmetic
  have hcos_rat : ∃ q : ℚ, cos (2 * arctan ((b : ℝ) / a)) = (q : ℝ) := by
    use ((a : ℚ) ^ 2 - b ^ 2) / ((a : ℚ) ^ 2 + b ^ 2)
    rw [hcos_val]
    push_cast
    ring
  -- Niven: cos(r·π) ∈ {-1,-1/2,0,1/2,1}
  have hNiven : cos (2 * arctan ((b : ℝ) / a)) ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) :=
    niven ⟨r, hr⟩ hcos_rat
  rw [hcos_val] at hNiven
  exact arctan_ratio_cos_not_niven ha hb hab hcop hNiven

end Paper1TierB2
