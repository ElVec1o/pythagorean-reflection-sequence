/-
Paper1TierA3.lean
=================
Formalization-debt paydown (2026-09-28): arithmetic Tier-A items from paper1.tex.

  * `thm:non-universality-restate` (arithmetic parts) -- DONE.
    Word-length arithmetic: 6c+2+6e+2+6c+4 = 6(2c+e)+8 and ≤ 24c+8 when e ≤ 2c.
    Pure omega.

  * `lem:complexity-arith` part (i) -- DONE.
    c_T is odd: both branches (mixed parity, both-odd) proved via Odd/Even API.

  * `lem:complexity-arith` part (iv) -- PARTIAL.
    μ_T primitive: the key step (common divisors of a²+b² and a²-b² divide 2·gcd(a,b)²)
    is proved.  The final coprimality conclusion (gcd=1 when gcd(a,b)=1) is documented
    but requires combining with part (i) (c_T odd) — that final step is left with a
    comment explaining the remaining gap.

No `sorry`.
-/
import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic

namespace Paper1TierA3

-- ─────────────────────────────────────────────────────────────────────────────
-- thm:non-universality-restate (arithmetic parts)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Word-length count: 6c+2+6e+2+6c+4 = 6(2c+e)+8. -/
theorem non_universality_word_length (c e : ℕ) :
    6 * c + 2 + 6 * e + 2 + 6 * c + 4 = 6 * (2 * c + e) + 8 := by omega

/-- Word-length bound: 6(2c+e)+8 ≤ 24c+8 when e ≤ 2c. -/
theorem non_universality_length_bound (c e : ℕ) (he : e ≤ 2 * c) :
    6 * (2 * c + e) + 8 ≤ 24 * c + 8 := by omega

/-- Combined: word length ≤ 24c+8. -/
theorem non_universality_combined (c e : ℕ) (he : e ≤ 2 * c) :
    6 * c + 2 + 6 * e + 2 + 6 * c + 4 ≤ 24 * c + 8 := by omega

-- ─────────────────────────────────────────────────────────────────────────────
-- lem:complexity-arith part (i): c_T is odd
-- ─────────────────────────────────────────────────────────────────────────────

/-- Branch 1 (a odd, b even): a²+b² is odd. -/
theorem sq_add_sq_odd_of_odd_even (a b : ℤ)
    (ha : Odd a) (hb : Even b) : Odd (a ^ 2 + b ^ 2) := by
  obtain ⟨k, rfl⟩ := ha; obtain ⟨l, rfl⟩ := hb
  exact ⟨2 * k ^ 2 + 2 * k + 2 * l ^ 2, by ring⟩

/-- Branch 1′ (a even, b odd): a²+b² is odd. -/
theorem sq_add_sq_odd_of_even_odd (a b : ℤ)
    (ha : Even a) (hb : Odd b) : Odd (a ^ 2 + b ^ 2) := by
  obtain ⟨k, rfl⟩ := ha; obtain ⟨l, rfl⟩ := hb
  exact ⟨2 * k ^ 2 + 2 * l ^ 2 + 2 * l, by ring⟩

/-- Auxiliary: if both a, b are odd then 4 | (a²+b²-2). -/
theorem four_dvd_sq_sq_sub_two_of_both_odd (a b : ℤ)
    (ha : Odd a) (hb : Odd b) : 4 ∣ (a ^ 2 + b ^ 2 - 2) := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨l, rfl⟩ := hb
  exact ⟨k ^ 2 + k + l ^ 2 + l, by ring⟩

/-- Branch 2 (both odd): (a²+b²)/2 is odd. -/
theorem sq_add_sq_half_odd_of_both_odd (a b : ℤ)
    (ha : Odd a) (hb : Odd b) : Odd ((a ^ 2 + b ^ 2) / 2) := by
  obtain ⟨m, hm⟩ := four_dvd_sq_sq_sub_two_of_both_odd a b ha hb
  have heq : a ^ 2 + b ^ 2 = 2 * (2 * m + 1) := by linarith
  exact ⟨m, by omega⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- lem:complexity-arith part (iv): μ_T is primitive (key divisibility steps)
-- ─────────────────────────────────────────────────────────────────────────────
-- In the a+b-odd branch: c_T = a²+b², e_T = a²-b².
-- Key step: any d dividing both a²+b² and a²-b² divides 2a² and 2b².

/-- A common divisor of a²+b² and a²-b² divides 2a². -/
theorem common_div_to_2a_sq (a b d : ℤ) (h1 : d ∣ a ^ 2 + b ^ 2)
    (h2 : d ∣ a ^ 2 - b ^ 2) : d ∣ 2 * a ^ 2 := by
  have := Int.dvd_add h1 h2
  simpa [show a ^ 2 + b ^ 2 + (a ^ 2 - b ^ 2) = 2 * a ^ 2 by ring] using this

/-- A common divisor of a²+b² and a²-b² divides 2b². -/
theorem common_div_to_2b_sq (a b d : ℤ) (h1 : d ∣ a ^ 2 + b ^ 2)
    (h2 : d ∣ a ^ 2 - b ^ 2) : d ∣ 2 * b ^ 2 := by
  have := Int.dvd_sub h1 h2
  simpa [show a ^ 2 + b ^ 2 - (a ^ 2 - b ^ 2) = 2 * b ^ 2 by ring] using this

/-- For coprime a, b: any odd prime p dividing both a²+b² and a²-b² leads to p | a and p | b,
    contradicting gcd(a,b)=1.  We prove the key step: from p | 2a² and ¬(p | 2) we get p | a. -/
theorem odd_prime_dvd_of_dvd_sq {p a : ℤ} (hp : Prime p) (hp2 : ¬(p ∣ 2))
    (h : p ∣ 2 * a ^ 2) : p ∣ a := by
  rcases hp.dvd_or_dvd h with h2 | ha2
  · exact absurd h2 hp2
  · exact hp.dvd_of_dvd_pow ha2

/-- Primitivity summary (a+b-odd branch): if p is an odd prime dividing gcd(a²+b², a²-b²),
    and IsCoprime a b, then p ∣ a AND p ∣ b, which contradicts IsCoprime a b. -/
theorem no_odd_prime_divides_both (a b : ℤ) (hcop : IsCoprime a b)
    (p : ℤ) (hp : Prime p) (hp2 : ¬(p ∣ 2))
    (h1 : p ∣ a ^ 2 + b ^ 2) (h2 : p ∣ a ^ 2 - b ^ 2) : False := by
  have hpa := odd_prime_dvd_of_dvd_sq hp hp2 (common_div_to_2a_sq a b p h1 h2)
  have hpb := odd_prime_dvd_of_dvd_sq hp hp2 (common_div_to_2b_sq a b p h1 h2)
  exact hp.not_unit (hcop.isUnit_of_dvd' hpa hpb)

end Paper1TierA3
