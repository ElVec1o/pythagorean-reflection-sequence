/-
Paper1TierA4.lean
=================
Formalization-debt paydown (2026-09-28): number-theoretic Tier-A items from paper1.tex.

  * `lem:complexity-arith` part (ii) -- DONE.
    Every prime factor of c_T = a²+b² (with gcd(a,b)=1) satisfies p ≡ 1 (mod 4).
    The key tools are:
      • `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime`: n=a²+b² + gcd=1 → IsSquare(-1:ZMod n)
      • `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one`: p∈factors + sq(-1) → p%4≠3
    From p prime, p≠2 (since n odd), p%4≠3 and p%4<4 we conclude p%4=1.

  * `lem:complexity-arith` part (iii) -- DONE (conditional on oddness hypothesis).
    If c_T = a²+b² > 1, gcd(a,b)=1, and a²+b² is odd, then a²+b² ≥ 5.
    Proof: oddness excludes the factor 2; every prime factor then satisfies p%4=1, so p≥5;
    hence n ≥ n.minFac ≥ 5.

No `sorry`.
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.SumTwoSquares

namespace Paper1TierA4

-- ─────────────────────────────────────────────────────────────────────────────
-- lem:complexity-arith part (ii): prime factors of a²+b² with gcd(a,b)=1 are ≡1 mod 4
-- ─────────────────────────────────────────────────────────────────────────────

/-- A prime factor of a²+b² (with gcd(a,b)=1) does not equal 3 mod 4. -/
theorem prime_factor_ne_three_mod_four {a b : ℕ} (hcop : Nat.Coprime a b)
    {p : ℕ} (hmem : p ∈ (a ^ 2 + b ^ 2).primeFactors) : p % 4 ≠ 3 :=
  Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hmem
    (ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime rfl hcop)

/-- An odd prime factor of a²+b² (with gcd(a,b)=1) is ≡1 mod 4. -/
theorem odd_prime_factor_eq_one_mod_four {a b : ℕ} (hcop : Nat.Coprime a b)
    {p : ℕ} (hprime : p.Prime) (hdvd : p ∣ a ^ 2 + b ^ 2) (hodd : p ≠ 2) : p % 4 = 1 := by
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h
    have ha : a = 0 := by nlinarith [Nat.zero_le (a ^ 2), Nat.zero_le (b ^ 2)]
    have hb : b = 0 := by nlinarith [Nat.zero_le (a ^ 2), Nat.zero_le (b ^ 2)]
    simp [ha, hb, Nat.Coprime] at hcop
  have hmem : p ∈ (a ^ 2 + b ^ 2).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hab⟩
  have hp4 : p % 4 ≠ 3 := prime_factor_ne_three_mod_four hcop hmem
  have hmod2 : p % 2 = 1 := by
    have : p % 2 ≠ 0 := by
      intro h
      have h2p : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
      rcases hprime.eq_one_or_self_of_dvd 2 h2p with h | h
      · exact absurd h (by decide)
      · exact hodd h.symm
    omega
  omega

-- Small examples: 5, 13, 17, 29, 37 are the first primes ≡1 mod 4.
example : (5 : ℕ) % 4 = 1 := by decide
example : (13 : ℕ) % 4 = 1 := by decide
example : (5 : ℕ).Prime ∧ (5 : ℕ) ∣ 1 ^ 2 + 2 ^ 2 := ⟨by decide, by decide⟩
example : (13 : ℕ).Prime ∧ (13 : ℕ) ∣ 2 ^ 2 + 3 ^ 2 := ⟨by decide, by decide⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- lem:complexity-arith part (iii): c_T ≥ 5 when c_T > 1
-- ─────────────────────────────────────────────────────────────────────────────
-- In the paper, c_T = a²+b² is always ODD (proven as part (i) from the parity of
-- the primitive Gaussian integer μ_T = a+bi with a XOR b odd; the geometric input
-- that forces exactly one of a, b to be odd is not formalized here).
-- We state the arithmetic consequence: given oddness + coprimeness + c_T > 1 → c_T ≥ 5.

/-- If n = a²+b² is odd, gcd(a,b)=1, and n > 1, then n ≥ 5. -/
theorem complexity_arith_ge_five {a b : ℕ} (hcop : Nat.Coprime a b)
    (hgt : a ^ 2 + b ^ 2 > 1) (hodd : Odd (a ^ 2 + b ^ 2)) : a ^ 2 + b ^ 2 ≥ 5 := by
  set n := a ^ 2 + b ^ 2 with hn_def
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hmin_prime : n.minFac.Prime := Nat.minFac_prime hn1
  have hmin_dvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hmin_odd : n.minFac ≠ 2 := by
    intro h2
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨j, hj⟩ := h2 ▸ hmin_dvd
    omega
  have hmin_mod : n.minFac % 4 = 1 :=
    odd_prime_factor_eq_one_mod_four hcop hmin_prime hmin_dvd hmin_odd
  have hmin_ge5 : n.minFac ≥ 5 := by
    have := hmin_prime.two_le; omega
  exact le_trans hmin_ge5 (Nat.le_of_dvd (by omega) hmin_dvd)

-- ─────────────────────────────────────────────────────────────────────────────
-- Concrete verification for standard examples
-- ─────────────────────────────────────────────────────────────────────────────

-- c_T = 5 = 1²+2² (primitive, odd, prime ≡1 mod 4): the minimum c_T > 1
example : (5 : ℕ) = 1 ^ 2 + 2 ^ 2 := by decide
example : Nat.Coprime 1 2 := by decide
example : Odd (1 ^ 2 + 2 ^ 2) := by decide

-- c_T = 13 = 2²+3²
example : (13 : ℕ) = 2 ^ 2 + 3 ^ 2 := by decide
example : Nat.Coprime 2 3 := by decide
example : Odd (2 ^ 2 + 3 ^ 2) := by decide

-- c_T = 25 = 3²+4² = 5² (illustrates that c_T can be a prime power, not prime)
example : (25 : ℕ) = 3 ^ 2 + 4 ^ 2 := by decide
example : Nat.Coprime 3 4 := by decide
example : Odd (3 ^ 2 + 4 ^ 2) := by decide

end Paper1TierA4
