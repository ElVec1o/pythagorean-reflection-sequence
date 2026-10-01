/-
CoxeterGrowthAlg.lean
=====================
`prop:coxeter` of `paper/journal/paper4.tex`: the growth series of
`W_m = <x_0,x_1,x_2 | x_i^2, (x_0 x_1)^m>` is
  `W_m(t) = (1+t)(1+t+...+t^{m-1}) / (1-t-t^2-...-t^m)`.

HYPOTHESIS-RELATIVE: Steinberg's formula for the growth series of a Coxeter system is NOT in
Mathlib.  The paper applies it to get
  `1 / W_m(1/t) = 1 - 3/(1+t) + 1/((1+t)(1+t+...+t^{m-1}))`.
That identity enters here as the explicit hypothesis `hSt`.  Proved from it: the displayed closed
form (pure rational-function algebra over a field, via `(t-1) S(t) = t^m - 1` and the reflection
`S(1/t) = t^{-(m-1)} S(t)`).  No sorry.
-/
import Mathlib.Tactic


namespace CoxeterGrowthAlg

open Finset

variable {K : Type*} [Field K]

/-- `S_m(t) = 1 + t + ... + t^{m-1}`. -/
def S (m : ℕ) (t : K) : K := ∑ k ∈ range m, t ^ k

/-- `Den_m(t) = 1 - t - t^2 - ... - t^m`. -/
def Den (m : ℕ) (t : K) : K := 1 - ∑ k ∈ range m, t ^ (k + 1)

theorem inv_pow_mul {u : K} (hu : u ≠ 0) (a b : ℕ) : u⁻¹ ^ (a + b) * u ^ b = u⁻¹ ^ a := by
  rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]

theorem S_inv (m : ℕ) (hm : 1 ≤ m) {u : K} (hu : u ≠ 0) :
    S m u⁻¹ = u⁻¹ ^ (m - 1) * S m u := by
  unfold S
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have e : u⁻¹ ^ (m - 1 - k) = u⁻¹ ^ (m - 1) * u ^ k := by
    have := inv_pow_mul hu (m - 1 - k) k
    rw [show m - 1 - k + k = m - 1 by omega] at this
    exact this.symm
  rw [inv_pow, ← inv_pow, e]

theorem geom_S (m : ℕ) (t : K) : (t - 1) * S m t = t ^ m - 1 := by
  unfold S
  rw [mul_comm]; exact geom_sum_mul t m

/-- `Den_m(u) = u^m * (u^{-m} - S_m(u^{-1}))`, the reflected numerator. -/
theorem Den_reflect (m : ℕ) (hm : 1 ≤ m) {u : K} (hu : u ≠ 0) :
    u⁻¹ ^ m - S m u⁻¹ = u⁻¹ ^ m * Den m u := by
  unfold S Den
  rw [mul_sub, mul_one, Finset.mul_sum]
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have e : u⁻¹ ^ (m - 1 - k) = u⁻¹ ^ m * u ^ (k + 1) := by
    have := inv_pow_mul hu (m - 1 - k) (k + 1)
    rw [show m - 1 - k + (k + 1) = m by omega] at this
    exact (by
      have h2 := inv_pow_mul hu m (k + 1)
      -- u⁻¹^(m-1-k) = u⁻¹^m * u^(k+1) follows from this : u⁻¹^m * u^(k+1) = u⁻¹^(m-1-k)
      exact this.symm)
  exact e

/-- **`prop:coxeter`, relative to Steinberg's formula.**  If `W` satisfies
`1/W(1/t) = 1 - 3/(1+t) + 1/((1+t) S_m(t))` for the relevant `t`, then
`W(u) = (1+u) S_m(u) / Den_m(u)`. -/
theorem prop_coxeter (m : ℕ) (hm : 1 ≤ m) (W : K → K)
    (hSt : ∀ t : K, t ≠ 0 → 1 + t ≠ 0 → S m t ≠ 0 →
      1 / W t⁻¹ = 1 - 3 / (1 + t) + 1 / ((1 + t) * S m t))
    {u : K} (hu : u ≠ 0) (h1 : 1 + u ≠ 0) (hS : S m u ≠ 0) (hD : Den m u ≠ 0) (hW : W u ≠ 0) :
    W u = (1 + u) * S m u / Den m u := by
  have hui : u⁻¹ ≠ 0 := inv_ne_zero hu
  have h1i : 1 + u⁻¹ ≠ 0 := by
    intro h
    apply h1
    have : u * (1 + u⁻¹) = 1 + u := by field_simp <;> ring
    rw [← this, h, mul_zero]
  have hSi : S m u⁻¹ ≠ 0 := by
    rw [S_inv m hm hu]
    exact mul_ne_zero (pow_ne_zero _ hui) hS
  have key := hSt u⁻¹ hui h1i hSi
  rw [inv_inv] at key
  -- evaluate the right-hand side
  have e1 : (1 + u⁻¹) = (1 + u) * u⁻¹ := by field_simp <;> ring
  have hgeo := geom_S m u⁻¹
  have hrefl := Den_reflect m hm hu
  have hSinv := S_inv m hm hu
  have hpm : u⁻¹ ^ m = u⁻¹ ^ (m - 1) * u⁻¹ := by
    rw [← pow_succ]; congr 1; omega
  have hrhs : 1 - 3 / (1 + u⁻¹) + 1 / ((1 + u⁻¹) * S m u⁻¹) =
      Den m u / ((1 + u) * S m u) := by
    have hnum : u⁻¹ ^ m - S m u⁻¹ = (u⁻¹ - 2) * S m u⁻¹ + 1 := by
      have : u⁻¹ ^ m = (u⁻¹ - 1) * S m u⁻¹ + 1 := by linear_combination (-1 : K) * hgeo
      rw [this]; ring
    have hden : (1 + u⁻¹) * S m u⁻¹ = u⁻¹ ^ m * ((1 + u) * S m u) := by
      rw [e1, hSinv, hpm]; ring
    have hden0 : (1 + u⁻¹) * S m u⁻¹ ≠ 0 := mul_ne_zero h1i hSi
    have gen : ∀ x y : K, x ≠ 0 → y ≠ 0 → (1 : K) - 3 / x + 1 / (x * y) = ((x - 3) * y + 1) / (x * y) := by
      intro x y hx hy
      field_simp
    have hX := gen (1 + u⁻¹) (S m u⁻¹) h1i hSi
    have h13 : (1 + u⁻¹) - 3 = u⁻¹ - 2 := by ring
    rw [h13] at hX
    rw [hX, ← hnum, hrefl, hden]
    have hpow : u⁻¹ ^ m ≠ 0 := pow_ne_zero _ hui
    field_simp
  rw [hrhs] at key
  have : W u = 1 / (Den m u / ((1 + u) * S m u)) := by
    rw [← key]; field_simp
  rw [this]
  field_simp

end CoxeterGrowthAlg

#print axioms CoxeterGrowthAlg.prop_coxeter
