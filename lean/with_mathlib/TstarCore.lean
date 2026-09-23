import Mathlib

namespace TstarCore

/-- One step of the leapfrog: `u₁ = u₀ + t p₀`, `p₁ = p₀ - α (t q) u₁`, where `t = q^s`. -/
theorem drift (q α t u₀ p₀ : ℝ) (hq : q ≠ 0) (hα : α ≠ 0) :
    let u₁ := u₀ + t * p₀
    let p₁ := p₀ - α * (t * q) * u₁
    (u₁ ^ 2 + p₁ ^ 2 / (α * q) + t * q * u₁ * p₁)
      - (u₀ ^ 2 + p₀ ^ 2 / (α * q) + t * u₀ * p₀)
      = -(1 - q) * t * u₁ * p₁ := by
  intro u₁ p₁
  simp only [u₁, p₁]
  field_simp
  ring

/-- Finite summation by parts behind `Σ q^s p_s² = α Σ q^s u_s²` on the level set:
with `u (s+1) - u s = t s * p s` and `p s - p (s-1) = -α t s u s`, `p (-1) = 0`. -/
theorem sbp (N : ℕ) (u p t : ℕ → ℝ) (α : ℝ)
    (hstep : ∀ s, u (s + 1) - u s = t s * p s)
    (hflux0 : p 0 = -α * t 0 * u 0)
    (hflux : ∀ s, p (s + 1) - p s = -α * t (s + 1) * u (s + 1)) :
    ∑ s ∈ Finset.range (N + 1), t s * p s ^ 2
      = p N * u (N + 1) + α * ∑ s ∈ Finset.range (N + 1), t s * u s ^ 2 := by
  induction N with
  | zero =>
    simp
    have h := hstep 0
    have : u 1 = u 0 + t 0 * p 0 := by linarith
    rw [this, hflux0]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ (fun s => t s * p s ^ 2) (n + 1), ih,
      Finset.sum_range_succ (fun s => t s * u s ^ 2) (n + 1)]
    have h1 := hstep (n + 1)
    have h2 := hflux n
    have hu : u (n + 1 + 1) = u (n + 1) + t (n + 1) * p (n + 1) := by linarith
    have hp : p n = p (n + 1) + α * t (n + 1) * u (n + 1) := by linarith
    rw [hu, hp]; ring

end TstarCore

#print axioms TstarCore.drift
#print axioms TstarCore.sbp
