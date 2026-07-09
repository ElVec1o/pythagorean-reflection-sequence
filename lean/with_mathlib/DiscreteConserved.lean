/-
  DiscreteConserved.lean
  ======================
  The two conserved quantities of the symmetric three-term recurrence
        w(n+1) = b n · w n − w(n-1)
  that underlie the denominator (block S_e) amplitude analysis of the U-gate
  (route_b, the pair-Casoratian `lem:pairC` and the discrete-energy envelope).

  Both are exact polynomial identities over any commutative ring, closed by `ring`
  after substituting the recurrence — no analysis, no `sorry`.
-/

import Mathlib.Tactic

namespace DiscreteConserved

variable {R : Type*} [CommRing R]

/-- **Casoratian conservation (`lem:pairC`).** For two solutions `z, z'` of
    `w(n+1) = b n · w n − w(n-1)`, the discrete Casoratian (Wronskian)
    `C_n = z n · z'(n-1) − z(n-1) · z' n` is constant: `C_{n+1} = C_n`.
    This is the exact pair-Casoratian that pins the amplitude *product* of the
    `ν = ±1/2` pair (leaving only the phase offset to the note's soft target). -/
theorem casoratian_const (z z' b : ℤ → R)
    (hz  : ∀ n, z  (n+1) = b n * z  n - z  (n-1))
    (hz' : ∀ n, z' (n+1) = b n * z' n - z' (n-1)) (n : ℤ) :
    z (n+1) * z' n - z n * z' (n+1) = z n * z' (n-1) - z (n-1) * z' n := by
  rw [hz n, hz' n]; ring

/-- **Discrete-energy drift.** For a solution `z` of `w(n+1) = b n · w n − w(n-1)`, the
    discrete energy `E_n = z(n+1)² + z n² − b n · z n · z(n+1)` drifts by exactly
    `E_n − E_{n-1} = z n · z(n-1) · (b(n-1) − b n)`. When `b` is constant this vanishes
    (energy conserved); its slow variation is the envelope drift of the block. -/
theorem energy_drift (z b : ℤ → R) (hz : ∀ n, z (n+1) = b n * z n - z (n-1)) (n : ℤ) :
    (z (n+1) ^ 2 + z n ^ 2 - b n * z n * z (n+1))
      - (z n ^ 2 + z (n-1) ^ 2 - b (n-1) * z (n-1) * z n)
      = z n * z (n-1) * (b (n-1) - b n) := by
  rw [hz n]; ring

/-- Corollary: with constant coefficient `b`, the energy is exactly conserved. -/
theorem energy_const (z : ℤ → R) (c : R) (hz : ∀ n, z (n+1) = c * z n - z (n-1)) (n : ℤ) :
    (z (n+1) ^ 2 + z n ^ 2 - c * z n * z (n+1))
      = (z n ^ 2 + z (n-1) ^ 2 - c * z (n-1) * z n) := by
  rw [hz n]; ring

end DiscreteConserved

#print axioms DiscreteConserved.casoratian_const
#print axioms DiscreteConserved.energy_drift
