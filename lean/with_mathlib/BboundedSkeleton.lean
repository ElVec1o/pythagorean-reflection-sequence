/-
  BboundedSkeleton.lean
  =====================
  The algebraic skeleton of paper 2, Lemma `lem:Bbounded` (amplitude regularity),
  as rewritten with the convergent closed form `eq:Bclosed`.

  The analytic inputs of that lemma -- the Weierstrass product for sinh, the digamma
  asymptotic with explicit remainder, and the convergence of the k-sum -- are NOT
  formalised here.  What is formalised is every step the proof performs *once those are
  granted*, i.e. exactly the bookkeeping in which such arguments fail in practice:

    * the per-factor rewriting `log (1 - q^i) = log (i tau) - i tau / 2 + phi (i tau)`
      and its summation, whose closed form needs the Gauss sum;
    * the collapse `log ((1-q) tau) = - tau/2 + 2 log tau + phi tau`;
    * the telescoping to `eq:Bsum`, `B_n = sum_{i<=2n} phi (i tau) - n phi tau`;
    * the *exact cancellation* `2 M log a + 2 M log R = 0` at `a R = 1`, which is what
      makes the Gamma-block sum of `eq:Bblocks` converge;
    * the scaling identities `tau w^2 = 2` and `(tau^2 w^3)^2 = 8 tau` (the latter true
      for the argument `w` and only up to `exp (-3 tau / 2)` for `W`), and the strip
      condition `|M| / R_1 < 1`;
    * the bounded-variation arithmetic that is the only consequence `lem:cos` consumes.

  Transcendental values enter only as named hypotheses, so no analysis is smuggled in.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace Bbounded

open Finset

/-! ### 1. The per-factor rewriting and its sum -/

/-- **One factor.**  With `L = log (1 - q^i)`, `Lt = log (i * tau)`, `P = phi (i * tau)`
    supplied as values, the paper's per-factor identity is the stated equation. -/
theorem factor_rewrite (tau i L Lt P : ℝ) (h : L = Lt - i * tau / 2 + P) :
    L - Lt - P = -(i * tau / 2) := by
  linarith

/-- **The Gauss sum**, which turns `sum_i (- i tau / 2)` into `- tau M (M+1) / 4`. -/
theorem gauss_sum (M : ℕ) :
    (∑ i ∈ range (M + 1), (i : ℝ)) = (M : ℝ) * (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- **The summed rewriting** (display `eq:qpochsum`, stripped of its transcendental
    interpretation): if every factor obeys `factor_rewrite`, the sum is `- tau M (M+1) / 4`. -/
theorem sum_rewrite (tau : ℝ) (M : ℕ) (L Lt P : ℕ → ℝ)
    (h : ∀ i, L i - Lt i - P i = -((i : ℝ) * tau / 2)) :
    (∑ i ∈ range (M + 1), (L i - Lt i - P i)) = -(tau * ((M : ℝ) * (M + 1))) / 4 := by
  have h1 : (∑ i ∈ range (M + 1), (L i - Lt i - P i))
      = ∑ i ∈ range (M + 1), (i : ℝ) * (-(tau / 2)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h i]; ring
  rw [h1, ← Finset.sum_mul, gauss_sum]
  ring

/-! ### 2. The collapse of the elementary terms -/

/-- **`log ((1-q) tau) = - tau/2 + 2 log tau + phi tau`.**  Granted
    `Lq = -(tau/2) + Lt + Pt` (i.e. `1 - q = tau * exp(-tau/2) * (sinh/(tau/2))`), the
    product rule gives the displayed collapse. -/
theorem collapse_log (tau Lq Lt Pt : ℝ) (h : Lq = -(tau / 2) + Lt + Pt) :
    Lq + Lt = -(tau / 2) + 2 * Lt + Pt := by
  linarith

/-- **The telescoping to `eq:Bsum`.**  Substituting `eq:qpochsum` and `collapse_log` into
    `-log eta_n = tau n^2 - n * log((1-q) tau) - log Gamma(2n+1) + log (q;q)_{2n}`,
    every elementary term cancels and exactly `S - n * Pt` survives, where
    `S = sum_{i <= 2n} phi (i tau)`, `Pt = phi tau`, `LG = log Gamma (2n+1)`. -/
theorem telescope (tau n LG S Lt Pt : ℝ) :
    tau * n ^ 2 - n * (-(tau / 2) + 2 * Lt + Pt) - LG
      + (LG + (2 * n) * Lt - tau * ((2 * n) * ((2 * n) + 1)) / 4 + S)
    = S - n * Pt := by
  ring

/-! ### 3. The exact cancellation behind the Gamma-block sum -/

/-- **`a R = 1` forces `2 M log a + 2 M log R = 0`.**  In the paper this is the statement
    that the `- 2 M log R` in `G(M;R)` is not a normalisation but the exact cancellation of
    the two leading Stirling terms -- which is what makes the `k`-sum converge.  Here
    `La = log a`, `LR = log R`, and `La + LR = 0` encodes `a R = 1`. -/
theorem block_cancellation {R : Type*} [CommRing R] (M La LR : R) (h : La + LR = 0) :
    2 * M * La + 2 * M * LR = 0 := by
  have hfac : 2 * M * La + 2 * M * LR = 2 * M * (La + LR) := by ring
  rw [hfac, h, mul_zero]

/-! ### 4. Scaling identities and the strip condition -/

/-- **`tau * w ^ 2 = 2`** is the defining relation of `w = sqrt (2 / tau)`; recorded so the
    downstream identities can be stated division-free. -/
theorem w_def_iff (tau w : ℝ) (hτ : tau ≠ 0) :
    tau * w ^ 2 = 2 ↔ w ^ 2 = 2 / tau := by
  constructor
  · intro h; field_simp; linarith [h]
  · intro h; field_simp at h; linarith [h]

/-- **`(tau^2 w^3)^2 = 8 tau`,** the division-free form of `tau^2 w^3 = 2 sqrt 2 sqrt tau`.
    This identity is exact for the argument `w`; for `W = w e^{-tau/2}` it holds only up to
    `e^{-3 tau / 2}`, exact for `w` only. -/
theorem tau_sq_w_cube_sq (tau w : ℝ) (h : tau * w ^ 2 = 2) :
    (tau ^ 2 * w ^ 3) ^ 2 = 8 * tau := by
  have hfac : (tau ^ 2 * w ^ 3) ^ 2 = tau * (tau * w ^ 2) ^ 3 := by ring
  rw [hfac, h]; ring

/-- **The strip condition `|M| / R_1 < 1`.**  With `r * pi = 4 * sq`, `sq = sqrt tau <= 1/2`
    and `pi > 3`, the ratio `r = (4/pi) sqrt tau` is `< 1`; this is what puts every `R_k`
    strictly beyond `|M|`, so that `R_k^2 - |M|^2 > 0` in the majorant. -/
theorem strip_ratio_lt_one (r sq pi_ : ℝ) (hpi : 3 < pi_) (_hsq0 : 0 ≤ sq)
    (hsq : sq ≤ 1 / 2) (hr : r * pi_ = 4 * sq) : r < 1 := by
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : pi_ ≤ r * pi_ := by nlinarith
  have h2 : r * pi_ ≤ 2 := by linarith
  linarith

/-! ### 5. The consequence actually consumed downstream -/

/-- **Bounded variation vanishes.**  Granted `sup |e^{-B}| <= E`, `|B'| <= D tau`, a contour
    of length `<= c w`, and `tau * w = rt2tau` (`= sqrt (2 tau)`), the bound
    `V <= E * D * c * sqrt (2 tau)` is pure arithmetic.  This is the *only* consequence of
    `lem:Bbounded` that Lemma `lem:cos` consumes, which is why enlarging the strip and
    weakening the constants costs nothing downstream. -/
theorem bv_bound (E D c tau w V rt2tau : ℝ)
    (hprod : tau * w = rt2tau)
    (hV : V ≤ E * (D * tau) * (c * w)) :
    V ≤ E * D * c * rt2tau := by
  have hre : E * (D * tau) * (c * w) = E * D * c * (tau * w) := by ring
  rw [hre, hprod] at hV
  exact hV

end Bbounded

-- Rule 5 axiom audit.
#print axioms Bbounded.factor_rewrite
#print axioms Bbounded.gauss_sum
#print axioms Bbounded.sum_rewrite
#print axioms Bbounded.collapse_log
#print axioms Bbounded.telescope
#print axioms Bbounded.block_cancellation
#print axioms Bbounded.w_def_iff
#print axioms Bbounded.tau_sq_w_cube_sq
#print axioms Bbounded.strip_ratio_lt_one
#print axioms Bbounded.bv_bound
