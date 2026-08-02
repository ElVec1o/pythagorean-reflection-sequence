/-
  SDAssembly.lean
  ===============
  The assembly of paper 2, Lemma `lem:infpoles` -- infinitude and accumulation of the
  travel poles -- machine-checked from its analytic input.

  `lem:infpoles` is the last link of BOTH transcendence theorems: `thm:V` and `thm:U` each
  need infinitely many travel poles.  The proof runs:

      1 - Sigma_1(tau) = cos w - T_2(w),      w = sqrt(2/tau)      [radius transport, exact]
      at the extreme phases w = m pi:  = (-1)^m - T_2(m pi)
      |T_2(m pi)| < 1                                              [from lem:cos]
      ==> the sign at w = m pi is exactly (-1)^m
      ==> consecutive extreme phases bracket a sign change
      ==> IVT puts a zero of 1 - Sigma_1 in every window
      ==> infinitely many travel poles, accumulating where tau -> 0.

  WHAT THIS FILE DOES.  It formalises that chain with the analytic input as an explicit
  hypothesis (`hT : forall m >= m0, |T m| < 1`, which is what `lem:cos` supplies).  It does
  NOT formalise `lem:cos`, the steepest-descent estimate behind it, or the transport
  identity: those are hypotheses.  As in `UAssembly`, the content is that the steps compose,
  and the hypothesis list is the audit.

  The one quantitative input is isolated in `sign_at_extreme_phase`: the *only* thing the
  infinitude argument needs is `|T_2(m pi)| < 1`, far weaker than a uniform `O(sqrt tau)` bound.
  It is supplied by `lem:T2abs`.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SDAssembly

open Set

/-! ### 1. The sign at an extreme phase -/

/-- **The only quantitative input.**  At `w = m pi` the block equals `(-1)^m - T`; if the
    error satisfies `|T| < 1` then the value has the sign of `(-1)^m`, i.e.
    `(-1)^m * value > 0`.  Note how weak this is compared with `lem:cos`'s `O(sqrt tau)`. -/
theorem sign_at_extreme_phase (m : ℕ) (T : ℝ) (hT : |T| < 1) :
    0 < (-1 : ℝ) ^ m * ((-1 : ℝ) ^ m - T) := by
  have hsq2 : ((-1 : ℝ)) ^ (m * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
  have hexp : (-1 : ℝ) ^ m * ((-1 : ℝ) ^ m - T) = 1 - (-1 : ℝ) ^ m * T := by
    ring_nf
    rw [hsq2]; ring
  have hle : (-1 : ℝ) ^ m * T ≤ |T| := by
    calc (-1 : ℝ) ^ m * T ≤ |(-1 : ℝ) ^ m * T| := le_abs_self _
      _ = |(-1 : ℝ) ^ m| * |T| := abs_mul _ _
      _ = |T| := by rw [abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [hexp]; linarith

/-- Consecutive extreme phases bracket a sign change. -/
theorem alternates (m : ℕ) (F T : ℕ → ℝ)
    (hF : ∀ k, F k = (-1 : ℝ) ^ k - T k) (hT : ∀ k, |T k| < 1) :
    F m * F (m + 1) < 0 := by
  have h1 : 0 < (-1 : ℝ) ^ m * F m := by rw [hF m]; exact sign_at_extreme_phase m (T m) (hT m)
  have h2 : 0 < (-1 : ℝ) ^ (m + 1) * F (m + 1) := by
    rw [hF (m + 1)]; exact sign_at_extreme_phase (m + 1) (T (m + 1)) (hT (m + 1))
  have hprod : ((-1 : ℝ) ^ m * F m) * ((-1 : ℝ) ^ (m + 1) * F (m + 1)) > 0 := mul_pos h1 h2
  have hsign : ((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ (m + 1)) = -1 := by
    rw [← pow_add, show m + (m + 1) = 2 * m + 1 by ring, pow_succ, pow_mul]
    norm_num
  have hre : ((-1 : ℝ) ^ m * F m) * ((-1 : ℝ) ^ (m + 1) * F (m + 1))
      = (((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ (m + 1))) * (F m * F (m + 1)) := by ring
  rw [hre, hsign] at hprod
  linarith

/-! ### 2. A zero in every window, by the intermediate value theorem -/

/-- If `g` is continuous and takes opposite signs at the endpoints of `[b, a]`, it vanishes
    somewhere strictly inside.  (The travel-pole equation is `g = 1 - Sigma_1`.) -/
theorem root_in_window {g : ℝ → ℝ} {b a : ℝ} (hba : b < a) (hg : ContinuousOn g (Icc b a))
    (hsign : g b * g a < 0) : ∃ x ∈ Ioo b a, g x = 0 := by
  rcases mul_neg_iff.mp hsign with ⟨hb, ha⟩ | ⟨hb, ha⟩
  · -- g b > 0, g a < 0
    have : (0 : ℝ) ∈ Ioo (g a) (g b) := ⟨ha, hb⟩
    obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo' hba.le hg this
    exact ⟨x, hx, hgx⟩
  · -- g b < 0, g a > 0
    have : (0 : ℝ) ∈ Ioo (g b) (g a) := ⟨hb, ha⟩
    obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo hba.le hg this
    exact ⟨x, hx, hgx⟩

/-! ### 3. Infinitely many zeros -/

/-- **The assembly.**  Given a strictly decreasing sequence of extreme-phase parameters
    `a : ℕ → ℝ` (for `lem:infpoles`, `a m = 2/(m pi)^2`), a continuous `g`, and a sign
    alternation at every `m ≥ m₀`, the zero set of `g` is infinite.

    The windows `Ioo (a (m+1)) (a m)` are pairwise disjoint because `a` is strictly
    antitone, so the chosen roots are pairwise distinct and `m ↦ root` is injective. -/
theorem infinitely_many_roots
    {g : ℝ → ℝ} {a : ℕ → ℝ} (m₀ : ℕ)
    (hanti : StrictAnti a)
    (hg : ∀ m, ContinuousOn g (Icc (a (m + 1)) (a m)))
    (halt : ∀ m, m₀ ≤ m → g (a (m + 1)) * g (a m) < 0) :
    {x : ℝ | g x = 0}.Infinite := by
  -- pick a root in each window beyond m₀
  have hroot : ∀ m, m₀ ≤ m → ∃ x ∈ Ioo (a (m + 1)) (a m), g x = 0 := by
    intro m hm
    exact root_in_window (hanti (Nat.lt_succ_self m)) (hg m) (halt m hm)
  choose! r hr hgr using hroot
  -- the chosen roots strictly decrease along the index: the windows are disjoint
  have hstrict : ∀ i j : ℕ, i < j → r (m₀ + j) < r (m₀ + i) := by
    intro i j hij
    have hi := hr (m₀ + i) (Nat.le_add_right _ _)
    have hj := hr (m₀ + j) (Nat.le_add_right _ _)
    have hle : a (m₀ + j) ≤ a (m₀ + i + 1) := hanti.antitone (by omega)
    have h1 : a (m₀ + i + 1) < r (m₀ + i) := hi.1
    have h2 : r (m₀ + j) < a (m₀ + j) := hj.2
    linarith
  apply Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => r (m₀ + m))
  · intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (ne_of_gt (hstrict i j h))
    · exact h
    · exact absurd hij.symm (ne_of_gt (hstrict j i h))
  · intro m
    exact hgr (m₀ + m) (Nat.le_add_right _ _)

/-! ### 4. What the chapter actually needs

    Reading the hypotheses above: the whole steepest-descent chapter enters the infinitude
    argument through exactly one inequality, `|T_2(m pi)| < 1`.  `lem:cos` proves the far
    stronger `|T_2| = O(sqrt tau)` uniformly in `w`; only the weak pointwise form at the
    extreme phases is consumed here. -/

/-- The weak form suffices: `O(sqrt tau)` decay at the extreme phases gives `|T| < 1`
    beyond some index, which is all `infinitely_many_roots` needs.  (Neither `0 ≤ C` nor
    `0 ≤ τ` is assumed: they are not needed, and the linter said so.) -/
theorem weak_input_suffices (T : ℕ → ℝ) (C : ℝ) (τ : ℕ → ℝ)
    (hbound : ∀ m, |T m| ≤ C * Real.sqrt (τ m))
    (m₀ : ℕ) (hsmall : ∀ m, m₀ ≤ m → C * Real.sqrt (τ m) < 1) :
    ∀ m, m₀ ≤ m → |T m| < 1 := fun m hm => lt_of_le_of_lt (hbound m) (hsmall m hm)

end SDAssembly
