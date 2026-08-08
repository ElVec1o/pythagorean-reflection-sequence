/-
  EnvelopeDichotomy.lean
  ======================
  Machine-checked core of paper 3: the arithmetic of Theorem `thm:dichotomy` and the
  root identity of Theorem `thm:envelope`.

  WHY THESE TWO.  The audit of the previous version of paper 3 found that its errors were
  concentrated in exactly two places, both of them steps a reader skims:

    * the deviation half of the dichotomy was proved by "splitting a geodesic word ... gives
      two distinct elements of B_n(G) sharing a fiber".  That is only literally an argument
      when K(N) is even; when K(N) is odd the two halves have DIFFERENT lengths n and n-1, so
      they are not two points of the radius-n sphere and the sphere count has to drop for a
      different reason.  Both cases are discharged below, separately.

    * the growth rate was asserted to be "1 plus the spectral radius 2cos(2pi/(n+3)) of the
      path P_{n+1}".  The spectral radius of P_{n+1} is 2cos(pi/(n+2)); the claim is false.
      The correct route runs through the three-term recurrence, the identity
      cot A + cot B = 0 <-> sin (A+B) = 0, and the inversion t = 1/(1 + 2 cos 2theta).
      Those three steps are proved here.

  WHAT IS NOT HERE.  No word metric, no Coxeter group, no clique polynomial: the group theory
  around these steps is not formalised.  What is formalised is the arithmetic and the
  trigonometry, which is where the previous version went wrong.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace EnvelopeDichotomy

/-! ### 1. The horizon arithmetic

    `n = ceil (K/2)`, written in `Nat` as `(K+1)/2`. -/

/-- **Below the horizon the fibres are singletons.**  If `d < ceil (K/2)` then `2*d < K`,
    which is the inequality that forces `g * h⁻¹ = 1`.
    (`1 ≤ K` is not assumed: at `K = 0` the hypothesis `d < 0` is already impossible.) -/
theorem two_mul_lt_of_lt_horizon {K d : ℕ} (hd : d < (K + 1) / 2) :
    2 * d < K := by
  omega

/-- **The split of a shortest relator.**  With `n = ceil (K/2)`, the two halves have lengths
    `n` and `K - n = floor (K/2)`; they are equal exactly when `K` is even, and differ by one
    when `K` is odd.  This is the case distinction the previous proof omitted. -/
theorem split_lengths {K : ℕ} (hK : 1 ≤ K) :
    K - (K + 1) / 2 = K / 2 ∧
    (K % 2 = 0 → K - (K + 1) / 2 = (K + 1) / 2) ∧
    (K % 2 = 1 → K - (K + 1) / 2 + 1 = (K + 1) / 2) := by
  refine ⟨by omega, fun _ => by omega, fun _ => by omega⟩

/-! ### 2. The two ways a sphere count drops

    Both are stated for finsets and a map `f` playing the role of the quotient projection,
    with `Sq` the sphere in the quotient and `s` the sphere upstairs. -/

/-- **The even case.**  Two distinct points of the upstairs sphere share a fibre, so the image
    is strictly smaller. -/
theorem card_image_lt_of_collision {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hfab : f a = f b) :
    (s.image f).card < s.card := by
  have hsub : s.image f ⊆ (s.erase b).image f := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    by_cases hxb : x = b
    · subst hxb
      exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hab, ha⟩, hfab⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxb, hx⟩, rfl⟩
  calc (s.image f).card ≤ ((s.erase b).image f).card := Finset.card_le_card hsub
    _ ≤ (s.erase b).card := Finset.card_image_le
    _ = s.card - 1 := Finset.card_erase_of_mem hb
    _ < s.card := by
        have : 0 < s.card := Finset.card_pos.mpr ⟨b, hb⟩
        omega

/-- **The odd case.**  Here the two halves sit on spheres of different radii, so no two points
    of the upstairs sphere need collide.  What holds instead is that some point `w` of the
    upstairs sphere is sent strictly inside, i.e. off the downstairs sphere `Sq`; since `Sq`
    is covered by the image of the upstairs sphere, dropping `w` still covers it. -/
theorem card_lt_of_escapes {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (Sq : Finset β) (f : α → β) {w : α}
    (hw : w ∈ s) (hcover : Sq ⊆ s.image f) (hout : f w ∉ Sq) :
    Sq.card < s.card := by
  have hsub : Sq ⊆ (s.erase w).image f := by
    intro y hy
    rcases Finset.mem_image.mp (hcover hy) with ⟨x, hx, rfl⟩
    have hxw : x ≠ w := by
      intro h; subst h; exact hout hy
    exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxw, hx⟩, rfl⟩
  calc Sq.card ≤ ((s.erase w).image f).card := Finset.card_le_card hsub
    _ ≤ (s.erase w).card := Finset.card_image_le
    _ = s.card - 1 := Finset.card_erase_of_mem hw
    _ < s.card := by
        have : 0 < s.card := Finset.card_pos.mpr ⟨w, hw⟩
        omega

/-! ### 3. The three-term recurrence

    `cos` and `sin` at consecutive multiples of an angle obey the same Chebyshev recurrence,
    which is what makes the ansatz below solve `J_m = (1+t)(J_{m-1} - t J_{m-2})`. -/

theorem cos_three_term (x y : ℝ) :
    Real.cos (x + y) = 2 * Real.cos y * Real.cos x - Real.cos (x - y) := by
  rw [Real.cos_add, Real.cos_sub]; ring

theorem sin_three_term (x y : ℝ) :
    Real.sin (x + y) = 2 * Real.cos y * Real.sin x - Real.sin (x - y) := by
  rw [Real.sin_add, Real.sin_sub]; ring

/-- The solution ansatz `J_m = rho^m (cos m t - c sin m t)`. -/
noncomputable def J (rho c θ : ℝ) (m : ℕ) : ℝ :=
  rho ^ m * (Real.cos (m * θ) - c * Real.sin (m * θ))

/-- **The ansatz satisfies the envelope recurrence.**  With `rho^2 = t(1+t)` and
    `2 rho cos θ = 1+t`, the sequence `J` obeys `J_{m+2} = (1+t)(J_{m+1} - t J_m)`, which is
    the recurrence of Theorem `thm:envelope`.  No initial conditions are used, so this is the
    general solution in the oscillatory regime. -/
theorem J_recurrence (rho t c θ : ℝ)
    (hrho : rho ^ 2 = t * (1 + t)) (hcos : 2 * rho * Real.cos θ = 1 + t) (m : ℕ) :
    J rho c θ (m + 2) = (1 + t) * (J rho c θ (m + 1) - t * J rho c θ m) := by
  have hx : ((m : ℝ) + 2) * θ = (((m : ℝ) + 1) * θ) + θ := by ring
  have hy : (m : ℝ) * θ = (((m : ℝ) + 1) * θ) - θ := by ring
  have hc2 : Real.cos (((m : ℝ) + 2) * θ)
      = 2 * Real.cos θ * Real.cos (((m : ℝ) + 1) * θ) - Real.cos ((m : ℝ) * θ) := by
    rw [hx, cos_three_term, ← hy]
  have hs2 : Real.sin (((m : ℝ) + 2) * θ)
      = 2 * Real.cos θ * Real.sin (((m : ℝ) + 1) * θ) - Real.sin ((m : ℝ) * θ) := by
    rw [hx, sin_three_term, ← hy]
  simp only [J]
  push_cast
  rw [hc2, hs2]
  -- the identity is `rho^{m+1} (A - cA') * hcos  -  rho^m (B - cB') * hrho`, where the first
  -- bracket collects the terms carrying `cos/sin at (m+1)θ` and the second those at `mθ`.
  linear_combination
    (rho ^ (m + 1) *
        (Real.cos (((m : ℝ) + 1) * θ) - c * Real.sin (((m : ℝ) + 1) * θ))) * hcos
      - (rho ^ m * (Real.cos ((m : ℝ) * θ) - c * Real.sin ((m : ℝ) * θ))) * hrho

/-! ### 4. The root condition

    `cot A + cot B = 0` collapses to a single sine, which is what turns the transcendental
    equation `J_{n+1} = 0` into the arithmetic progression of angles `k pi / (n+3)`. -/

theorem cot_add_cot_eq_zero_iff {A B : ℝ} (hA : Real.sin A ≠ 0) (hB : Real.sin B ≠ 0) :
    Real.cos A / Real.sin A + Real.cos B / Real.sin B = 0 ↔ Real.sin (A + B) = 0 := by
  have key : Real.cos A / Real.sin A + Real.cos B / Real.sin B
      = Real.sin (A + B) / (Real.sin A * Real.sin B) := by
    rw [Real.sin_add]; field_simp; ring
  rw [key, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (mul_ne_zero hA hB)
  · intro h; exact Or.inl h

/-- **The vanishing of `J` is a sine condition.**  With the constant `c` pinned by the initial
    conditions to `-cot 2θ`, `J_m = 0` happens exactly at the angles with `sin((m+2)θ) = 0`,
    i.e.\ `θ ∈ (π/(m+2)) ℤ`.  For `m = n+1` this is `θ = kπ/(n+3)`. -/
theorem J_eq_zero_iff (rho c θ : ℝ) (m : ℕ)
    (hrho : rho ≠ 0)
    (hs2 : Real.sin (2 * θ) ≠ 0)
    (hsm : Real.sin ((m : ℝ) * θ) ≠ 0)
    (hc : c = -(Real.cos (2 * θ) / Real.sin (2 * θ))) :
    J rho c θ m = 0 ↔ Real.sin (((m : ℝ) + 2) * θ) = 0 := by
  have hpow : rho ^ m ≠ 0 := pow_ne_zero _ hrho
  have hsplit : J rho c θ m = 0 ↔ Real.cos ((m : ℝ) * θ) - c * Real.sin ((m : ℝ) * θ) = 0 := by
    simp only [J, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hpow
      · exact h
    · intro h; exact Or.inr h
  have hcot : Real.cos ((m : ℝ) * θ) - c * Real.sin ((m : ℝ) * θ) = 0 ↔
      Real.cos ((m : ℝ) * θ) / Real.sin ((m : ℝ) * θ)
        + Real.cos (2 * θ) / Real.sin (2 * θ) = 0 := by
    rw [hc]
    constructor
    · intro h
      field_simp at h ⊢
      linarith [h]
    · intro h
      field_simp at h ⊢
      linarith [h]
  have hsum : (m : ℝ) * θ + 2 * θ = ((m : ℝ) + 2) * θ := by ring
  rw [hsplit, hcot, cot_add_cot_eq_zero_iff hsm hs2, hsum]

/-! ### 5. Recovering `t` from the angle

    The last step of Theorem `thm:envelope`: inverting `cos^2 θ = (1+t)/(4t)`. -/

/-- **`t = 1/(1 + 2 cos 2θ)`.**  This is where the growth rate comes from, and it uses
    `cos 2θ`, not `cos θ`; reading `cos θ` here is what produced the false claim that the rate
    is one plus a path spectral radius. -/
theorem t_of_theta {t θ : ℝ} (ht : t ≠ 0)
    (hcos : Real.cos θ ^ 2 = (1 + t) / (4 * t)) :
    t * (1 + 2 * Real.cos (2 * θ)) = 1 := by
  have h2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have h4 : (4 : ℝ) * t ≠ 0 := by simpa using ht
  have hmul : 4 * t * Real.cos θ ^ 2 = 1 + t := by
    rw [hcos]; field_simp
  rw [h2]; linarith [hmul]

/-- The growth rate in the form used by the paper: `1/t = 1 + 2 cos 2θ`. -/
theorem rate_of_theta {t θ : ℝ} (ht : t ≠ 0)
    (hcos : Real.cos θ ^ 2 = (1 + t) / (4 * t)) :
    1 / t = 1 + 2 * Real.cos (2 * θ) := by
  have h := t_of_theta ht hcos
  field_simp
  linarith [h]

/-- **The false identification, refuted.**  At `n = 2` the claimed rate ingredient
    `2cos(2π/(n+3)) = 2cos(2π/5)` and the spectral radius of the path `P_{n+1} = P_3`,
    namely `2cos(π/(n+2)) = 2cos(π/4) = √2`, are different numbers. -/
theorem rate_ne_path_spectral_radius :
    2 * Real.cos (2 * Real.pi / 5) ≠ 2 * Real.cos (Real.pi / 4) := by
  have hpi := Real.pi_pos
  have hlt : Real.cos (2 * Real.pi / 5) < Real.cos (Real.pi / 4) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  intro h
  linarith [hlt, h]

end EnvelopeDichotomy
