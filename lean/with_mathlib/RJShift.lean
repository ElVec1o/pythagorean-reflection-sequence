import Mathlib

/-!
# RJShift — the X and Y shift identities from the actual eigen-recursions (room 58)

Setting: `R, Ψ : ℕ → ℝ` (Ψ written `P`), `0 < q < 1`,
* `R s = 2 q^{s+1} Σ_t q^{max s t} R t`            (R is a pole eigenvector)
* `Ψ 0 = 1`, `Ψ b = 2 q^b Σ_a q^{max a b} Ψ a` for `b ≥ 1`
* `Σ_s q^s R s = 1`                               (pole normalisation)
* absolute summability of the kernel family `(b,t) ↦ Ψ b q^{max b t} R t` on `ℕ × ℕ`
  and of `a ↦ q^a Ψ a`.

Then `X := Σ_b Ψ b Σ_t q^{max b t} R t = q(1+2t₁)/(1-q)` and
`Y := Σ_b Ψ b Σ_s R s q^{max s (b-1)} = 1/(1-q)`, `t₁ = Σ_{b≥1} q^b Ψ b`.
(ℕ-subtraction: `b - 1 = 0` at `b = 0`, which is the intended `max(s,-1) = s`.)
No other hypotheses: the double-sum interchanges are proved from the ℕ×ℕ summability.
-/

namespace RJShift

/-- The kernel applied to R: `(KR)_b = Σ_t q^{max b t} R_t`. -/
noncomputable def KR (q : ℝ) (R : ℕ → ℝ) (b : ℕ) : ℝ := ∑' t, q ^ max b t * R t

/-- The kernel applied to Ψ: `F_t = Σ_b q^{max b t} Ψ_b`. -/
noncomputable def F (q : ℝ) (P : ℕ → ℝ) (t : ℕ) : ℝ := ∑' b, q ^ max b t * P b

theorem summable_swap {f : ℕ × ℕ → ℝ} (h : Summable f) :
    Summable (fun p : ℕ × ℕ => f p.swap) :=
  (Equiv.prodComm ℕ ℕ).summable_iff.mpr h

theorem KR_zero (q : ℝ) (R : ℕ → ℝ) : KR q R 0 = ∑' s, q ^ s * R s := by
  unfold KR; simp

/-- **The X shift identity, in raw form** (both evaluations of the double sum):
`X = 1 + S` and `X = 2q(1+t₁) + q S`, where `S = Σ_{b≥0} Ψ_{b+1}(KR)_{b+1}`. -/
theorem X_shift (q : ℝ) (hq0 : 0 < q) (R P : ℕ → ℝ)
    (hK : Summable (fun p : ℕ × ℕ => P p.1 * (q ^ max p.1 p.2 * R p.2)))
    (hPs : Summable (fun a => q ^ a * P a))
    (hR : ∀ s, R s = 2 * q ^ (s + 1) * KR q R s)
    (hP0 : P 0 = 1)
    (hP : ∀ b, 1 ≤ b → P b = 2 * q ^ b * F q P b)
    (hnorm : ∑' s, q ^ s * R s = 1) :
    (∑' b, P b * KR q R b = 1 + ∑' b, P (b + 1) * KR q R (b + 1)) ∧
    (∑' b, P b * KR q R b = 2 * q * (1 + ∑' b, q ^ (b + 1) * P (b + 1))
        + q * ∑' b, P (b + 1) * KR q R (b + 1)) := by
  have hrow : ∀ b, ∑' t, P b * (q ^ max b t * R t) = P b * KR q R b := fun b => by
    unfold KR; exact tsum_mul_left
  have hf : Summable (fun b => P b * KR q R b) := by
    have := hK.prod; simpa [hrow] using this
  have hcol : ∀ t, ∑' b, P b * (q ^ max b t * R t) = R t * F q P t := fun t => by
    unfold F
    rw [← tsum_mul_left]; congr 1; funext b; ring
  have hg : Summable (fun t => R t * F q P t) := by
    have := (summable_swap hK).prod; simpa [hcol] using this
  have hcomm : ∑' b, P b * KR q R b = ∑' t, R t * F q P t := by
    rw [← tsum_congr hrow, ← tsum_congr hcol]
    exact (Summable.tsum_comm (f := fun b t => P b * (q ^ max b t * R t)) hK).symm
  have hKR0 : KR q R 0 = 1 := by rw [KR_zero, hnorm]
  have hR0 : R 0 = 2 * q := by rw [hR 0, hKR0]; ring
  have hF0 : F q P 0 = 1 + ∑' b, q ^ (b + 1) * P (b + 1) := by
    have e : F q P 0 = ∑' b, q ^ b * P b := by unfold F; simp
    rw [e, hPs.tsum_eq_zero_add, hP0]; simp
  have hstep : ∀ t, R (t + 1) * F q P (t + 1) = q * (P (t + 1) * KR q R (t + 1)) := fun t => by
    rw [hR (t + 1), hP (t + 1) (by omega)]; ring
  refine ⟨?_, ?_⟩
  · rw [hf.tsum_eq_zero_add, hP0, hKR0]; ring
  · rw [hcomm, hg.tsum_eq_zero_add, hR0, hF0, tsum_congr hstep, tsum_mul_left]

/-- **X closed form**: `X = q(1+2t₁)/(1-q)`. -/
theorem X_closed (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (R P : ℕ → ℝ)
    (hK : Summable (fun p : ℕ × ℕ => P p.1 * (q ^ max p.1 p.2 * R p.2)))
    (hPs : Summable (fun a => q ^ a * P a))
    (hR : ∀ s, R s = 2 * q ^ (s + 1) * KR q R s)
    (hP0 : P 0 = 1)
    (hP : ∀ b, 1 ≤ b → P b = 2 * q ^ b * F q P b)
    (hnorm : ∑' s, q ^ s * R s = 1) :
    ∑' b, P b * KR q R b = q * (1 + 2 * ∑' b, q ^ (b + 1) * P (b + 1)) / (1 - q) := by
  obtain ⟨h1, h2⟩ := X_shift q hq0 R P hK hPs hR hP0 hP hnorm
  have hne : (1 - q) ≠ 0 := by linarith
  rw [eq_div_iff hne]
  linear_combination h2 - q * h1

/-- The Y inner sum `G_b = Σ_s R_s q^{max s (b-1)}`. -/
noncomputable def G (q : ℝ) (R : ℕ → ℝ) (b : ℕ) : ℝ := ∑' s, R s * q ^ max s (b - 1)

/-- The Y family is dominated by `q⁻¹ ×` the X family, hence summable. -/
theorem summable_Y (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (R P : ℕ → ℝ)
    (hK : Summable (fun p : ℕ × ℕ => P p.1 * (q ^ max p.1 p.2 * R p.2))) :
    Summable (fun p : ℕ × ℕ => P p.1 * (R p.2 * q ^ max p.2 (p.1 - 1))) := by
  refine Summable.of_norm_bounded (hK.norm.mul_left q⁻¹) (fun p => ?_)
  have hle : q ^ (max p.2 (p.1 - 1) + 1) ≤ q ^ max p.1 p.2 :=
    pow_le_pow_of_le_one hq0.le hq1.le (by omega)
  have hpos : 0 ≤ q ^ max p.2 (p.1 - 1) := by positivity
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hpos,
    abs_of_nonneg (pow_nonneg hq0.le _)]
  rw [pow_succ] at hle
  have hq' : q ^ max p.2 (p.1 - 1) ≤ q⁻¹ * q ^ max p.1 p.2 := by
    rw [le_inv_mul_iff₀ hq0]; linarith
  have := mul_le_mul_of_nonneg_left hq' (mul_nonneg (abs_nonneg (P p.1)) (abs_nonneg (R p.2)))
  nlinarith [abs_nonneg (P p.1), abs_nonneg (R p.2)]

/-- **The Y shift identity**: `Y = 1 + q Y`. -/
theorem Y_shift (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (R P : ℕ → ℝ)
    (hK : Summable (fun p : ℕ × ℕ => P p.1 * (q ^ max p.1 p.2 * R p.2)))
    (hR : ∀ s, R s = 2 * q ^ (s + 1) * KR q R s)
    (hP0 : P 0 = 1)
    (hP : ∀ b, 1 ≤ b → P b = 2 * q ^ b * F q P b)
    (hnorm : ∑' s, q ^ s * R s = 1) :
    ∑' b, P b * G q R b = 1 + q * ∑' b, P b * G q R b := by
  have hq : q ≠ 0 := hq0.ne'
  have hY := summable_Y q hq0 hq1 R P hK
  have hrow : ∀ b, ∑' s, P b * (R s * q ^ max s (b - 1)) = P b * G q R b := fun b => by
    unfold G; exact tsum_mul_left
  have hf : Summable (fun b => P b * G q R b) := by
    have := hY.prod; simpa [hrow] using this
  -- column sums: Σ_b Ψ_b q^{max s (b-1)} = F_{s+1}/q
  have hFs : ∀ s, F q P (s + 1) = q * ∑' b, P b * q ^ max s (b - 1) := fun s => by
    unfold F; rw [← tsum_mul_left]; congr 1; funext b
    have e : max b (s + 1) = max s (b - 1) + 1 := by omega
    rw [e, pow_succ]; ring
  have hcol : ∀ s, ∑' b, P b * (R s * q ^ max s (b - 1))
      = R s * P (s + 1) / (2 * q ^ (s + 2)) := fun s => by
    have e1 : ∑' b, P b * (R s * q ^ max s (b - 1)) = R s * ∑' b, P b * q ^ max s (b - 1) := by
      rw [← tsum_mul_left]; congr 1; funext b; ring
    have e2 := hP (s + 1) (by omega)
    rw [hFs s] at e2
    rw [e1, e2]
    field_simp
    ring
  have hg : Summable (fun s => R s * P (s + 1) / (2 * q ^ (s + 2))) := by
    have := (summable_swap hY).prod; simpa [hcol] using this
  have hcomm : ∑' b, P b * G q R b = ∑' s, R s * P (s + 1) / (2 * q ^ (s + 2)) := by
    rw [← tsum_congr hrow, ← tsum_congr hcol]
    exact (Summable.tsum_comm (f := fun b s => P b * (R s * q ^ max s (b - 1))) hY).symm
  have hG0 : G q R 0 = 1 := by
    unfold G; rw [← hnorm]; congr 1; funext s; simp [mul_comm]
  have hstep : ∀ b, P (b + 1) * G q R (b + 1)
      = q * (R b * P (b + 1) / (2 * q ^ (b + 2))) := fun b => by
    have e : G q R (b + 1) = KR q R b := by
      unfold G KR; congr 1; funext s; simp [max_comm, mul_comm]
    rw [e]
    have hRb := hR b
    have hKR : KR q R b = R b / (2 * q ^ (b + 1)) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [hKR]; field_simp; ring
  have h0 := hf.tsum_eq_zero_add
  rw [hP0, hG0, tsum_congr hstep, tsum_mul_left, ← hcomm] at h0
  linarith

/-- **Y closed form**: `Y = 1/(1-q)`. -/
theorem Y_closed (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (R P : ℕ → ℝ)
    (hK : Summable (fun p : ℕ × ℕ => P p.1 * (q ^ max p.1 p.2 * R p.2)))
    (hR : ∀ s, R s = 2 * q ^ (s + 1) * KR q R s)
    (hP0 : P 0 = 1)
    (hP : ∀ b, 1 ≤ b → P b = 2 * q ^ b * F q P b)
    (hnorm : ∑' s, q ^ s * R s = 1) :
    ∑' b, P b * G q R b = 1 / (1 - q) := by
  have h := Y_shift q hq0 hq1 R P hK hR hP0 hP hnorm
  have hne : (1 - q) ≠ 0 := by linarith
  rw [eq_div_iff hne]; linear_combination h

end RJShift

#print axioms RJShift.summable_swap
#print axioms RJShift.KR_zero
#print axioms RJShift.X_shift
#print axioms RJShift.X_closed
#print axioms RJShift.summable_Y
#print axioms RJShift.Y_shift
#print axioms RJShift.Y_closed
