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


/-!
# RJClosedForm — algebraic core of the (R-J) closed form (rooms 54b / 55, Reviewer K)
-/

namespace RJClosedForm

/-- Solving the X shift identity `X = 1 + (X - (1+t1) R0)/q`, `R0 = 2q`. -/
theorem X_solve (X t1 q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hX : X = 1 + (X - (1 + t1) * (2 * q)) / q) :
    X = q * (1 + 2 * t1) / (1 - q) := by
  have hq : q ≠ 0 := hq0.ne'
  have h1 : (1 - q) ≠ 0 := by linarith
  rw [eq_div_iff h1]
  field_simp at hX
  linarith

/-- Solving `Y = 1 + q Y`. -/
theorem Y_solve (Y q : ℝ) (hq1 : q < 1) (hY : Y = 1 + q * Y) : Y = 1 / (1 - q) := by
  have h1 : (1 - q) ≠ 0 := by linarith
  rw [eq_div_iff h1]; linarith

/-- Closed form (room 54b, y = 1): `(1+x)X + (q+x)Y = 2q(1+x)/(1-q) (t1 + (1+x)/(2x))`. -/
theorem closed_form (X Y t1 q x : ℝ) (hx : x ^ 2 = q) (hq0 : 0 < q) (hq1 : q < 1)
    (hX : X = 1 + (X - (1 + t1) * (2 * q)) / q) (hY : Y = 1 + q * Y) :
    (1 + x) * X + (q + x) * Y = 2 * q * (1 + x) / (1 - q) * (t1 + (1 + x) / (2 * x)) := by
  rw [X_solve X t1 q hq0 hq1 hX, Y_solve Y q hq1 hY]
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
  have h1 : (1 - q) ≠ 0 := by linarith
  subst hx
  field_simp
  ring

/-- Room 55 (y = q): only the s = 0 junction slot changes, `B0 → B0z = B0 (1 - t1 q/(1+q))`,
so `⟨λ,R⟩_new = ⟨λ,R⟩_old + (B0z - B0) R0` with `⟨λ,R⟩_old = B0((1+x)X + (q+x)Y)`.
Result: `⟨λ,R⟩_new = B0 R0 (1+x)/(1-x) [t1 (1-x+q)/(1+q) + 1/(2x)]`. -/
theorem closed_form_yq (X Y t1 q x B0 B0z : ℝ) (hx : x ^ 2 = q) (hxpos : 0 < x)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hX : X = 1 + (X - (1 + t1) * (2 * q)) / q) (hY : Y = 1 + q * Y)
    (hB : B0z = B0 * (1 - t1 * q / (1 + q))) :
    B0 * ((1 + x) * X + (q + x) * Y) + (B0z - B0) * (2 * q)
      = B0 * (2 * q) * (1 + x) / (1 - x) * (t1 * (1 - x + q) / (1 + q) + 1 / (2 * x)) := by
  rw [closed_form X Y t1 q x hx hq0 hq1 hX hY, hB]
  have hx1 : x < 1 := by nlinarith
  have h1 : (1 - x) ≠ 0 := by linarith
  have h2 : (1 - q) ≠ 0 := by linarith
  have h3 : (1 + q) ≠ 0 := by linarith
  subst hx
  field_simp
  ring

/-- Gate consequence: `|g t1| ≤ 0.983`, `g = q/(1-q)`, gives `q|t1| ≤ 0.983(1-q)`. -/
theorem gate_bound (t1 q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hg : |q / (1 - q) * t1| ≤ 0.983) : q * |t1| ≤ 0.983 * (1 - q) := by
  have h1 : 0 < 1 - q := by linarith
  rw [abs_mul, abs_of_pos (div_pos hq0 h1), div_mul_eq_mul_div, div_le_iff₀ h1] at hg
  linarith

/-- Nonvanishing of `1 - g t1` (only needs the gate). -/
theorem one_sub_gt_pos (t1 q : ℝ) (hg : |q / (1 - q) * t1| ≤ 0.983) :
    0 < 1 - q / (1 - q) * t1 := by
  have := (abs_le.mp hg).2; linarith

/-- Nonvanishing of the y = 1 bracket `t1 + (1+x)/(2x)` for `q ≥ 0.9`. -/
theorem bracket_pos (t1 q : ℝ) (hq0 : 0.9 ≤ q) (hq1 : q < 1)
    (hg : |q / (1 - q) * t1| ≤ 0.983) :
    0 < t1 + (1 + Real.sqrt q) / (2 * Real.sqrt q) := by
  have hqp : 0 < q := by linarith
  have hb := gate_bound t1 q hqp hq1 hg
  set x := Real.sqrt q with hxdef
  have hx2 : x ^ 2 = q := Real.sq_sqrt hqp.le
  have hxp : 0 < x := Real.sqrt_pos.mpr hqp
  have hx1 : x < 1 := by nlinarith
  have ht : -0.12 < t1 := by
    have := neg_abs_le t1; nlinarith [abs_nonneg t1]
  have : 1 ≤ (1 + x) / (2 * x) := by rw [le_div_iff₀ (by linarith)]; linarith
  linarith

/-- Nonvanishing of the y = q bracket `t1 (1-x+q)/(1+q) + 1/(2x)` for `q ≥ 0.9`. -/
theorem bracket_yq_pos (t1 q : ℝ) (hq0 : 0.9 ≤ q) (hq1 : q < 1)
    (hg : |q / (1 - q) * t1| ≤ 0.983) :
    0 < t1 * (1 - Real.sqrt q + q) / (1 + q) + 1 / (2 * Real.sqrt q) := by
  have hqp : 0 < q := by linarith
  have hb := gate_bound t1 q hqp hq1 hg
  set x := Real.sqrt q with hxdef
  have hx2 : x ^ 2 = q := Real.sq_sqrt hqp.le
  have hxp : 0 < x := Real.sqrt_pos.mpr hqp
  have hx1 : x < 1 := by nlinarith
  have ht : |t1| < 0.12 := by nlinarith [abs_nonneg t1]
  have hc0 : 0 < (1 - x + q) / (1 + q) := by apply div_pos <;> linarith
  have hc1 : (1 - x + q) / (1 + q) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hk : |t1 * (1 - x + q) / (1 + q)| ≤ |t1| := by
    rw [mul_div_assoc, abs_mul, abs_of_pos hc0]
    exact mul_le_of_le_one_right (abs_nonneg _) hc1
  have hh : 1 / 2 < 1 / (2 * x) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith
  have := neg_abs_le (t1 * (1 - x + q) / (1 + q))
  linarith

/-! ## Summation-level shift arguments (absolute summability as hypothesis) -/

/-- Generic shift: if `f` is summable and `f (n+1) = q f n + h n` with `h` summable,
then `S = f 0 + q S + Σ h`. -/
theorem tsum_shift (f h : ℕ → ℝ) (q : ℝ) (hf : Summable f) (hh : Summable h)
    (hrec : ∀ n, f (n + 1) = q * f n + h n) :
    ∑' n, f n = f 0 + q * ∑' n, f n + ∑' n, h n := by
  have e := hf.tsum_eq_zero_add
  have : (fun n => f (n + 1)) = fun n => q * f n + h n := funext hrec
  rw [this, (hf.mul_left q).tsum_add hh, tsum_mul_left] at e
  linarith

/-- Y as a sum: `Y = Σ_s q^s` satisfies `Y = 1 + qY`, hence `Y = 1/(1-q)`. -/
theorem Y_tsum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, q ^ n) = 1 + q * ∑' n : ℕ, q ^ n ∧ (∑' n : ℕ, q ^ n) = 1 / (1 - q) := by
  have hs : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have h := tsum_shift (fun n => q ^ n) (fun _ => 0) q hs summable_zero
    (fun n => by simp [pow_succ]; ring)
  simp at h
  exact ⟨h, Y_solve _ q hq1 h⟩

/-- Tail-shift version for `R_s q^{max(s, b-1)}`: for `s ≥ b-1` the weight is `q^s`, so the
tail `Σ_{s} R_{b-1+s} q^{b-1+s}` obeys the same shift whenever `R_{s+1} = R_s` on the tail. -/
theorem tail_shift (R : ℕ → ℝ) (q : ℝ) (b : ℕ)
    (hs : Summable (fun s => R (b - 1 + s) * q ^ max (b - 1 + s) (b - 1)))
    (hR : ∀ s, R (b - 1 + s + 1) = R (b - 1 + s)) :
    (∑' s, R (b - 1 + s) * q ^ max (b - 1 + s) (b - 1))
      = R (b - 1) * q ^ (b - 1) + q * ∑' s, R (b - 1 + s) * q ^ max (b - 1 + s) (b - 1) := by
  have h := tsum_shift (fun s => R (b - 1 + s) * q ^ max (b - 1 + s) (b - 1)) (fun _ => 0) q hs
    summable_zero (fun n => by
      have e1 : max (b - 1 + (n + 1)) (b - 1) = b - 1 + n + 1 := by omega
      have e2 : max (b - 1 + n) (b - 1) = b - 1 + n := by omega
      show R (b - 1 + (n + 1)) * q ^ max (b - 1 + (n + 1)) (b - 1)
        = q * (R (b - 1 + n) * q ^ max (b - 1 + n) (b - 1)) + 0
      rw [e1, e2, ← add_assoc, hR, pow_succ]; ring)
  simpa using h

end RJClosedForm


/-! # RJMain — wiring (room 59) -/

namespace RJMain
open RJShift

/-- The t₁ series `Σ_{b≥1} q^b Ψ_b`. -/
noncomputable def t1 (q : ℝ) (P : ℕ → ℝ) : ℝ := ∑' b, q ^ (b + 1) * P (b + 1)

/-- **Numerator closed form.** -/
theorem RJ_numerator_closed (q x : ℝ) (hx : x ^ 2 = q) (hq0 : 0 < q) (hq1 : q < 1)
    (R P : ℕ → ℝ)
    (hK : Summable (fun p : ℕ × ℕ => P p.1 * (q ^ max p.1 p.2 * R p.2)))
    (hPs : Summable (fun a => q ^ a * P a))
    (hR : ∀ s, R s = 2 * q ^ (s + 1) * KR q R s)
    (hP0 : P 0 = 1)
    (hP : ∀ b, 1 ≤ b → P b = 2 * q ^ b * F q P b)
    (hnorm : ∑' s, q ^ s * R s = 1) :
    (1 + x) * ∑' b, P b * KR q R b + (q + x) * ∑' b, P b * G q R b
      = 2 * q * (1 + x) / (1 - q) * (t1 q P + (1 + x) / (2 * x)) := by
  rw [X_closed q hq0 hq1 R P hK hPs hR hP0 hP hnorm, Y_closed q hq0 hq1 R P hK hR hP0 hP hnorm]
  unfold t1
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
  have h1 : (1 - q) ≠ 0 := by linarith
  subst hx
  field_simp
  ring

/-- **Nonvanishing corollary** under the gate `|g t₁| ≤ 0.983`, `q ≥ 0.9`. -/
theorem RJ_numerator_pos (q : ℝ) (hq9 : 0.9 ≤ q) (hq1 : q < 1)
    (R P : ℕ → ℝ)
    (hK : Summable (fun p : ℕ × ℕ => P p.1 * (q ^ max p.1 p.2 * R p.2)))
    (hPs : Summable (fun a => q ^ a * P a))
    (hR : ∀ s, R s = 2 * q ^ (s + 1) * KR q R s)
    (hP0 : P 0 = 1)
    (hP : ∀ b, 1 ≤ b → P b = 2 * q ^ b * F q P b)
    (hnorm : ∑' s, q ^ s * R s = 1)
    (hgate : |q / (1 - q) * t1 q P| ≤ 0.983) :
    0 < (1 + Real.sqrt q) * ∑' b, P b * KR q R b
        + (q + Real.sqrt q) * ∑' b, P b * G q R b := by
  have hq0 : 0 < q := by linarith
  rw [RJ_numerator_closed q (Real.sqrt q) (Real.sq_sqrt hq0.le) hq0 hq1 R P hK hPs hR hP0 hP hnorm]
  have hb := RJClosedForm.bracket_pos (t1 q P) q hq9 hq1 hgate
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hc : 0 < 2 * q * (1 + Real.sqrt q) / (1 - q) := by
    apply div_pos <;> nlinarith
  exact mul_pos hc hb

/-- `q^{max b t} ≤ (√q)^b (√q)^t`. -/
theorem pow_max_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b t : ℕ) :
    q ^ max b t ≤ Real.sqrt q ^ b * Real.sqrt q ^ t := by
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1
  rw [← pow_add]
  have e : q ^ max b t = Real.sqrt q ^ (2 * max b t) := by
    rw [pow_mul, Real.sq_sqrt hq0]
  rw [e]
  exact pow_le_pow_of_le_one hs0 hs1 (by omega)

/-- **Summability discharge from boundedness.** -/
theorem summable_of_bounded (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (R P : ℕ → ℝ)
    (C C' : ℝ) (hRb : ∀ t, |R t| ≤ C) (hPb : ∀ b, |P b| ≤ C') :
    Summable (fun p : ℕ × ℕ => P p.1 * (q ^ max p.1 p.2 * R p.2)) ∧
    Summable (fun a => q ^ a * P a) := by
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hq1
  have hg : Summable (fun n : ℕ => Real.sqrt q ^ n) := summable_geometric_of_lt_one hs0 hs1
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hRb 0)
  have hC' : 0 ≤ C' := le_trans (abs_nonneg _) (hPb 0)
  constructor
  · have hprod : Summable (fun p : ℕ × ℕ => Real.sqrt q ^ p.1 * Real.sqrt q ^ p.2) :=
      Summable.mul_of_nonneg hg hg (fun n => pow_nonneg hs0 n) (fun n => pow_nonneg hs0 n)
    refine Summable.of_norm_bounded (hprod.mul_left (C' * C)) (fun p => ?_)
    have hm := pow_max_le q hq0 hq1.le p.1 p.2
    have hqm : 0 ≤ q ^ max p.1 p.2 := pow_nonneg hq0 _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hqm]
    have h1 := hPb p.1
    have h2 := hRb p.2
    calc |P p.1| * (q ^ max p.1 p.2 * |R p.2|)
        ≤ C' * (q ^ max p.1 p.2 * C) := by gcongr
      _ = (C' * C) * q ^ max p.1 p.2 := by ring
      _ ≤ (C' * C) * (Real.sqrt q ^ p.1 * Real.sqrt q ^ p.2) := by gcongr
  · have hgq : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
    refine Summable.of_norm_bounded (hgq.mul_left C') (fun a => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq0 a)]
    have := hPb a
    calc q ^ a * |P a| ≤ q ^ a * C' := by gcongr
      _ = C' * q ^ a := by ring

/-- Geometric decay `|R t| ≤ C r^t`, `|P b| ≤ C' r'^b` (with `0 ≤ r, r' ≤ 1`) implies boundedness. -/
theorem summable_of_geometric (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (R P : ℕ → ℝ)
    (C C' r r' : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr0' : 0 ≤ r') (hr1' : r' ≤ 1)
    (hRb : ∀ t, |R t| ≤ C * r ^ t) (hPb : ∀ b, |P b| ≤ C' * r' ^ b) :
    Summable (fun p : ℕ × ℕ => P p.1 * (q ^ max p.1 p.2 * R p.2)) ∧
    Summable (fun a => q ^ a * P a) := by
  have hC : 0 ≤ C := by have := hRb 0; simp at this; linarith [abs_nonneg (R 0)]
  have hC' : 0 ≤ C' := by have := hPb 0; simp at this; linarith [abs_nonneg (P 0)]
  refine summable_of_bounded q hq0 hq1 R P C C' (fun t => ?_) (fun b => ?_)
  · calc |R t| ≤ C * r ^ t := hRb t
      _ ≤ C * 1 := by gcongr; exact pow_le_one₀ hr0 hr1
      _ = C := by ring
  · calc |P b| ≤ C' * r' ^ b := hPb b
      _ ≤ C' * 1 := by gcongr; exact pow_le_one₀ hr0' hr1'
      _ = C' := by ring

/-- **Fully discharged**: closed form + positivity with only boundedness in place of hK/hPs. -/
theorem RJ_numerator_pos_bounded (q : ℝ) (hq9 : 0.9 ≤ q) (hq1 : q < 1)
    (R P : ℕ → ℝ) (C C' : ℝ) (hRb : ∀ t, |R t| ≤ C) (hPb : ∀ b, |P b| ≤ C')
    (hR : ∀ s, R s = 2 * q ^ (s + 1) * KR q R s)
    (hP0 : P 0 = 1)
    (hP : ∀ b, 1 ≤ b → P b = 2 * q ^ b * F q P b)
    (hnorm : ∑' s, q ^ s * R s = 1)
    (hgate : |q / (1 - q) * t1 q P| ≤ 0.983) :
    (1 + Real.sqrt q) * ∑' b, P b * KR q R b + (q + Real.sqrt q) * ∑' b, P b * G q R b
        = 2 * q * (1 + Real.sqrt q) / (1 - q) * (t1 q P + (1 + Real.sqrt q) / (2 * Real.sqrt q))
    ∧ 0 < (1 + Real.sqrt q) * ∑' b, P b * KR q R b
        + (q + Real.sqrt q) * ∑' b, P b * G q R b := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hK, hPs⟩ := summable_of_bounded q hq0.le hq1 R P C C' hRb hPb
  exact ⟨RJ_numerator_closed q _ (Real.sq_sqrt hq0.le) hq0 hq1 R P hK hPs hR hP0 hP hnorm,
    RJ_numerator_pos q hq9 hq1 R P hK hPs hR hP0 hP hnorm hgate⟩

end RJMain
#print axioms RJShift.summable_swap
#print axioms RJShift.KR_zero
#print axioms RJShift.X_shift
#print axioms RJShift.X_closed
#print axioms RJShift.summable_Y
#print axioms RJShift.Y_shift
#print axioms RJShift.Y_closed
#print axioms RJClosedForm.X_solve
#print axioms RJClosedForm.Y_solve
#print axioms RJClosedForm.closed_form
#print axioms RJClosedForm.closed_form_yq
#print axioms RJClosedForm.gate_bound
#print axioms RJClosedForm.one_sub_gt_pos
#print axioms RJClosedForm.bracket_pos
#print axioms RJClosedForm.bracket_yq_pos
#print axioms RJClosedForm.tsum_shift
#print axioms RJClosedForm.Y_tsum
#print axioms RJClosedForm.tail_shift
#print axioms RJMain.RJ_numerator_closed
#print axioms RJMain.RJ_numerator_pos
#print axioms RJMain.pow_max_le
#print axioms RJMain.summable_of_bounded
#print axioms RJMain.summable_of_geometric
#print axioms RJMain.RJ_numerator_pos_bounded
