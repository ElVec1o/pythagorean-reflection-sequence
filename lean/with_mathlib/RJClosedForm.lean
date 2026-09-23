import Mathlib

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
