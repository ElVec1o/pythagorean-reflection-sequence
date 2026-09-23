import Mathlib

namespace TstarAmplitude

/-- `c² = α q / 4` for `α = 2q(1-q)`, `c = q √((1-q)/2)`. -/
theorem c_sq (q : ℝ) (hq1 : q < 1) :
    (q * Real.sqrt ((1 - q) / 2)) ^ 2 = (2 * q * (1 - q)) * q / 4 := by
  rw [mul_pow, Real.sq_sqrt (by linarith)]; ring

theorem c_nonneg (q : ℝ) (hq : 0 < q) : 0 ≤ q * Real.sqrt ((1 - q) / 2) :=
  mul_nonneg hq.le (Real.sqrt_nonneg _)

/-- Reviewer C repair 1: `c ≤ √6/9 < 1` on `(1/2,1)` (we prove `c ≤ 3/10`, enough for `c < 1`). -/
theorem c_le (q : ℝ) (hq : 1/2 < q) (hq1 : q < 1) : q * Real.sqrt ((1 - q) / 2) ≤ 3/10 := by
  have h := c_sq q hq1
  have hc := c_nonneg q (by linarith)
  nlinarith [sq_nonneg (q - 2/3), sq_nonneg (q * Real.sqrt ((1 - q) / 2) - 3/10)]

/-- AM-GM amplitude step: `|u p| ≤ c (u² + p²/(α q))`. -/
theorem amgm (q u p : ℝ) (hq : 1/2 < q) (hq1 : q < 1) :
    |u * p| ≤ q * Real.sqrt ((1 - q) / 2) * (u ^ 2 + p ^ 2 / (2 * q * (1 - q) * q)) := by
  set c := q * Real.sqrt ((1 - q) / 2)
  have hc2 : c ^ 2 = (2 * q * (1 - q)) * q / 4 := c_sq q hq1
  have hc : 0 < c := by
    apply mul_pos (by linarith); apply Real.sqrt_pos.2; linarith
  have hk : 0 < 2 * q * (1 - q) * q := by
    have : 0 < 1 - q := by linarith
    positivity
  set k := 2 * q * (1 - q) * q
  have hck : k = 4 * c ^ 2 := by linarith
  rw [abs_le]
  have e : c * (u ^ 2 + p ^ 2 / k) = (c * u ^ 2 * k + c * p ^ 2) / k := by field_simp
  rw [e]
  constructor
  · have : (c * u ^ 2 * k + c * p ^ 2) / k + u * p
        = c * (2 * c * u + p) ^ 2 / k := by rw [hck]; field_simp; ring
    have : 0 ≤ c * (2 * c * u + p) ^ 2 / k := by positivity
    linarith
  · have : (c * u ^ 2 * k + c * p ^ 2) / k - u * p
        = c * (2 * c * u - p) ^ 2 / k := by rw [hck]; field_simp; ring
    have : 0 ≤ c * (2 * c * u - p) ^ 2 / k := by positivity
    linarith

/-- Two-sided bound `(1 - t c) F' ≤ G ≤ (1 + t c) F'` for `0 ≤ t ≤ 1`,
`F' = u² + p²/(αq)`, `G = F' + t u p`. -/
theorem G_bounds (q t u p : ℝ) (hq : 1/2 < q) (hq1 : q < 1) (ht : 0 ≤ t) :
    let c := q * Real.sqrt ((1 - q) / 2)
    let F' := u ^ 2 + p ^ 2 / (2 * q * (1 - q) * q)
    (1 - t * c) * F' ≤ F' + t * (u * p) ∧ F' + t * (u * p) ≤ (1 + t * c) * F' := by
  intro c F'
  have h := amgm q u p hq hq1
  have h' := abs_le.1 h
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h'.1 ht]
  · nlinarith [mul_le_mul_of_nonneg_left h'.2 ht]

/-- The leapfrog system with `t_s = q^s`, `α = 2q(1-q)`. -/
structure Leapfrog (q : ℝ) (u p : ℕ → ℝ) : Prop where
  hu : ∀ s, u (s + 1) = u s + q ^ s * p s
  hp : ∀ s, p (s + 1) = p s - 2 * q * (1 - q) * (q ^ s * q) * u (s + 1)

/-- The leapfrog invariant `G_s = u² + p²/(αq) + q^s u p`. -/
noncomputable def G (q : ℝ) (u p : ℕ → ℝ) (s : ℕ) : ℝ :=
  u s ^ 2 + p s ^ 2 / (2 * q * (1 - q) * q) + q ^ s * (u s * p s)

theorem drift {q : ℝ} {u p : ℕ → ℝ} (hq : 1/2 < q) (hq1 : q < 1) (L : Leapfrog q u p) (s : ℕ) :
    G q u p (s + 1) - G q u p s = -(1 - q) * q ^ s * u (s + 1) * p (s + 1) := by
  have hq0 : q ≠ 0 := by intro h; linarith
  have h1 : (1 - q) ≠ 0 := by intro h; linarith
  unfold G
  rw [L.hp s, L.hu s, pow_succ]
  field_simp
  ring

/-- Per-step ratio bound: `|G_s - G_{s+1}| ≤ d̄ q^s G_{s+1}`, `d̄ = (1-q)c/(1-c)`;
in particular `G_{s+1} > 0` whenever `(u,p)_{s+1} ≠ 0`, and `G ≥ 0` always. -/
theorem step {q : ℝ} {u p : ℕ → ℝ} (hq : 1/2 < q) (hq1 : q < 1) (L : Leapfrog q u p) (s : ℕ) :
    let c := q * Real.sqrt ((1 - q) / 2)
    |G q u p s - G q u p (s + 1)| ≤ (1 - q) * c / (1 - c) * q ^ s * G q u p (s + 1) := by
  intro c
  have hcle := c_le q hq hq1
  have hc0 := c_nonneg q (by linarith)
  have hd := drift hq hq1 L s
  have ha := abs_le.1 (amgm q (u (s + 1)) (p (s + 1)) hq hq1)
  set F := u (s + 1) ^ 2 + p (s + 1) ^ 2 / (2 * q * (1 - q) * q)
  have hts : 0 ≤ q ^ (s + 1) := pow_nonneg (by linarith) _
  have ht1 : q ^ (s + 1) ≤ 1 := pow_le_one₀ (by linarith) hq1.le
  have hs0 : 0 ≤ q ^ s := pow_nonneg (by linarith) _
  have hB := (G_bounds q (q ^ (s + 1)) (u (s + 1)) (p (s + 1)) hq hq1 hts).1
  have hGF : (1 - c) * F ≤ G q u p (s + 1) := by
    have : (1 - q ^ (s + 1) * c) * F ≥ (1 - c) * F := by
      have hF : 0 ≤ F := by
        have : 0 < 2 * q * (1 - q) * q := by
          have : 0 < 1 - q := by linarith
          have : 0 < q := by linarith
          positivity
        positivity
      nlinarith [mul_le_mul_of_nonneg_right ht1 hc0]
    unfold G; linarith
  have hc1 : 0 < 1 - c := by show 0 < 1 - q * Real.sqrt ((1 - q) / 2); linarith
  -- |G_s - G_{s+1}| = (1-q) q^s |u p| ≤ (1-q) q^s c F ≤ (1-q) q^s c G/(1-c)
  have hup : |u (s + 1) * p (s + 1)| ≤ c * F := amgm q _ _ hq hq1
  have e : G q u p s - G q u p (s + 1) = (1 - q) * q ^ s * (u (s + 1) * p (s + 1)) := by
    linarith
  rw [e, abs_mul, abs_of_nonneg (mul_nonneg (by linarith) hs0)]
  have hF' : c * F ≤ c * G q u p (s + 1) / (1 - c) := by
    rw [le_div_iff₀ hc1]; nlinarith [mul_le_mul_of_nonneg_left hGF hc0]
  calc (1 - q) * q ^ s * |u (s + 1) * p (s + 1)|
      ≤ (1 - q) * q ^ s * (c * G q u p (s + 1) / (1 - c)) :=
        mul_le_mul_of_nonneg_left (hup.trans hF') (mul_nonneg (by linarith) hs0)
    _ = (1 - q) * c / (1 - c) * q ^ s * G q u p (s + 1) := by ring

/-- Log-step bound from a two-sided ratio bound `|a - b| ≤ x b`, `0 ≤ x ≤ d < 1`, `a,b>0`. -/
theorem log_step (a b x d : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hxd : x ≤ d) (hd : d < 1)
    (h : |a - b| ≤ x * b) : |Real.log a - Real.log b| ≤ x / (1 - d) := by
  have h' := abs_le.1 h
  have hd1 : 0 < 1 - d := by linarith
  have hx1 : 0 < 1 - x := by linarith
  rw [abs_le]; constructor
  · -- log b - log a ≤ -log(1-x) ≤ x/(1-x) ≤ x/(1-d)
    have hab : (1 - x) * b ≤ a := by linarith
    have : Real.log b - Real.log a ≤ x / (1 - x) := by
      rw [← Real.log_div hb.ne' ha.ne']
      have hl := Real.log_le_sub_one_of_pos (div_pos hb ha)
      have : b / a ≤ 1 / (1 - x) := by
        rw [div_le_div_iff₀ ha hx1]; linarith
      have : b / a - 1 ≤ x / (1 - x) := by
        have : 1 / (1 - x) - 1 = x / (1 - x) := by field_simp; ring
        linarith
      linarith
    have : x / (1 - x) ≤ x / (1 - d) := div_le_div_of_nonneg_left hx hd1 (by linarith)
    linarith
  · have hl := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at hl
    have : a / b - 1 ≤ x := by rw [div_sub_one hb.ne', div_le_iff₀ hb]; linarith
    have : x ≤ x / (1 - d) := by
      rw [le_div_iff₀ hd1]; nlinarith
    linarith

/-- Telescoping: per-step log bounds sum over `[m, n)`. -/
theorem log_tele (L : ℕ → ℝ) (w : ℕ → ℝ) (h : ∀ s, |L s - L (s + 1)| ≤ w s) (m n : ℕ)
    (hmn : m ≤ n) : |L m - L n| ≤ ∑ s ∈ Finset.Ico m n, w s := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk]
    calc |L m - L (k + 1)| = |(L m - L k) + (L k - L (k + 1))| := by ring_nf
      _ ≤ |L m - L k| + |L k - L (k + 1)| := abs_add_le _ _
      _ ≤ _ := add_le_add ih (h k)

/-- Finite-horizon max G / min G bound: for all `m ≤ n`,
`|log G_m - log G_n| ≤ d̄ q^m / ((1 - d̄)(1 - q)) ≤ d̄/((1-d̄)(1-q)) = c/((1-c)(1-d̄))`,
assuming `G_s > 0` for all `s`. -/
theorem log_ratio {q : ℝ} {u p : ℕ → ℝ} (hq : 1/2 < q) (hq1 : q < 1) (Lf : Leapfrog q u p)
    (hpos : ∀ s, 0 < G q u p s) (m n : ℕ) (hmn : m ≤ n) :
    let c := q * Real.sqrt ((1 - q) / 2)
    let d := (1 - q) * c / (1 - c)
    |Real.log (G q u p m) - Real.log (G q u p n)| ≤ c / ((1 - c) * (1 - d)) := by
  intro c d
  have hcle := c_le q hq hq1
  have hc0 := c_nonneg q (by linarith)
  have hc1 : 0 < 1 - c := by show 0 < 1 - q * Real.sqrt ((1 - q) / 2); linarith
  have hd0 : 0 ≤ d := div_nonneg (mul_nonneg (by linarith) hc0) hc1.le
  have hd1 : d < 1 := by
    show (1 - q) * c / (1 - c) < 1
    rw [div_lt_one hc1]
    have : c ≤ 3/10 := hcle
    nlinarith
  have hstep : ∀ s, |Real.log (G q u p s) - Real.log (G q u p (s + 1))| ≤ d * q ^ s / (1 - d) := by
    intro s
    have hs0 : 0 ≤ q ^ s := pow_nonneg (by linarith) _
    have hs1 : q ^ s ≤ 1 := pow_le_one₀ (by linarith) hq1.le
    apply log_step _ _ (d * q ^ s) d (hpos s) (hpos (s + 1)) (mul_nonneg hd0 hs0)
      (by nlinarith) hd1
    have := step hq hq1 Lf s
    simpa [d, c, mul_assoc] using this
  have ht := log_tele (fun s => Real.log (G q u p s)) _ hstep m n hmn
  refine ht.trans ?_
  have hg : ∑ s ∈ Finset.Ico m n, q ^ s ≤ q ^ m / (1 - q) :=
    geom_sum_Ico_le_of_lt_one (by linarith) hq1
  have hqm : q ^ m / (1 - q) ≤ 1 / (1 - q) :=
    div_le_div_of_nonneg_right (pow_le_one₀ (by linarith) hq1.le) (by linarith)
  have hk : 0 ≤ d / (1 - d) := div_nonneg hd0 (by linarith)
  calc ∑ s ∈ Finset.Ico m n, d * q ^ s / (1 - d)
      = d / (1 - d) * ∑ s ∈ Finset.Ico m n, q ^ s := by
        rw [Finset.mul_sum]; congr 1; ext s; ring
    _ ≤ d / (1 - d) * (1 / (1 - q)) := mul_le_mul_of_nonneg_left (hg.trans hqm) hk
    _ = c / ((1 - c) * (1 - d)) := by
        have : (1 - q) ≠ 0 := by intro h; linarith
        have : (1 - d) ≠ 0 := by intro h; linarith
        simp only [d]; field_simp

end TstarAmplitude

#print axioms TstarAmplitude.c_le
#print axioms TstarAmplitude.amgm
#print axioms TstarAmplitude.G_bounds
#print axioms TstarAmplitude.drift
#print axioms TstarAmplitude.step
#print axioms TstarAmplitude.log_step
#print axioms TstarAmplitude.log_tele
#print axioms TstarAmplitude.log_ratio
