import Mathlib

namespace RoomB34

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


/-! ## (a) Tao's shift lemma, finite horizon -/

/-- `E_N(u) = Σ_{s<N} q^{-s} (u_{s+1}-u_s)^2`. -/
noncomputable def E (q : ℝ) (N : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ s ∈ Finset.range N, (q ^ s)⁻¹ * (u (s + 1) - u s) ^ 2

/-- `M_N(u) = Σ_{s<N} 2(1-q) q^{s+1} u_s^2`. -/
noncomputable def M (q : ℝ) (N : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ s ∈ Finset.range N, 2 * (1 - q) * q ^ (s + 1) * u s ^ 2

/-- Shift `(S* u)_s = u_{s+1}`. -/
def shift (u : ℕ → ℝ) : ℕ → ℝ := fun s => u (s + 1)

/-- Exact identity (no hypothesis on `u_0`): `E_N(S*u) = q (E_{N+1}(u) - (u_1-u_0)^2)`. -/
theorem E_shift_eq (q : ℝ) (hq : q ≠ 0) (N : ℕ) (u : ℕ → ℝ) :
    E q N (shift u) = q * (E q (N + 1) u - (u 1 - u 0) ^ 2) := by
  unfold E shift
  rw [Finset.sum_range_succ']
  simp only [pow_zero, inv_one, one_mul, add_sub_cancel_right, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [pow_succ]
  field_simp
  ring

/-- Shift inequality: `E_N(S*u) ≤ q E_{N+1}(u)` for `0 < q`. -/
theorem E_shift_le (q : ℝ) (hq : 0 < q) (N : ℕ) (u : ℕ → ℝ) :
    E q N (shift u) ≤ q * E q (N + 1) u := by
  rw [E_shift_eq q hq.ne' N u]
  have : 0 ≤ (u 1 - u 0) ^ 2 := sq_nonneg _
  nlinarith

/-- Exact identity: `M_N(S*u) = (M_{N+1}(u) - 2(1-q) q u_0^2) / q`. -/
theorem M_shift_eq_general (q : ℝ) (hq : q ≠ 0) (N : ℕ) (u : ℕ → ℝ) :
    M q N (shift u) = (M q (N + 1) u - 2 * (1 - q) * q * u 0 ^ 2) / q := by
  unfold M shift
  rw [Finset.sum_range_succ']
  simp only [zero_add, pow_one, add_sub_cancel_right, Finset.sum_div]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [pow_succ, pow_succ]
  field_simp
  ring

/-- With `u_0 = 0`: `M_N(S*u) = M_{N+1}(u) / q`. -/
theorem M_shift_eq (q : ℝ) (hq : q ≠ 0) (N : ℕ) (u : ℕ → ℝ) (h0 : u 0 = 0) :
    M q N (shift u) = M q (N + 1) u / q := by
  rw [M_shift_eq_general q hq N u, h0]; ring

/-- With `u_0 = 0`: `E_N(S*u) = q (E_{N+1}(u) - u_1^2)`. -/
theorem E_shift_eq0 (q : ℝ) (hq : q ≠ 0) (N : ℕ) (u : ℕ → ℝ) (h0 : u 0 = 0) :
    E q N (shift u) = q * (E q (N + 1) u - u 1 ^ 2) := by
  rw [E_shift_eq q hq N u, h0, sub_zero]

/-- Rayleigh-quotient drop: `u_0 = 0`, `0<q`, `M_{N+1}(u) > 0` ⇒
`E_N(S*u)/M_N(S*u) ≤ q^2 · E_{N+1}(u)/M_{N+1}(u)`. -/
theorem rayleigh_shift (q : ℝ) (hq : 0 < q) (N : ℕ) (u : ℕ → ℝ) (h0 : u 0 = 0)
    (hM : 0 < M q (N + 1) u) :
    E q N (shift u) / M q N (shift u) ≤ q ^ 2 * (E q (N + 1) u / M q (N + 1) u) := by
  rw [M_shift_eq q hq.ne' N u h0, div_div_eq_mul_div]
  have hE := E_shift_le q hq N u
  rw [div_le_iff₀ hM]
  have : q ^ 2 * (E q (N + 1) u / M q (N + 1) u) * M q (N + 1) u = q ^ 2 * E q (N + 1) u := by
    field_simp
  rw [this]
  nlinarith

/-! ## (b) Positivity of the leapfrog quantity `G` and comparison with `F'` -/

/-- `F'_s = u_s^2 + p_s^2/(αq)`. -/
noncomputable def F' (q : ℝ) (u p : ℕ → ℝ) (s : ℕ) : ℝ :=
  u s ^ 2 + p s ^ 2 / (2 * q * (1 - q) * q)

theorem F'_pos (q : ℝ) (hq : 1/2 < q) (hq1 : q < 1) (u p : ℕ → ℝ) (s : ℕ)
    (h : u s ≠ 0 ∨ p s ≠ 0) : 0 < F' q u p s := by
  have hk : 0 < 2 * q * (1 - q) * q := by
    have : 0 < 1 - q := by linarith
    have : 0 < q := by linarith
    positivity
  unfold F'
  rcases h with h | h
  · have := pow_pos (abs_pos.2 h) 2
    rw [sq_abs] at this
    have : 0 ≤ p s ^ 2 / (2 * q * (1 - q) * q) := by positivity
    linarith
  · have := pow_pos (abs_pos.2 h) 2
    rw [sq_abs] at this
    have : 0 < p s ^ 2 / (2 * q * (1 - q) * q) := div_pos this hk
    nlinarith [sq_nonneg (u s)]

/-- Two-sided comparison `(1 - q^s c) F'_s ≤ G_s ≤ (1 + q^s c) F'_s`, hence
`(1-c) F' ≤ G ≤ (1+c) F'`. -/
theorem G_F'_compare (q : ℝ) (hq : 1/2 < q) (hq1 : q < 1) (u p : ℕ → ℝ) (s : ℕ) :
    let c := q * Real.sqrt ((1 - q) / 2)
    (1 - c) * F' q u p s ≤ G q u p s ∧ G q u p s ≤ (1 + c) * F' q u p s := by
  intro c
  have hts : 0 ≤ q ^ s := pow_nonneg (by linarith) _
  have ht1 : q ^ s ≤ 1 := pow_le_one₀ (by linarith) hq1.le
  have hB := G_bounds q (q ^ s) (u s) (p s) hq hq1 hts
  have hc0 : 0 ≤ c := c_nonneg q (by linarith)
  have hk : 0 < 2 * q * (1 - q) * q := by
    have : 0 < 1 - q := by linarith
    have : 0 < q := by linarith
    positivity
  have hF : 0 ≤ F' q u p s := by unfold F'; positivity
  have e : G q u p s = F' q u p s + q ^ s * (u s * p s) := rfl
  simp only at hB
  rw [e]
  constructor
  · have : (1 - c) * F' q u p s ≤ (1 - q ^ s * c) * F' q u p s := by
      apply mul_le_mul_of_nonneg_right _ hF; nlinarith
    exact le_trans this hB.1
  · have : (1 + q ^ s * c) * F' q u p s ≤ (1 + c) * F' q u p s := by
      apply mul_le_mul_of_nonneg_right _ hF; nlinarith
    exact le_trans hB.2 this

/-- Pointwise positivity: `G_s > 0` whenever `(u_s,p_s) ≠ 0`. -/
theorem G_pos_of_ne (q : ℝ) (hq : 1/2 < q) (hq1 : q < 1) (u p : ℕ → ℝ) (s : ℕ)
    (h : u s ≠ 0 ∨ p s ≠ 0) : 0 < G q u p s := by
  have h1 := (G_F'_compare q hq hq1 u p s).1
  have hF := F'_pos q hq hq1 u p s h
  have hc : q * Real.sqrt ((1 - q) / 2) ≤ 3/10 := c_le q hq hq1
  have : 0 < (1 - q * Real.sqrt ((1 - q) / 2)) * F' q u p s := mul_pos (by linarith) hF
  linarith

/-- The leapfrog step is invertible: nonzero data stays nonzero. -/
theorem leapfrog_ne {q : ℝ} {u p : ℕ → ℝ} (L : Leapfrog q u p)
    (h0 : u 0 ≠ 0 ∨ p 0 ≠ 0) : ∀ s, u s ≠ 0 ∨ p s ≠ 0 := by
  intro s
  induction s with
  | zero => exact h0
  | succ n ih =>
    by_contra hc
    push Not at hc
    obtain ⟨hu, hp⟩ := hc
    have hps : p n = 0 := by have := L.hp n; rw [hu, hp] at this; linarith
    have hus : u n = 0 := by have := L.hu n; rw [hu, hps] at this; linarith
    rcases ih with h | h <;> contradiction

/-- Global positivity: along any leapfrog orbit with nonzero initial data, `G_s > 0` for all `s`.
This discharges the positivity hypothesis of `TstarAmplitude.log_ratio`. -/
theorem G_pos {q : ℝ} {u p : ℕ → ℝ} (hq : 1/2 < q) (hq1 : q < 1) (L : Leapfrog q u p)
    (h0 : u 0 ≠ 0 ∨ p 0 ≠ 0) : ∀ s, 0 < G q u p s :=
  fun s => G_pos_of_ne q hq hq1 u p s (leapfrog_ne L h0 s)

end RoomB34

#print axioms RoomB34.E_shift_eq
#print axioms RoomB34.E_shift_le
#print axioms RoomB34.E_shift_eq0
#print axioms RoomB34.M_shift_eq_general
#print axioms RoomB34.M_shift_eq
#print axioms RoomB34.rayleigh_shift
#print axioms RoomB34.F'_pos
#print axioms RoomB34.G_F'_compare
#print axioms RoomB34.G_pos_of_ne
#print axioms RoomB34.leapfrog_ne
#print axioms RoomB34.G_pos
