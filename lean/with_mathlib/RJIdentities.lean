import Mathlib

/-!
# RJIdentities — finite/algebraic identities from the (R-J) closure (room 51)

Travel recursion (room 34/38 scripts):
  u_{s+1} = (1 + q - 2 λ (1-q) q^{2s+1}) u_s - q u_{s-1}.
All statements are finite-horizon, exact, with explicit boundary terms.
-/

namespace RJIdentities

open Finset

/-! ## 1. Casoratian telescoping -/

/-- Coefficient of the travel recursion. -/
def coef (q lam : ℝ) (s : ℕ) : ℝ := 1 + q - 2 * lam * (1 - q) * q ^ (2 * s + 1)

/-- Unnormalised Casoratian `D_s = u_{s+1} v_s - u_s v_{s+1}`. -/
def cas (u v : ℕ → ℝ) (s : ℕ) : ℝ := u (s + 1) * v s - u s * v (s + 1)

/-- One step: `D_{s+1} = q D_s + (c_{s+1}-c'_{s+1}) u_{s+1} v_{s+1}` (any coefficients). -/
theorem cas_step (q : ℝ) (c c' u v : ℕ → ℝ)
    (hu : ∀ s, u (s + 2) = c (s + 1) * u (s + 1) - q * u s)
    (hv : ∀ s, v (s + 2) = c' (s + 1) * v (s + 1) - q * v s) (s : ℕ) :
    cas u v (s + 1) = q * cas u v s + (c (s + 1) - c' (s + 1)) * u (s + 1) * v (s + 1) := by
  unfold cas; rw [hu, hv]; ring

/-- Normalised Wronskian `W_s = D_s / q^s`. -/
noncomputable def wr (q : ℝ) (u v : ℕ → ℝ) (s : ℕ) : ℝ := cas u v s / q ^ s

/-- `W_{s+1} - W_s = -2 (λ-λ') (1-q) q^{s+2} u_{s+1} v_{s+1}` for the travel recursion. -/
theorem wr_step (q lam lam' : ℝ) (hq : q ≠ 0) (u v : ℕ → ℝ)
    (hu : ∀ s, u (s + 2) = coef q lam (s + 1) * u (s + 1) - q * u s)
    (hv : ∀ s, v (s + 2) = coef q lam' (s + 1) * v (s + 1) - q * v s) (s : ℕ) :
    wr q u v (s + 1) - wr q u v s
      = -2 * (lam - lam') * (1 - q) * q ^ (s + 2) * u (s + 1) * v (s + 1) := by
  unfold wr
  rw [cas_step q _ _ u v hu hv s]
  unfold coef
  have hs : q ^ s ≠ 0 := pow_ne_zero _ hq
  field_simp
  ring

/-- Finite-sum Casoratian telescoping. -/
theorem wr_telescope (q lam lam' : ℝ) (hq : q ≠ 0) (u v : ℕ → ℝ)
    (hu : ∀ s, u (s + 2) = coef q lam (s + 1) * u (s + 1) - q * u s)
    (hv : ∀ s, v (s + 2) = coef q lam' (s + 1) * v (s + 1) - q * v s) (N : ℕ) :
    wr q u v N - wr q u v 0
      = ∑ s ∈ range N, -2 * (lam - lam') * (1 - q) * q ^ (s + 2) * u (s + 1) * v (s + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← ih, ← wr_step q lam lam' hq u v hu hv n]; ring

/-! ## 2. Symplectic Euler: invariance and step-change drift -/

def Qh (mu h u p : ℝ) : ℝ := mu * u ^ 2 + p ^ 2 - mu * h * u * p

/-- `Q_h` is exactly invariant under `p' = p - μ h u`, `u' = u + h p'`. -/
theorem Qh_invariant (mu h u p : ℝ) :
    Qh mu h (u + h * (p - mu * h * u)) (p - mu * h * u) = Qh mu h u p := by
  unfold Qh; ring

/-- Exact drift when the step changes from `h` to `q h`. -/
theorem Qh_drift (mu h q u p : ℝ) :
    Qh mu (q * h) u p - Qh mu h u p = mu * h * (1 - q) * u * p := by
  unfold Qh; ring

/-- One full step with step-size change: `Q_{qh}(u',p') = Q_h(u,p) + μ h (1-q) u' p'`. -/
theorem Qh_step_drift (mu h q u p : ℝ) :
    Qh mu (q * h) (u + h * (p - mu * h * u)) (p - mu * h * u)
      = Qh mu h u p + mu * h * (1 - q) * (u + h * (p - mu * h * u)) * (p - mu * h * u) := by
  unfold Qh; ring

/-! ## 3. Virial identity, finite horizon
`P s` stands for `p_{s-1}` (so `P 0 = p_{-1}`); recurrence
`p_s = p_{s-1} - μ h_s u_s`, `u_{s+1} = u_s + h_s p_s`. -/

theorem virial (mu : ℝ) (h u P : ℕ → ℝ)
    (hp : ∀ s, P (s + 1) = P s - mu * h s * u s)
    (hu : ∀ s, u (s + 1) = u s + h s * P (s + 1)) (N : ℕ) :
    ∑ s ∈ range N, h s * P (s + 1) ^ 2
      = mu * ∑ s ∈ range N, h s * u s ^ 2 + (P N * u N - P 0 * u 0) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih, hu n]
    have := hp n
    linear_combination (-(u n)) * this

/-! ## 4. Partial fractions behind W_m (per term), a = 2m-1, b = 2n-1 -/

theorem pf_term (a b : ℝ) (hb : b ≠ 0) (hab : a ^ 2 - b ^ 2 ≠ 0) :
    a ^ 2 / (b ^ 2 * (a ^ 2 - b ^ 2)) = 1 / b ^ 2 + 1 / (a ^ 2 - b ^ 2) := by
  field_simp; ring

theorem pf_split (a b : ℝ) (ha : a ≠ 0) (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    1 / (a ^ 2 - b ^ 2) = (1 / (2 * a)) * (1 / (a - b) + 1 / (a + b)) := by
  have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [this]; field_simp; ring

/-- Combined: `a²/(b²(a²-b²)) = 1/b² + (1/(2a))(1/(a-b)+1/(a+b))`. -/
theorem pf_full (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    a ^ 2 / (b ^ 2 * (a ^ 2 - b ^ 2))
      = 1 / b ^ 2 + (1 / (2 * a)) * (1 / (a - b) + 1 / (a + b)) := by
  have hab : a ^ 2 - b ^ 2 ≠ 0 := by
    have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [this]; exact mul_ne_zero h1 h2
  rw [pf_term a b hb hab, pf_split a b ha h1 h2]

/-! ## 5. Sigma algebra (room 48): `M_{s+1} - M_s = -ε q^s S_s`, `V_s = q^s S_s` -/

theorem w2_pointwise (eps q : ℝ) (M S : ℕ → ℝ)
    (hM : ∀ s, M (s + 1) - M s = -eps * q ^ s * S s) (s : ℕ) :
    M s + M (s + 1) = 2 * M s - eps * (q ^ s * S s) := by
  have := hM s; linarith

theorem w2_sum (eps q : ℝ) (M S R : ℕ → ℝ)
    (hM : ∀ s, M (s + 1) - M s = -eps * q ^ s * S s) (N : ℕ) :
    ∑ s ∈ range N, R s * (M s + M (s + 1))
      = 2 * ∑ s ∈ range N, R s * M s - eps * ∑ s ∈ range N, R s * (q ^ s * S s) := by
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  rw [w2_pointwise eps q M S hM s]; ring

theorem M_telescope (eps q : ℝ) (M S : ℕ → ℝ)
    (hM : ∀ s, M (s + 1) - M s = -eps * q ^ s * S s) (N : ℕ) :
    M N - M 0 = -eps * ∑ s ∈ range N, q ^ s * S s := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; have := hM n; linarith

/-! ## 6. Room 38 F4 / Lemma 1.1: `λ l2 = (1+q) P - ε X + boundary`, finite horizon.
Indices in ℤ so that `U (-1)` is available. Here `e_s = 2 q x_s`, `x_{s+1} = q x_s`,
`C` = partial sums of `L`, `M_{s+1}-M_s = -ε x_s C_s`, and
`w_s ε x_s = M_s + M_{s+1}` (i.e. `w_s = (M_s+M_{s+1})/(ε x_s)`).
`εX = q Σ L_{s+1}(U_{s+1}-U_s)`. -/

theorem w_diff (q eps : ℝ) (x C M w : ℤ → ℝ)
    (hx : ∀ s, x (s + 1) = q * x s) (hx0 : ∀ s, x s ≠ 0) (heps : eps ≠ 0)
    (hM : ∀ s, M (s + 1) - M s = -eps * x s * C s)
    (hw : ∀ s, w s * (eps * x s) = M s + M (s + 1)) (s : ℤ) :
    w s - q * w (s + 1) = C s + q * C (s + 1) := by
  have h1 := hw s
  have h2 := hw (s + 1)
  have h3 := hM s
  have h4 := hM (s + 1)
  have h5 := hx s
  have hne : eps * x s ≠ 0 := mul_ne_zero heps (hx0 s)
  apply mul_right_cancel₀ hne
  rw [show s + 1 + 1 = s + 2 by ring] at h2 h4
  rw [h5] at h2 h4
  linear_combination h1 - h2 - h3 - h4

theorem F4_identity (q eps lam : ℝ) (x e C L M w U : ℤ → ℝ)
    (hx : ∀ s, x (s + 1) = q * x s) (hx0 : ∀ s, x s ≠ 0) (heps : eps ≠ 0)
    (he : ∀ s, e s = 2 * q * x s)
    (hC : ∀ s, C (s + 1) = C s + L (s + 1)) (hC0 : C 0 = L 0)
    (hM : ∀ s, M (s + 1) - M s = -eps * x s * C s)
    (hw : ∀ s, w s * (eps * x s) = M s + M (s + 1))
    (hU : ∀ s, U (s + 1) - (1 + q) * U s + q * U (s - 1) = -lam * eps * e s * x s * U s)
    (N : ℕ) :
    lam * ∑ s ∈ range N, e s * U s * (M s + M (s + 1))
      = (1 + q) * ∑ s ∈ range N, L s * U s
        - q * ∑ s ∈ range N, L (s + 1) * (U (s + 1) - U s)
        - (1 + q) * U N * (C N - L N)
        - q * (U N - U (N - 1)) * w N
        + q * (U 0 - U (-1)) * w 0 := by
  induction N with
  | zero => simp [hC0]
  | succ n ih =>
    simp only [sum_range_succ]
    push_cast
    have key : lam * (e n * U n * (M n + M (n + 1)))
        = -(U (n + 1) - (1 + q) * U n + q * U (n - 1)) * w n := by
      rw [hU n, ← hw n, he n]; ring
    have hd := w_diff q eps x C M w hx hx0 heps hM hw n
    have hc := hC n
    rw [show (n : ℤ) + 1 - 1 = n by ring]
    linear_combination ih + key + (-(U (n + 1) - U n)) * hd
      + ((1 + q) * U (n + 1) - q * (U (n + 1) - U n)) * hc

end RJIdentities

#print axioms RJIdentities.cas_step
#print axioms RJIdentities.wr_step
#print axioms RJIdentities.wr_telescope
#print axioms RJIdentities.Qh_invariant
#print axioms RJIdentities.Qh_drift
#print axioms RJIdentities.Qh_step_drift
#print axioms RJIdentities.virial
#print axioms RJIdentities.pf_term
#print axioms RJIdentities.pf_split
#print axioms RJIdentities.pf_full
#print axioms RJIdentities.w2_pointwise
#print axioms RJIdentities.w2_sum
#print axioms RJIdentities.M_telescope
#print axioms RJIdentities.w_diff
#print axioms RJIdentities.F4_identity
