/-
KplusForward.lean
=================
`lem:Kplus` (ii) and (iii) of `merged_novel_paper.tex`, the algebra on the continuants `D_k`.

For orthoscheme legs `a_1,...,a_n > 0` put `r_k = (a_k/a_{k+1})^2` and define `c(a)` by the
paper's forward formula.  Then `c_i(a)^2 = x_i` with
  `x_1 = 1/(1+r_1)`, `x_i = r_{i-1}/((1+r_{i-1})(1+r_i))` (2 <= i <= n-1), `x_n = r_{n-1}/(1+r_{n-1})`.
We prove, for the continuant `D` of `c(a)`:
  * `D_{k+1} = rho_k D_k` with `rho_k = r_k/(1+r_k)`   (the inverse-map formula (iii)),
  * `D_k > 0` for `1 <= k <= n` and `D_{n+1} = 0`      (the D-form of `c(a) ∈ K^+`, part (i)).
No sorry.
-/
import KplusPath

namespace KplusForward

open KplusPath

/-- `rho_k = r_k / (1 + r_k)`. -/
noncomputable def rho (r : ℕ → ℝ) (k : ℕ) : ℝ := r k / (1 + r k)

/-- The paper's `x_i` in terms of `r`. -/
noncomputable def X (n : ℕ) (r : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 1 then 1 / (1 + r 1)
  else if i = n then r (n - 1) / (1 + r (n - 1))
  else r (i - 1) / ((1 + r (i - 1)) * (1 + r i))

section
variable (n : ℕ) (r c : ℕ → ℝ) (hr : ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < r k)
  (hc : ∀ i, 1 ≤ i → i ≤ n → c i ^ 2 = X n r i)

include hr hc in
/-- Inverse-map formula: `D_{k+1} = rho_k D_k` for `1 <= k <= n-1`. -/
theorem D_ratio (hn : 2 ≤ n) : ∀ k, 1 ≤ k → k + 1 ≤ n → D c (k + 1) = rho r k * D c k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro h2
    have hr1 := hr 1 le_rfl h2
    have e : D c 2 = D c 1 - c 1 ^ 2 * D c 0 := rfl
    rw [e, hc 1 le_rfl (by omega)]
    simp only [X, if_true, D, rho]
    field_simp
    ring
  | succ k hk ih =>
    intro hk2
    have ih' := ih (by omega)
    have hrk := hr k hk (by omega)
    have hrk1 := hr (k + 1) (by omega) hk2
    have e : D c (k + 2) = D c (k + 1) - c (k + 1) ^ 2 * D c k := rfl
    have hX : c (k + 1) ^ 2 = r k / ((1 + r k) * (1 + r (k + 1))) := by
      rw [hc (k + 1) (by omega) (by omega)]
      have h1 : k + 1 ≠ 1 := by omega
      have h2 : k + 1 ≠ n := by omega
      simp only [X, if_neg h1, if_neg h2]
      simp
    rw [e, hX, ih']
    simp only [rho]
    have h1 : (1 + r k) ≠ 0 := by positivity
    have h2 : (1 + r (k + 1)) ≠ 0 := by positivity
    field_simp
    ring

include hr hc in
/-- `D_k > 0` for `1 <= k <= n`. -/
theorem D_pos (hn : 2 ≤ n) : ∀ k, 1 ≤ k → k ≤ n → 0 < D c k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; simp [D]
  | succ k hk ih =>
    intro hk2
    rw [D_ratio n r c hr hc hn k hk hk2]
    exact mul_pos (div_pos (hr k hk hk2) (by have := hr k hk hk2; positivity)) (ih (by omega))

include hr hc in
/-- `D_{n+1} = 0`. -/
theorem D_last (hn : 2 ≤ n) : D c (n + 1) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e : D c (m + 2 + 1) = D c (m + 2) - c (m + 2) ^ 2 * D c (m + 1) := rfl
  have hX : c (m + 2) ^ 2 = rho r (m + 1) := by
    rw [hc (m + 2) (by omega) le_rfl]
    have h1 : m + 2 ≠ 1 := by omega
    simp only [X, if_neg h1, if_true, rho]
    simp
  have hR := D_ratio (m + 2) r c hr hc hn (m + 1) (by omega) (by omega)
  rw [e, hX, hR]
  ring

end

/-! ### The forward formula `c(a)` -/

/-- The paper's forward formula `c_i(a)`. -/
noncomputable def cOf (n : ℕ) (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 1 then a 2 / Real.sqrt (a 1 ^ 2 + a 2 ^ 2)
  else if i = n then a (n - 1) / Real.sqrt (a (n - 1) ^ 2 + a n ^ 2)
  else a (i - 1) * a (i + 1) /
    Real.sqrt ((a (i - 1) ^ 2 + a i ^ 2) * (a i ^ 2 + a (i + 1) ^ 2))

/-- `r_k = (a_k/a_{k+1})^2`. -/
noncomputable def rOf (a : ℕ → ℝ) (k : ℕ) : ℝ := (a k / a (k + 1)) ^ 2

theorem cOf_sq (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) :
    ∀ i, 1 ≤ i → i ≤ n → cOf n a i ^ 2 = X n (rOf a) i := by
  intro i hi1 hin
  unfold cOf X rOf
  by_cases h1 : i = 1
  · subst h1
    simp only [if_true]
    have a1 := ha 1 le_rfl (by omega)
    have a2 := ha 2 (by omega) hn
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  · by_cases hn' : i = n
    · subst hn'
      simp only [if_neg h1, if_true]
      have a1 := ha (i - 1) (by omega) (by omega)
      have a2 := ha i hi1 le_rfl
      rw [div_pow, Real.sq_sqrt (by positivity)]
      have : (i - 1 + 1) = i := by omega
      rw [this]
      field_simp
      ring
    · simp only [if_neg h1, if_neg hn']
      have a1 := ha (i - 1) (by omega) (by omega)
      have a2 := ha i hi1 hin
      have a3 := ha (i + 1) (by omega) (by omega)
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have e : (i - 1 + 1) = i := by omega
      rw [e]
      field_simp
      ring

theorem rOf_pos (n : ℕ) (a : ℕ → ℝ) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) :
    ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < rOf a k := by
  intro k hk hk2
  have := ha k hk (by omega)
  have := ha (k + 1) (by omega) hk2
  unfold rOf
  positivity

/-- **`lem:Kplus` (ii)+(iii), algebra.**  For legs `a_1..a_n > 0` (`n >= 2`) the continuant `D`
of `c(a)` satisfies `D_{k+1} = rho_k D_k` (inverse formula, `rho_k = r_k/(1+r_k)`),
`D_k > 0` for `1 <= k <= n`, and `D_{n+1} = 0`. -/
theorem forward_formula (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) :
    (∀ k, 1 ≤ k → k + 1 ≤ n → D (cOf n a) (k + 1) = rho (rOf a) k * D (cOf n a) k) ∧
    (∀ k, 1 ≤ k → k ≤ n → 0 < D (cOf n a) k) ∧ D (cOf n a) (n + 1) = 0 :=
  ⟨D_ratio n (rOf a) (cOf n a) (rOf_pos n a ha) (cOf_sq n hn a ha) hn,
   D_pos n (rOf a) (cOf n a) (rOf_pos n a ha) (cOf_sq n hn a ha) hn,
   D_last n (rOf a) (cOf n a) (rOf_pos n a ha) (cOf_sq n hn a ha) hn⟩

end KplusForward

#print axioms KplusForward.forward_formula
