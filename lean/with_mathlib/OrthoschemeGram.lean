import Mathlib

/-!
# OrthoschemeGram — the orthoscheme Gram continuant (Room D, Lemma A)

Legs `a_1, …, a_n > 0`, `b_k = a_k^2`, `n ≥ 2`.  The off-diagonal data of the orthoscheme
Gram matrix is

* `x_1 = b_2/(b_1+b_2)`,
* `x_k = b_{k-1} b_{k+1} / ((b_{k-1}+b_k)(b_k+b_{k+1}))`   (`2 ≤ k ≤ n-1`),
* `x_n = b_{n-1}/(b_{n-1}+b_n)`,

and the continuants are `D_0 = D_1 = 1`, `D_{k+1} = D_k - x_k D_{k-1}`.

Proved here (over `ℝ`, `n` an arbitrary natural number `≥ 2`, sequences indexed by `ℕ`,
only the entries `1..n` of `b` being constrained):

* `D_eq_prod`  : `D_{k+1} = ∏_{j=1}^{k} b_j/(b_j+b_{j+1})` for `k ≤ n-1`;
* `D_pos`      : these are `> 0`;
* `D_last`     : `D_{n+1} = 0`;
* the inverse map `bInv x k = (∏_{j=1}^{k-1} x_j)/(D_{k-1} D_k)`:
  - `bInv_spec`  : on every `x` with `x_j > 0` (`j ≤ n-1`), `D_k > 0` (`k ≤ n`), `D_{n+1} = 0`,
    `bInv x` is a positive leg-square vector whose forward image is `x` (surjectivity);
  - `b_eq_bInv`  : every positive `b` is `b_1 · bInv (X b)` (the forward map is injective up
    to the scale `b_1`);
  - `X_inj_scale`: `X b = X b'` implies `b' = c·b` on `1..n` for some `c > 0`.
-/

namespace OrthoschemeGram

open Finset

/-- `r_j = b_j/(b_j+b_{j+1})`. -/
noncomputable def r (b : ℕ → ℝ) (j : ℕ) : ℝ := b j / (b j + b (j + 1))

/-- The forward map: the Gram off-diagonal data `x_k` of the leg squares `b`. -/
noncomputable def X (n : ℕ) (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 1 then b 2 / (b 1 + b 2)
  else if k = n then b (n - 1) / (b (n - 1) + b n)
  else b (k - 1) * b (k + 1) / ((b (k - 1) + b k) * (b k + b (k + 1)))

/-- The continuant of an arbitrary sequence `x`: `D_0 = D_1 = 1`, `D_{k+2} = D_{k+1} - x_{k+1} D_k`. -/
noncomputable def D (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (k + 2) => D x (k + 1) - x (k + 1) * D x k

@[simp] lemma D_zero (x : ℕ → ℝ) : D x 0 = 1 := rfl
@[simp] lemma D_one (x : ℕ → ℝ) : D x 1 = 1 := rfl
lemma D_succ_succ (x : ℕ → ℝ) (k : ℕ) : D x (k + 2) = D x (k + 1) - x (k + 1) * D x k := rfl

/-- `P k = ∏_{j=1}^k r_j`. -/
noncomputable def P (b : ℕ → ℝ) (k : ℕ) : ℝ := ∏ j ∈ Icc 1 k, r b j

@[simp] lemma P_zero (b : ℕ → ℝ) : P b 0 = 1 := by simp [P]

lemma P_succ (b : ℕ → ℝ) (k : ℕ) : P b (k + 1) = P b k * r b (k + 1) := by
  unfold P; rw [prod_Icc_succ_top (by omega : 1 ≤ k + 1)]

lemma X_one {n : ℕ} (b : ℕ → ℝ) : X n b 1 = b 2 / (b 1 + b 2) := by simp [X]

lemma X_last {n : ℕ} (hn : 2 ≤ n) (b : ℕ → ℝ) :
    X n b n = b (n - 1) / (b (n - 1) + b n) := by
  unfold X; rw [if_neg (by omega), if_pos rfl]

lemma X_mid {n k : ℕ} (b : ℕ → ℝ) (h1 : k ≠ 1) (hn : k ≠ n) :
    X n b k = b (k - 1) * b (k + 1) / ((b (k - 1) + b k) * (b k + b (k + 1))) := by
  unfold X; rw [if_neg h1, if_neg hn]

section forward

variable {n : ℕ} {b : ℕ → ℝ}

/-- Two-step induction: `D_{k+1} = P_k` and `D_k = P_{k-1}` for `k+1 ≤ n`. -/
theorem D_eq_prod_aux (hn : 2 ≤ n) (hb : ∀ j, 1 ≤ j → j ≤ n → 0 < b j) :
    ∀ k, k + 1 ≤ n → D (X n b) (k + 1) = P b k ∧ D (X n b) k = P b (k - 1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨h1, h0⟩ := ih (by omega)
    refine ⟨?_, by simpa using h1⟩
    rw [D_succ_succ, h1, h0]
    rcases k with _ | m
    · -- k = 0 : D_2 = 1 - x_1 = r_1
      have b1 := hb 1 le_rfl (by omega)
      have b2 := hb 2 (by omega) (by omega)
      simp only [P_zero, zero_add, Nat.zero_sub, mul_one, P_succ, one_mul]
      rw [X_one]; unfold r
      field_simp; ring
    · -- k = m+1 : D_{m+3} = P_{m+1} - x_{m+2} P_m = P_{m+2}
      have b1 := hb (m + 1) (by omega) (by omega)
      have b2 := hb (m + 2) (by omega) (by omega)
      have b3 := hb (m + 3) (by omega) (by omega)
      rw [X_mid b (by omega) (by omega)]
      simp only [Nat.add_sub_cancel, show m + 1 + 1 = m + 2 from rfl, P_succ]
      unfold r
      simp only [show m + 2 - 1 = m + 1 by omega, show m + 1 + 1 = m + 2 from rfl,
        show m + 2 + 1 = m + 3 from rfl]
      field_simp; ring

/-- **Lemma A, product form.** `D_{k+1} = ∏_{j=1}^k b_j/(b_j+b_{j+1})` for `k ≤ n-1`. -/
theorem D_eq_prod (hn : 2 ≤ n) (hb : ∀ j, 1 ≤ j → j ≤ n → 0 < b j) (k : ℕ) (hk : k + 1 ≤ n) :
    D (X n b) (k + 1) = ∏ j ∈ Icc 1 k, b j / (b j + b (j + 1)) :=
  (D_eq_prod_aux hn hb k hk).1

/-- **Lemma A, positivity.** `D_{k+1} > 0` for `k ≤ n-1`. -/
theorem D_pos (hn : 2 ≤ n) (hb : ∀ j, 1 ≤ j → j ≤ n → 0 < b j) (k : ℕ) (hk : k + 1 ≤ n) :
    0 < D (X n b) (k + 1) := by
  rw [D_eq_prod hn hb k hk]
  refine prod_pos fun j hj => ?_
  rw [mem_Icc] at hj
  have := hb j hj.1 (by omega); have := hb (j + 1) (by omega) (by omega)
  positivity

/-- **Lemma A, degeneracy.** `D_{n+1} = 0`. -/
theorem D_last (hn : 2 ≤ n) (hb : ∀ j, 1 ≤ j → j ≤ n → 0 < b j) : D (X n b) (n + 1) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨h1, h0⟩ := D_eq_prod_aux hn hb (m + 1) le_rfl
  rw [show m + 2 + 1 = (m + 1) + 2 by omega, D_succ_succ, h1, h0,
    show m + 1 + 1 = m + 2 by omega, X_last hn, P_succ]
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega]
  unfold r; ring

/-- Statement in terms of the legs `a_k`, with `b_k = a_k^2`. -/
theorem lemmaA_legs {a : ℕ → ℝ} (hn : 2 ≤ n) (ha : ∀ j, 1 ≤ j → j ≤ n → 0 < a j) :
    (∀ k, k + 1 ≤ n →
      D (X n (fun j => a j ^ 2)) (k + 1) = ∏ j ∈ Icc 1 k, a j ^ 2 / (a j ^ 2 + a (j + 1) ^ 2) ∧
      0 < D (X n (fun j => a j ^ 2)) (k + 1)) ∧
    D (X n (fun j => a j ^ 2)) (n + 1) = 0 := by
  have hb : ∀ j, 1 ≤ j → j ≤ n → 0 < (fun j => a j ^ 2) j := fun j h1 h2 => by
    have := ha j h1 h2; positivity
  exact ⟨fun k hk => ⟨D_eq_prod hn hb k hk, D_pos hn hb k hk⟩, D_last hn hb⟩

end forward

/-! ## The inverse map -/

/-- The inverse map: `bInv x k = (∏_{j=1}^{k-1} x_j)/(D_{k-1} D_k)` (normalised `bInv x 1 = 1`). -/
noncomputable def bInv (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∏ j ∈ Ico 1 k, x j) / (D x (k - 1) * D x k)

lemma bInv_one (x : ℕ → ℝ) : bInv x 1 = 1 := by simp [bInv]

/-- The step relation `bInv_{k+1} = bInv_k · x_k D_{k-1}/D_{k+1}` (for `k ≥ 1`). -/
lemma bInv_succ (x : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) (hD0 : D x (k - 1) ≠ 0) (hD1 : D x k ≠ 0)
    (hD2 : D x (k + 1) ≠ 0) :
    bInv x (k + 1) = bInv x k * (x k * D x (k - 1) / D x (k + 1)) := by
  unfold bInv
  rw [prod_Ico_succ_top hk, Nat.add_sub_cancel]
  field_simp

section inverse

variable {n : ℕ} {x : ℕ → ℝ}

/-- Hypotheses describing the image of the forward map. -/
structure Admissible (n : ℕ) (x : ℕ → ℝ) : Prop where
  two_le : 2 ≤ n
  x_pos : ∀ j, 1 ≤ j → j + 1 ≤ n → 0 < x j
  D_pos : ∀ k, 1 ≤ k → k ≤ n → 0 < D x k
  D_last : D x (n + 1) = 0

lemma Admissible.D_pos' (h : Admissible n x) {k : ℕ} (hk : k ≤ n) : 0 < D x k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exact h.D_pos k hk0 hk

theorem bInv_pos (h : Admissible n x) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) : 0 < bInv x k := by
  unfold bInv
  have h0 := h.D_pos' (k := k - 1) (by omega)
  have h1 := h.D_pos' hk
  have : 0 < ∏ j ∈ Ico 1 k, x j := prod_pos fun j hj => by
    rw [mem_Ico] at hj; exact h.x_pos j hj.1 (by omega)
  positivity

/-- The ratio law `bInv_k/(bInv_k + bInv_{k+1}) = D_{k+1}/D_k` and its complement. -/
theorem bInv_ratio (h : Admissible n x) {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ n) :
    bInv x k / (bInv x k + bInv x (k + 1)) = D x (k + 1) / D x k ∧
    bInv x (k + 1) / (bInv x k + bInv x (k + 1)) = x k * D x (k - 1) / D x k := by
  have h0 := h.D_pos' (k := k - 1) (by omega)
  have h1 := h.D_pos' (k := k) (by omega)
  have h2 := h.D_pos' hk
  have hB := bInv_pos h k hk1 (by omega)
  have hrec : D x (k + 1) = D x k - x k * D x (k - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp [D_succ_succ]
  rw [bInv_succ x hk1 h0.ne' h1.ne' h2.ne']
  have hsum : bInv x k + bInv x k * (x k * D x (k - 1) / D x (k + 1))
      = bInv x k * D x k / D x (k + 1) := by
    field_simp; rw [hrec]; ring
  rw [hsum]
  constructor
  · field_simp
  · field_simp

/-- **Surjectivity of the forward map onto admissible data.** -/
theorem bInv_spec (h : Admissible n x) :
    (∀ k, 1 ≤ k → k ≤ n → 0 < bInv x k) ∧ ∀ k, 1 ≤ k → k ≤ n → X n (bInv x) k = x k := by
  refine ⟨fun k h1 h2 => bInv_pos h k h1 h2, fun k hk1 hkn => ?_⟩
  have hn := h.two_le
  have hrec : ∀ j, 1 ≤ j → D x (j + 1) = D x j - x j * D x (j - 1) := fun j hj => by
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp [D_succ_succ]
  by_cases hk : k = 1
  · subst hk
    rw [X_one]
    have := (bInv_ratio h le_rfl (by omega)).2
    rw [this]; simp
  by_cases hkn' : k = n
  · subst hkn'
    rw [X_last hn]
    have hr := (bInv_ratio h (k := k - 1) (by omega) (by omega)).1
    rw [show k - 1 + 1 = k by omega] at hr
    rw [hr]
    have hl := h.D_last
    rw [hrec k hk1] at hl
    have := h.D_pos' (k := k - 1) (by omega)
    field_simp
    linarith
  · rw [X_mid _ hk hkn']
    have hA := (bInv_ratio h (k := k - 1) (by omega) (by omega)).1
    have hB := (bInv_ratio h (k := k) hk1 (by omega)).2
    rw [show k - 1 + 1 = k by omega] at hA
    rw [mul_div_mul_comm, hA, hB]
    have := h.D_pos' (k := k - 1) (by omega)
    have := h.D_pos' (k := k) (by omega)
    field_simp

end inverse

section injective

variable {n : ℕ} {b : ℕ → ℝ}

/-- **Injectivity up to scale.** Every positive `b` is recovered from its image as
`b_k = b_1 · bInv (X b) k`. -/
theorem b_eq_bInv (hn : 2 ≤ n) (hb : ∀ j, 1 ≤ j → j ≤ n → 0 < b j) :
    ∀ k, 1 ≤ k → k ≤ n → b k = b 1 * bInv (X n b) k := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base => intro _; rw [bInv_one, mul_one]
  | succ k hk1 ih =>
    intro hk
    have hPk := D_eq_prod_aux hn hb k (by omega)
    have hDk1 := D_pos hn hb k (by omega)
    have hDk : 0 < D (X n b) k := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact D_pos hn hb m (by omega)
    have hDk0 : 0 < D (X n b) (k - 1) := by
      rcases Nat.lt_or_ge k 2 with h | h
      · rw [show k - 1 = 0 by omega]; simp
      · obtain ⟨m, hm⟩ : ∃ m, k - 1 = m + 1 := ⟨k - 2, by omega⟩
        rw [hm]; exact D_pos hn hb m (by omega)
    rw [bInv_succ _ hk1 hDk0.ne' hDk.ne' hDk1.ne', ← mul_assoc, ← ih (by omega)]
    -- `x_k D_{k-1} = D_k - D_{k+1}` and `D_{k+1} = D_k r_k`
    have hrec : D (X n b) (k + 1) = D (X n b) k - X n b k * D (X n b) (k - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp [D_succ_succ]
    have hxD : X n b k * D (X n b) (k - 1) = D (X n b) k - D (X n b) (k + 1) := by linarith
    rw [mul_div_assoc', hxD]
    have hr : D (X n b) (k + 1) = D (X n b) k * r b k := by
      rw [hPk.1, hPk.2]
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp [P_succ]
    rw [hr]; unfold r
    have := hb k hk1 (by omega); have := hb (k + 1) (by omega) hk
    field_simp; ring

/-- Two positive leg-square vectors with the same Gram data are proportional. -/
theorem X_inj_scale {b' : ℕ → ℝ} (hn : 2 ≤ n) (hb : ∀ j, 1 ≤ j → j ≤ n → 0 < b j)
    (hb' : ∀ j, 1 ≤ j → j ≤ n → 0 < b' j) (hX : ∀ k, X n b k = X n b' k) :
    ∃ c : ℝ, 0 < c ∧ ∀ k, 1 ≤ k → k ≤ n → b' k = c * b k := by
  have hXe : X n b = X n b' := funext hX
  have h1 := hb 1 le_rfl (by omega); have h1' := hb' 1 le_rfl (by omega)
  refine ⟨b' 1 / b 1, by positivity, fun k hk1 hk => ?_⟩
  rw [b_eq_bInv hn hb' k hk1 hk, b_eq_bInv hn hb k hk1 hk, hXe]
  field_simp

end injective

end OrthoschemeGram
