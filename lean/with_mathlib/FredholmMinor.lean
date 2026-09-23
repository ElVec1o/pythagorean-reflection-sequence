import Mathlib

/-!
# FredholmMinor — the principal minors of the travel kernel (Room C, thm:fredholm (iii))

1. `det_maxMat` : for any `y : ℕ → R` (`R` a commutative ring) and every `k`,
      `det (y_{max(i,j)})_{i,j ≤ k} = y_k · ∏_{i<k} (y_i - y_{i+1})`.
   `det_min_antitone` : for `x` antitone (decreasing), `det [min(x_i,x_j)]_{i,j<k+1}` equals the same.
2. `det_T_minor`, `det_S_minor` : for a monotone index sequence `s`,
      `det [2q^{1+s_i} q^{max(s_i,s_j)}] = det [√d_i q^{max(s_i,s_j)} √d_j]
         = (2q)^{k+1} q^{2 Σ s_i} ∏_{i<k} (1 - q^{s_{i+1}-s_i})`.
3. `gap_hasSum` / `gap_tsum` : for `0 < q < 1`, `m ≥ 1`,
      `∑_{δ≥1} q^{mδ}(1-q^δ) = q^m(1-q)/((1-q^m)(1-q^{m+1}))`.
4. `C_hasSum` : the gap-sum closed form.  Parametrise `k = m+1` points by the first point
   `t ≥ 0` and the `m` gaps `δ_j = g_j + 1 ≥ 1` (`pts t g`); then
      `Σ_{t, g} det T[pts t g] = (2(1-q))^{k} q^{k²} / (q;q)_{2k}`
   as an honest `HasSum` over `ℕ × (Fin m → ℕ)`.
5. `pts_bijective` : `(t, g) ↦ pts t g` is a bijection from `ℕ × (Fin m → ℕ)` onto the
   strictly increasing `(m+1)`-tuples of naturals, i.e. onto the index sets `I` with `|I| = k`
   listed increasingly, so 4 is the sum over all `|I| = k`.
-/

namespace FredholmMinor

open Finset Matrix

/-! ## 1. The `max` matrix -/

/-- `maxMat y k = (y_{max(i,j)})_{i,j<k}`. -/
def maxMat {R : Type*} (y : ℕ → R) (k : ℕ) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i j => y (max (i : ℕ) (j : ℕ))

theorem det_maxMat {R : Type*} [CommRing R] (k : ℕ) : ∀ y : ℕ → R,
    (maxMat y (k + 1)).det = y k * ∏ i ∈ range k, (y i - y (i + 1)) := by
  induction k with
  | zero => intro y; simp [maxMat]
  | succ k ih =>
    intro y
    set M := maxMat y (k + 2) with hM
    have h01 : (0 : Fin (k + 2)) ≠ 1 := by simp
    rw [← Matrix.det_updateRow_add_smul_self M h01 (-1), Matrix.det_succ_row_zero,
      Fin.sum_univ_succ]
    have hrow : ∀ j : Fin (k + 1), (M.updateRow 0 (M 0 + (-1 : R) • M 1)) 0 j.succ = 0 := by
      intro j
      simp only [Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hM, maxMat,
        Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_succ]
      rw [max_eq_right (by omega : (0 : ℕ) ≤ j + 1), max_eq_right (by omega : 1 ≤ (j : ℕ) + 1)]
      ring
    simp only [hrow, mul_zero, zero_mul, sum_const_zero, add_zero]
    have hsub : (M.updateRow 0 (M 0 + (-1 : R) • M 1)).submatrix Fin.succ (Fin.succAbove 0)
        = maxMat (fun i => y (i + 1)) (k + 1) := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_zero,
        Matrix.updateRow_ne (Fin.succ_ne_zero i), hM, maxMat, Matrix.of_apply, Fin.val_succ]
      congr 1; omega
    rw [hsub, ih]
    simp only [Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hM, maxMat,
      Matrix.of_apply, Fin.val_zero, Fin.val_one]
    rw [prod_range_succ' (fun i => y i - y (i + 1))]
    simp
    ring

/-- The principal-minor formula for `min` of a decreasing sequence. -/
theorem det_min_antitone {R : Type*} [CommRing R] [LinearOrder R] (x : ℕ → R) (hx : Antitone x)
    (k : ℕ) :
    (Matrix.of fun i j : Fin (k + 1) => min (x i) (x j)).det
      = x k * ∏ i ∈ range k, (x i - x (i + 1)) := by
  rw [← det_maxMat]
  congr 1; ext i j
  simp [maxMat, hx.map_max]

/-! ## 2. The principal minors of `T = D_e K` and `S = D_e^{1/2} K D_e^{1/2}` -/

lemma sum_prod_pow (q : ℝ) (s : ℕ → ℕ) (hs : Monotone s) (k : ℕ) :
    q ^ s k * ∏ i ∈ range k, (q ^ s i - q ^ s (i + 1))
      = q ^ (∑ i ∈ range (k + 1), s i) * ∏ i ∈ range k, (1 - q ^ (s (i + 1) - s i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, prod_range_succ, sum_range_succ]
    obtain ⟨d, hd⟩ : ∃ d, s (k + 1) = s k + d :=
      ⟨s (k + 1) - s k, by have := hs (Nat.le_add_right k 1); omega⟩
    rw [hd, Nat.add_sub_cancel_left, pow_add, pow_add]
    linear_combination (q ^ s k * q ^ d * (1 - q ^ d)) * ih

/-- `det T[I,I]` for `I = {s_0 ≤ … ≤ s_k}`, `T_{ab} = 2q^{1+a} q^{max(a,b)}`. -/
theorem det_T_minor (q : ℝ) (s : ℕ → ℕ) (hs : Monotone s) (k : ℕ) :
    (Matrix.of fun i j : Fin (k + 1) => 2 * q ^ (1 + s i) * q ^ max (s i) (s j)).det
      = (2 * q) ^ (k + 1) * q ^ (2 * ∑ i ∈ range (k + 1), s i)
          * ∏ i ∈ range k, (1 - q ^ (s (i + 1) - s i)) := by
  have hfac : (Matrix.of fun i j : Fin (k + 1) => 2 * q ^ (1 + s i) * q ^ max (s i) (s j))
      = Matrix.diagonal (fun i : Fin (k + 1) => 2 * q ^ (1 + s i)) * maxMat (fun i => q ^ s i) (k + 1) := by
    ext i j
    simp [maxMat, Matrix.diagonal_mul, hs.map_max]
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal, det_maxMat, sum_prod_pow q s hs,
    Fin.prod_univ_eq_prod_range (fun i => 2 * q ^ (1 + s i)) (k + 1)]
  rw [prod_mul_distrib, prod_const, card_range]
  simp only [pow_add, pow_one, prod_mul_distrib, prod_const, card_range, prod_pow_eq_pow_sum]
  ring

/-- The symmetric form `S = D^{1/2} K D^{1/2}` has the same principal minor (for `q > 0`). -/
theorem det_S_minor (q : ℝ) (hq : 0 < q) (s : ℕ → ℕ) (hs : Monotone s) (k : ℕ) :
    (Matrix.of fun i j : Fin (k + 1) =>
        Real.sqrt (2 * q ^ (1 + s i)) * q ^ max (s i) (s j) * Real.sqrt (2 * q ^ (1 + s j))).det
      = (2 * q) ^ (k + 1) * q ^ (2 * ∑ i ∈ range (k + 1), s i)
          * ∏ i ∈ range k, (1 - q ^ (s (i + 1) - s i)) := by
  rw [← det_T_minor q s hs k]
  set d : Fin (k + 1) → ℝ := fun i => Real.sqrt (2 * q ^ (1 + s i))
  have hfac : (Matrix.of fun i j : Fin (k + 1) =>
        Real.sqrt (2 * q ^ (1 + s i)) * q ^ max (s i) (s j) * Real.sqrt (2 * q ^ (1 + s j)))
      = Matrix.diagonal d * maxMat (fun i => q ^ s i) (k + 1) * Matrix.diagonal d := by
    ext i j
    simp [d, maxMat, Matrix.diagonal_mul, Matrix.mul_diagonal, hs.map_max]
  have hfacT : (Matrix.of fun i j : Fin (k + 1) => 2 * q ^ (1 + s i) * q ^ max (s i) (s j))
      = Matrix.diagonal (fun i => d i * d i) * maxMat (fun i => q ^ s i) (k + 1) := by
    ext i j
    have : 0 ≤ 2 * q ^ (1 + s i) := by positivity
    rw [Matrix.diagonal_mul]
    simp only [maxMat, Matrix.of_apply, d]
    rw [Real.mul_self_sqrt this, hs.map_max]
  simp only [hfac, hfacT, Matrix.det_mul, Matrix.det_diagonal, prod_mul_distrib]
  ring

/-! ## 3. The per-gap geometric sum -/

lemma one_sub_pow_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {m : ℕ} (hm : m ≠ 0) :
    0 < 1 - q ^ m := by
  have := pow_lt_one₀ hq0.le hq1 hm; linarith

/-- `∑_{δ≥1} q^{mδ}(1-q^δ) = q^m(1-q)/((1-q^m)(1-q^{m+1}))`, as a `HasSum` over `δ = d+1`. -/
theorem gap_hasSum {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {m : ℕ} (hm : 1 ≤ m) :
    HasSum (fun d : ℕ => q ^ (m * (d + 1)) * (1 - q ^ (d + 1)))
      (q ^ m * (1 - q) / ((1 - q ^ m) * (1 - q ^ (m + 1)))) := by
  set a := q ^ m with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hb0 : 0 ≤ a * q := by positivity
  have hb1 : a * q < 1 := by nlinarith
  have h1 := (hasSum_geometric_of_lt_one ha0 ha1).mul_left a
  have h2 := (hasSum_geometric_of_lt_one hb0 hb1).mul_left (a * q)
  have h := h1.sub h2
  have hfun : (fun d : ℕ => q ^ (m * (d + 1)) * (1 - q ^ (d + 1)))
      = (fun d : ℕ => a * a ^ d - a * q * (a * q) ^ d) := by
    funext d; rw [ha, ← pow_mul, mul_pow, ← pow_mul]; ring
  rw [hfun]
  convert h using 1
  have e1 : 0 < 1 - a := by linarith
  have e2 : 0 < 1 - a * q := by linarith
  have e3 : q ^ (m + 1) = a * q := by rw [ha, pow_succ]
  rw [e3]
  field_simp
  ring

theorem gap_tsum {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {m : ℕ} (hm : 1 ≤ m) :
    ∑' d : ℕ, q ^ (m * (d + 1)) * (1 - q ^ (d + 1))
      = q ^ m * (1 - q) / ((1 - q ^ m) * (1 - q ^ (m + 1))) :=
  (gap_hasSum hq0 hq1 hm).tsum_eq

/-! ## 4. The gap-sum closed form for `C_k` -/

/-- Products of nonnegative absolutely summable families over `Fin m → ℕ`. -/
theorem hasSum_pi_prod : ∀ (m : ℕ) (f : Fin m → ℕ → ℝ) (a : Fin m → ℝ),
    (∀ i, HasSum (f i) (a i)) → (∀ i n, 0 ≤ f i n) →
    HasSum (fun g : Fin m → ℕ => ∏ i, f i (g i)) (∏ i, a i) := by
  intro m
  induction m with
  | zero =>
    intro f a _ _
    simp
  | succ m ih =>
    intro f a hf h0
    have hrest := ih (fun i => f i.succ) (fun i => a i.succ) (fun i => hf i.succ)
      (fun i n => h0 i.succ n)
    have hprod : HasSum (fun p : ℕ × (Fin m → ℕ) => f 0 p.1 * ∏ i : Fin m, f i.succ (p.2 i))
        (a 0 * ∏ i : Fin m, a i.succ) :=
      HasSum.mul (f := f 0) (g := fun g : Fin m → ℕ => ∏ i : Fin m, f i.succ (g i)) (hf 0) hrest
        (Summable.mul_of_nonneg (f := f 0) (g := fun g : Fin m → ℕ => ∏ i : Fin m, f i.succ (g i))
          (hf 0).summable hrest.summable (fun n => h0 0 n)
          (fun g => prod_nonneg fun i _ => h0 i.succ (g i)))
    have e : (fun g : Fin (m + 1) → ℕ => ∏ i, f i (g i)) ∘ (Fin.consEquiv fun _ => ℕ)
        = fun p : ℕ × (Fin m → ℕ) => f 0 p.1 * ∏ i : Fin m, f i.succ (p.2 i) := by
      funext p
      simp [Fin.consEquiv, Fin.prod_univ_succ]
    have key : HasSum ((fun g : Fin (m + 1) → ℕ => ∏ i, f i (g i)) ∘ (Fin.consEquiv fun _ => ℕ))
        (a 0 * ∏ i : Fin m, a i.succ) := by rw [e]; exact hprod
    rw [Fin.prod_univ_succ]
    exact (Equiv.hasSum_iff _).mp key

/-- The extension of a gap vector to `ℕ`. -/
def G {m : ℕ} (g : Fin m → ℕ) (j : ℕ) : ℕ := if h : j < m then g ⟨j, h⟩ else 0

/-- The points `s_i = t + Σ_{j<i} (g_j + 1)`. -/
def pts {m : ℕ} (t : ℕ) (g : Fin m → ℕ) (i : ℕ) : ℕ := t + ∑ j ∈ range i, (G g j + 1)

lemma pts_succ {m : ℕ} (t : ℕ) (g : Fin m → ℕ) (i : ℕ) :
    pts t g (i + 1) = pts t g i + (G g i + 1) := by
  unfold pts; rw [sum_range_succ]; ring

lemma pts_strictMono {m : ℕ} (t : ℕ) (g : Fin m → ℕ) : StrictMono (pts t g) :=
  strictMono_nat_of_lt_succ fun i => by rw [pts_succ]; omega

lemma sum_sum_range (c : ℕ → ℕ) : ∀ n : ℕ,
    ∑ i ∈ range (n + 1), ∑ j ∈ range i, c j = ∑ j ∈ range n, (n - j) * c j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun j => (n + 1 - j) * c j), sum_range_succ c n,
      show n + 1 - n = 1 by omega, one_mul, ← add_assoc, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [show n + 1 - j = (n - j) + 1 by omega]; ring

lemma sum_pts {m : ℕ} (t : ℕ) (g : Fin m → ℕ) :
    ∑ i ∈ range (m + 1), pts t g i = (m + 1) * t + ∑ j ∈ range m, (m - j) * (G g j + 1) := by
  unfold pts
  rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, sum_sum_range]

/-- The per-gap summand `h_r(d) = q^{2r(d+1)} (1 - q^{d+1})`. -/
noncomputable def h (q : ℝ) (r d : ℕ) : ℝ := q ^ (2 * r * (d + 1)) * (1 - q ^ (d + 1))

/-- The factorised form of `det T[pts t g]`. -/
theorem det_T_pts (q : ℝ) (m t : ℕ) (g : Fin m → ℕ) :
    (Matrix.of fun i j : Fin (m + 1) =>
        2 * q ^ (1 + pts t g i) * q ^ max (pts t g i) (pts t g j)).det
      = (2 * q) ^ (m + 1) * ((q ^ (2 * (m + 1))) ^ t * ∏ j : Fin m, h q (m - j) (g j)) := by
  rw [det_T_minor q (pts t g) (pts_strictMono t g).monotone m, sum_pts]
  have hgap : ∀ i, pts t g (i + 1) - pts t g i = G g i + 1 := fun i => by rw [pts_succ]; omega
  simp only [hgap]
  have hG : ∏ j : Fin m, h q (m - j) (g j) = ∏ j ∈ range m, h q (m - j) (G g j) := by
    rw [← Fin.prod_univ_eq_prod_range (fun j => h q (m - j) (G g j)) m]
    refine Fintype.prod_congr _ _ fun j => ?_
    simp [G, j.isLt]
  rw [hG]
  unfold h
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, ← pow_mul]
  have hexp : 2 * ((m + 1) * t + ∑ j ∈ range m, (m - j) * (G g j + 1))
      = 2 * (m + 1) * t + ∑ j ∈ range m, 2 * (m - j) * (G g j + 1) := by
    rw [mul_add, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun j _ => by ring
  rw [hexp, pow_add]
  ring

/-- The per-gap constant `c(M) = q^M(1-q)/((1-q^M)(1-q^{M+1}))`. -/
noncomputable def c (q : ℝ) (M : ℕ) : ℝ := q ^ M * (1 - q) / ((1 - q ^ M) * (1 - q ^ (M + 1)))

/-- `(q;q)_n = ∏_{i<n} (1 - q^{i+1})`. -/
noncomputable def qpoch (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ range n, (1 - q ^ (i + 1))

/-- The finite product identity behind the closed form. -/
theorem closed_form_product {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : ∀ m : ℕ,
    (2 * q) ^ (m + 1) / (1 - q ^ (2 * (m + 1))) * ∏ r ∈ range m, c q (2 * (r + 1))
      = (2 * (1 - q)) ^ (m + 1) * q ^ ((m + 1) ^ 2) / qpoch q (2 * (m + 1)) := by
  have hp : ∀ n, n ≠ 0 → 0 < 1 - q ^ n := fun n hn => one_sub_pow_pos hq0 hq1 hn
  intro m
  induction m with
  | zero =>
    simp only [zero_add, pow_one, mul_one, range_zero, prod_empty, qpoch, one_pow]
    rw [show (2 : ℕ) = 1 + 1 from rfl, prod_range_succ, prod_range_succ]
    have := hp 2 (by norm_num)
    have := hp 1 (by norm_num)
    simp only [range_zero, prod_empty, one_mul, zero_add, pow_one] at *
    field_simp
  | succ m ih =>
    rw [prod_range_succ, show 2 * (m + 1 + 1) = 2 * (m + 1) + 1 + 1 by ring, qpoch,
      prod_range_succ, prod_range_succ, ← qpoch]
    have hQ : 0 < qpoch q (2 * (m + 1)) := prod_pos fun i _ => hp (i + 1) (by omega)
    have e1 := hp (2 * (m + 1)) (by omega)
    have e2 := hp (2 * (m + 1) + 1) (by omega)
    have e3 := hp (2 * (m + 1) + 1 + 1) (by omega)
    have ih' : ∏ r ∈ range m, c q (2 * (r + 1))
        = (2 * (1 - q)) ^ (m + 1) * q ^ ((m + 1) ^ 2) / qpoch q (2 * (m + 1))
          * (1 - q ^ (2 * (m + 1))) / (2 * q) ^ (m + 1) := by
      rw [← ih]; field_simp
    rw [ih']
    unfold c
    rw [show 2 * (m + 1) + 1 + 1 = 2 * (m + 1 + 1) by ring] at e3 ⊢
    rw [show (m + 1 + 1) ^ 2 = (m + 1) ^ 2 + 2 * (m + 1) + 1 by ring,
      show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 from rfl]
    field_simp
    ring

/-- **The gap-sum closed form.** For `0 < q < 1` and `k = m+1` points,
`Σ_{t ≥ 0, g ∈ ℕ^m} det T[{pts t g}] = (2(1-q))^k q^{k²}/(q;q)_{2k}`. -/
theorem C_hasSum {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    HasSum (fun p : ℕ × (Fin m → ℕ) =>
        (Matrix.of fun i j : Fin (m + 1) =>
          2 * q ^ (1 + pts p.1 p.2 i) * q ^ max (pts p.1 p.2 i) (pts p.1 p.2 j)).det)
      ((2 * (1 - q)) ^ (m + 1) * q ^ ((m + 1) ^ 2) / qpoch q (2 * (m + 1))) := by
  set A := q ^ (2 * (m + 1)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hA1 : A < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have ht : HasSum (fun t : ℕ => A ^ t) (1 - A)⁻¹ := hasSum_geometric_of_lt_one hA0 hA1
  have hgaps : ∀ j : Fin m, HasSum (fun d => h q (m - j) d) (c q (2 * (m - j))) := fun j => by
    have := gap_hasSum hq0 hq1 (m := 2 * (m - j)) (by have := j.isLt; omega)
    unfold h c; convert this using 3 with d
  have hh0 : ∀ (j : Fin m) d, 0 ≤ h q (m - j) d := fun j d => by
    unfold h
    have : q ^ (d + 1) ≤ 1 := pow_le_one₀ hq0.le hq1.le
    have : 0 ≤ q ^ (2 * (m - j) * (d + 1)) := by positivity
    nlinarith
  have hg : HasSum (fun g : Fin m → ℕ => ∏ j : Fin m, h q (m - (j : ℕ)) (g j)) (∏ j : Fin m, c q (2 * (m - j))) :=
    hasSum_pi_prod m (fun j => h q (m - j)) (fun j => c q (2 * (m - j))) hgaps hh0
  have hsum : Summable (fun p : ℕ × (Fin m → ℕ) => A ^ p.1 * ∏ j : Fin m, h q (m - (j : ℕ)) (p.2 j)) :=
    Summable.mul_of_nonneg (f := fun t : ℕ => A ^ t)
      (g := fun g : Fin m → ℕ => ∏ j : Fin m, h q (m - (j : ℕ)) (g j)) ht.summable hg.summable
      (fun n => pow_nonneg hA0 n) (fun g => prod_nonneg fun j _ => hh0 j (g j))
  have hprod := HasSum.mul (f := fun t : ℕ => A ^ t)
    (g := fun g : Fin m → ℕ => ∏ j : Fin m, h q (m - (j : ℕ)) (g j)) ht hg hsum
  have hfin := hprod.mul_left ((2 * q) ^ (m + 1))
  have hreflect : ∏ j : Fin m, c q (2 * (m - j)) = ∏ r ∈ range m, c q (2 * (r + 1)) := by
    rw [Fin.prod_univ_eq_prod_range (fun j => c q (2 * (m - j))) m,
      ← prod_range_reflect (fun r => c q (2 * (r + 1))) m]
    refine prod_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    congr 2; omega
  have hval : (2 * q) ^ (m + 1) * ((1 - A)⁻¹ * ∏ j : Fin m, c q (2 * (m - j)))
      = (2 * (1 - q)) ^ (m + 1) * q ^ ((m + 1) ^ 2) / qpoch q (2 * (m + 1)) := by
    rw [← closed_form_product hq0 hq1 m, hreflect, hA, div_eq_mul_inv]
    ring
  have hfun : (fun p : ℕ × (Fin m → ℕ) =>
        (Matrix.of fun i j : Fin (m + 1) =>
          2 * q ^ (1 + pts p.1 p.2 i) * q ^ max (pts p.1 p.2 i) (pts p.1 p.2 j)).det)
      = fun p => (2 * q) ^ (m + 1) * (A ^ p.1 * ∏ j : Fin m, h q (m - (j : ℕ)) (p.2 j)) :=
    funext fun p => det_T_pts q m p.1 p.2
  rw [hfun, ← hval]
  exact hfin

/-! ## 5. The gap parametrisation covers every `k`-point index set exactly once -/

/-- `(t, g) ↦ (pts t g i)_{i ≤ m}` is a bijection onto strictly increasing tuples. -/
theorem pts_bijective (m : ℕ) :
    Function.Bijective (fun p : ℕ × (Fin m → ℕ) =>
      (⟨fun i : Fin (m + 1) => pts p.1 p.2 i,
        (pts_strictMono p.1 p.2).comp (Fin.strictMono_iff_lt_succ.mpr fun i => by simp)⟩ :
        {s : Fin (m + 1) → ℕ // StrictMono s})) := by
  constructor
  · rintro ⟨t, g⟩ ⟨t', g'⟩ hEq
    simp only [Subtype.mk.injEq] at hEq
    have hp : ∀ i : Fin (m + 1), pts t g i = pts t' g' i := fun i => congrFun hEq i
    have ht : t = t' := by simpa [pts] using hp 0
    subst ht
    refine Prod.ext rfl (funext fun j => ?_)
    have h1 := hp j.castSucc
    have h2 := hp j.succ
    simp only [Fin.val_castSucc, Fin.val_succ, pts_succ] at h1 h2
    have : G g j = G g' j := by omega
    simpa [G, j.isLt] using this
  · rintro ⟨s, hs⟩
    refine ⟨(s 0, fun j => s j.succ - s j.castSucc - 1), ?_⟩
    apply Subtype.ext
    funext i
    simp only
    induction i using Fin.induction with
    | zero => simp [pts]
    | succ j ih =>
      rw [show ((j.succ : Fin (m + 1)) : ℕ) = (j.castSucc : ℕ) + 1 by simp, pts_succ, ih]
      have hlt := hs (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
      simp only [G, Fin.val_castSucc, j.isLt, dif_pos, Fin.eta]
      omega

/-- **`C_k` as a sum over all `k`-point index sets.** Summing `det T[I,I]` over every strictly
increasing tuple `s_0 < ⋯ < s_m` (i.e. every `I ⊂ ℕ` with `|I| = k = m+1`, listed increasingly)
gives `(2(1-q))^k q^{k²}/(q;q)_{2k}`. -/
theorem C_hasSum_strictMono {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    HasSum (fun s : {s : Fin (m + 1) → ℕ // StrictMono s} =>
        (Matrix.of fun i j : Fin (m + 1) =>
          2 * q ^ (1 + s.1 i) * q ^ max (s.1 i) (s.1 j)).det)
      ((2 * (1 - q)) ^ (m + 1) * q ^ ((m + 1) ^ 2) / qpoch q (2 * (m + 1))) :=
  (Equiv.ofBijective _ (pts_bijective m)).hasSum_iff.mp (C_hasSum hq0 hq1 m)

end FredholmMinor
