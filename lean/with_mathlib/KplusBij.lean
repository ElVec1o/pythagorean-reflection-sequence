/-
KplusBij.lean
=============
`lem:Kplus` (iii): `a ↦ c(a)` is a bijection from `R_{>0}^n` modulo scaling onto `K^+`, with
inverse `(a_k/a_{k+1})^2 = rho_k/(1-rho_k)`, `rho_k = D_{k+1}/D_k`.  No sorry.

  * `cOf_scale`      : `c(s a) = c(a)` for `s > 0`.
  * `inverse_formula`: `r_k(a) = rho_k/(1-rho_k)` at `c = c(a)`.
  * `cOf_inj`        : `c(a) = c(a')` implies `a' = s a` on indices `1..n`.
  * `cOf_surj`       : every `c ∈ K^+` is `c(a)` for some `a > 0`.
-/
import KplusMain

namespace KplusBij

open KplusPath KplusForward KplusMain KplusLocus

variable {n : ℕ}

/-! ### scale invariance -/

theorem cOf_scale (hn : 2 ≤ n) (a : ℕ → ℝ) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) {s : ℝ}
    (hs : 0 < s) (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    cOf n (fun k => s * a k) i = cOf n a i := by
  have key : ∀ u : ℝ, 0 ≤ u → Real.sqrt (s ^ 2 * u) = s * Real.sqrt u := by
    intro u hu
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  unfold cOf
  by_cases h1 : i = 1
  · subst h1; simp only [if_true]
    have a1 := ha 1 le_rfl (by omega)
    have a2 := ha 2 (by omega) hn
    have : (s * a 1) ^ 2 + (s * a 2) ^ 2 = s ^ 2 * (a 1 ^ 2 + a 2 ^ 2) := by ring
    rw [this, key _ (by positivity)]
    have : 0 < Real.sqrt (a 1 ^ 2 + a 2 ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  · by_cases hn' : i = n
    · subst hn'; simp only [if_neg h1, if_true]
      have a1 := ha (i - 1) (by omega) (by omega)
      have a2 := ha i hi1 le_rfl
      have : (s * a (i - 1)) ^ 2 + (s * a i) ^ 2 = s ^ 2 * (a (i - 1) ^ 2 + a i ^ 2) := by ring
      rw [this, key _ (by positivity)]
      have : 0 < Real.sqrt (a (i - 1) ^ 2 + a i ^ 2) := Real.sqrt_pos.mpr (by positivity)
      field_simp
    · simp only [if_neg h1, if_neg hn']
      have a1 := ha (i - 1) (by omega) (by omega)
      have a2 := ha i hi1 hin
      have a3 := ha (i + 1) (by omega) (by omega)
      have : (s * a (i - 1) ^ 2 * 0 + ((s * a (i - 1)) ^ 2 + (s * a i) ^ 2) *
          ((s * a i) ^ 2 + (s * a (i + 1)) ^ 2)) =
          s ^ 4 * ((a (i - 1) ^ 2 + a i ^ 2) * (a i ^ 2 + a (i + 1) ^ 2)) := by ring
      have e : ((s * a (i - 1)) ^ 2 + (s * a i) ^ 2) * ((s * a i) ^ 2 + (s * a (i + 1)) ^ 2) =
          (s ^ 2) ^ 2 * ((a (i - 1) ^ 2 + a i ^ 2) * (a i ^ 2 + a (i + 1) ^ 2)) := by ring
      rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      have : 0 < Real.sqrt ((a (i - 1) ^ 2 + a i ^ 2) * (a i ^ 2 + a (i + 1) ^ 2)) :=
        Real.sqrt_pos.mpr (by positivity)
      field_simp

/-! ### inverse formula -/

/-- `rho_k = D_{k+1}/D_k`. -/
noncomputable def rhoD (c : ℕ → ℝ) (k : ℕ) : ℝ := D c (k + 1) / D c k

/-- **Inverse formula**: at `c = c(a)`, `(a_k/a_{k+1})^2 = rho_k/(1-rho_k)`, `rho_k = D_{k+1}/D_k`,
and `rho_k = r_k/(1+r_k)`. -/
theorem inverse_formula (hn : 2 ≤ n) (a : ℕ → ℝ) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ n) :
    rhoD (cOf n a) k = rOf a k / (1 + rOf a k) ∧
      (a k / a (k + 1)) ^ 2 = rhoD (cOf n a) k / (1 - rhoD (cOf n a) k) := by
  obtain ⟨hratio, hpos, -⟩ := forward_formula n hn a ha
  have hr := rOf_pos n a ha k hk1 hk2
  have hDk := hpos k hk1 (by omega)
  have h1 : rhoD (cOf n a) k = rOf a k / (1 + rOf a k) := by
    unfold rhoD
    rw [hratio k hk1 hk2]
    simp only [rho]
    field_simp
  refine ⟨h1, ?_⟩
  rw [h1]
  have : (a k / a (k + 1)) ^ 2 = rOf a k := rfl
  rw [this]
  have hne : (1 + rOf a k) ≠ 0 := by positivity
  field_simp
  ring

/-! ### injectivity modulo scaling -/

theorem D_congr {c c' : ℕ → ℝ} {m : ℕ} (h : ∀ i, 1 ≤ i → i ≤ m → c i = c' i) :
    ∀ k, k ≤ m + 1 → D c k = D c' k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k, ih, hk with
    | 0, _, _ => rfl
    | 1, _, _ => rfl
    | (j + 2), ih, hk =>
      have e1 : D c (j + 2) = D c (j + 1) - c (j + 1) ^ 2 * D c j := rfl
      have e2 : D c' (j + 2) = D c' (j + 1) - c' (j + 1) ^ 2 * D c' j := rfl
      rw [e1, e2, ih (j + 1) (by omega) (by omega), ih j (by omega) (by omega),
        h (j + 1) (by omega) (by omega)]

theorem cOf_inj (hn : 2 ≤ n) (a a' : ℕ → ℝ) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i)
    (ha' : ∀ i, 1 ≤ i → i ≤ n → 0 < a' i)
    (h : ∀ i, 1 ≤ i → i ≤ n → cOf n a i = cOf n a' i) :
    ∃ s : ℝ, 0 < s ∧ ∀ i, 1 ≤ i → i ≤ n → a' i = s * a i := by
  have hD := D_congr h
  have hr : ∀ k, 1 ≤ k → k + 1 ≤ n → (a k / a (k + 1)) = (a' k / a' (k + 1)) := by
    intro k hk1 hk2
    have e1 := (inverse_formula hn a ha k hk1 hk2).2
    have e2 := (inverse_formula hn a' ha' k hk1 hk2).2
    have hrho : rhoD (cOf n a) k = rhoD (cOf n a') k := by
      unfold rhoD
      rw [hD (k + 1) (by omega), hD k (by omega)]
    rw [hrho] at e1
    have hsq : (a k / a (k + 1)) ^ 2 = (a' k / a' (k + 1)) ^ 2 := by rw [e1, e2]
    have p1 : 0 < a k / a (k + 1) := div_pos (ha k hk1 (by omega)) (ha (k + 1) (by omega) hk2)
    have p2 : 0 < a' k / a' (k + 1) :=
      div_pos (ha' k hk1 (by omega)) (ha' (k + 1) (by omega) hk2)
    exact (pow_left_inj₀ p1.le p2.le two_ne_zero).mp hsq
  refine ⟨a' 1 / a 1, div_pos (ha' 1 le_rfl (by omega)) (ha 1 le_rfl (by omega)), ?_⟩
  intro i hi1 hin
  induction i, hi1 using Nat.le_induction with
  | base => have := ha 1 le_rfl (by omega); field_simp
  | succ k hk ih =>
    have ih' := ih (by omega)
    have hk' := hr k hk hin
    have a1 := ha k hk (by omega)
    have a2 := ha (k + 1) (by omega) hin
    have a3 := ha' k hk (by omega)
    have a4 := ha' (k + 1) (by omega) hin
    rw [div_eq_div_iff a2.ne' a4.ne'] at hk'
    have : a' (k + 1) = a' k * a (k + 1) / a k := by
      field_simp; linarith
    rw [this, ih']
    field_simp

/-! ### surjectivity onto `K^+` -/

section surj

variable {c : ℕ → ℝ}

/-- `r_k := rho_k/(1-rho_k)`. -/
noncomputable def rInv (c : ℕ → ℝ) (k : ℕ) : ℝ := rhoD c k / (1 - rhoD c k)

theorem rho_bounds (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i)
    (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < D c k) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ n) :
    0 < rhoD c k ∧ rhoD c k < 1 := by
  have h1 := hpos k hk1 (by omega)
  have h2 := hpos (k + 1) (by omega) hk2
  have hD0 : 0 < D c (k - 1) := by
    rcases Nat.eq_zero_or_pos (k - 1) with h | h
    · rw [h]; simp [D]
    · exact hpos (k - 1) h (by omega)
  have hrec : D c (k + 1) = D c k - c k ^ 2 * D c (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rfl
  have hck := hc k hk1 (by omega)
  refine ⟨div_pos h2 h1, ?_⟩
  unfold rhoD
  rw [div_lt_one h1, hrec]
  have : 0 < c k ^ 2 * D c (k - 1) := by positivity
  linarith

theorem rInv_pos (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i)
    (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < D c k) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ n) :
    0 < rInv c k := by
  obtain ⟨h1, h2⟩ := rho_bounds hc hpos k hk1 hk2
  unfold rInv
  exact div_pos h1 (by linarith)

theorem rho_of_rInv (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i)
    (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < D c k) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ n) :
    rInv c k / (1 + rInv c k) = rhoD c k ∧ 1 / (1 + rInv c k) = 1 - rhoD c k := by
  obtain ⟨h1, h2⟩ := rho_bounds hc hpos k hk1 hk2
  have hne : 1 - rhoD c k ≠ 0 := by linarith
  unfold rInv
  constructor <;> field_simp <;> ring

/-- A positive leg sequence realising prescribed ratios `r_k`. -/
noncomputable def legs (r : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | s, (j + 1) => legs r s j / Real.sqrt (r (j + 1))

noncomputable def aSeq (r : ℕ → ℝ) (k : ℕ) : ℝ := legs r 0 (k - 1)

theorem aSeq_pos (r : ℕ → ℝ) (hr : ∀ k, 1 ≤ k → 0 < r k) : ∀ k, 0 < aSeq r k := by
  have : ∀ j, 0 < legs r 0 j := by
    intro j
    induction j with
    | zero => simp [legs]
    | succ j ih =>
      simp only [legs]
      exact div_pos ih (Real.sqrt_pos.mpr (hr (j + 1) (by omega)))
  intro k; exact this _

theorem aSeq_ratio (r : ℕ → ℝ) (hr : ∀ k, 1 ≤ k → 0 < r k) (k : ℕ) (hk : 1 ≤ k) :
    (aSeq r k / aSeq r (k + 1)) ^ 2 = r k := by
  have e : aSeq r (k + 1) = aSeq r k / Real.sqrt (r k) := by
    unfold aSeq
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rfl
  rw [e]
  have hp := hr k hk
  have hs : 0 < Real.sqrt (r k) := Real.sqrt_pos.mpr hp
  have ha := aSeq_pos r hr k
  have : aSeq r k / (aSeq r k / Real.sqrt (r k)) = Real.sqrt (r k) := by field_simp
  rw [this]
  exact Real.sq_sqrt hp.le

theorem X_congr {r r' : ℕ → ℝ} (h : ∀ k, 1 ≤ k → k + 1 ≤ n → r k = r' k) (i : ℕ)
    (hi1 : 1 ≤ i) (hin : i ≤ n) (hn : 2 ≤ n) : X n r i = X n r' i := by
  unfold X
  by_cases h1 : i = 1
  · subst h1; simp only [if_true]; rw [h 1 le_rfl (by omega)]
  · by_cases hn' : i = n
    · subst hn'; simp only [if_neg h1, if_true]
      rw [h (i - 1) (by omega) (by omega)]
    · simp only [if_neg h1, if_neg hn']
      rw [h (i - 1) (by omega) (by omega), h i (by omega) (by omega)]

/-- **Surjectivity**: every `c ∈ K^+` is `c(a)` for some `a > 0`. -/
theorem cOf_surj (hn : 2 ≤ n) (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i) (hK : InK c n) :
    ∃ a : ℕ → ℝ, (∀ i, 1 ≤ i → i ≤ n → 0 < a i) ∧ ∀ i, 1 ≤ i → i ≤ n → cOf n a i = c i := by
  obtain ⟨hpos, hlast⟩ := D_of_inK hc hK
  have hrpos : ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < rInv c k := rInv_pos hc hpos
  have hrpos' : ∀ k, 1 ≤ k → 0 < (fun k => if k + 1 ≤ n then rInv c k else 1) k := by
    intro k hk
    by_cases h : k + 1 ≤ n
    · simp only [if_pos h]; exact hrpos k hk h
    · simp only [if_neg h]; exact one_pos
  set r : ℕ → ℝ := fun k => if k + 1 ≤ n then rInv c k else 1 with hrdef
  have hagree : ∀ k, 1 ≤ k → k + 1 ≤ n → r k = rInv c k := by
    intro k _ h; simp only [hrdef, if_pos h]
  refine ⟨aSeq r, fun i hi1 hin => aSeq_pos r hrpos' i, ?_⟩
  intro i hi1 hin
  have hrO : ∀ k, 1 ≤ k → k + 1 ≤ n → rOf (aSeq r) k = rInv c k := by
    intro k hk1 hk2
    rw [← hagree k hk1 hk2]; exact aSeq_ratio r hrpos' k hk1
  -- c_i^2 = X n (rInv c) i
  have hsq : c i ^ 2 = X n (rInv c) i := by
    have hD0 : ∀ j, j ≤ n → 0 < D c j ∨ j = 0 := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with h | h
      · exact Or.inr h
      · exact Or.inl (hpos j h hj)
    have hrec : ∀ j, 1 ≤ j → D c (j + 1) = D c j - c j ^ 2 * D c (j - 1) := by
      intro j hj
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; rfl
    have hDpos : ∀ j, j ≤ n → 0 < D c j := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp [D]
      · exact hpos j h hj
    have hratio : ∀ j, 1 ≤ j → j + 1 ≤ n → D c (j + 1) = rhoD c j * D c j := by
      intro j _ _
      unfold rhoD
      field_simp [(hDpos j (by omega)).ne']
    unfold X
    by_cases h1 : i = 1
    · subst h1
      simp only [if_true]
      obtain ⟨-, h2⟩ := rho_of_rInv hc hpos 1 le_rfl (by omega)
      rw [h2]
      have e := hrec 1 le_rfl
      have e2 := hratio 1 le_rfl (by omega)
      simp only [D] at e e2 ⊢
      nlinarith [e, e2]
    · by_cases hn' : i = n
      · subst hn'
        simp only [if_neg h1, if_true]
        obtain ⟨m, hm⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        have hk : 1 ≤ i - 1 := by omega
        obtain ⟨h2, -⟩ := rho_of_rInv hc hpos (i - 1) hk (by omega)
        rw [h2]
        have e := hrec i (by omega)
        rw [hlast] at e
        have e2 := hratio (i - 1) hk (by omega)
        have hi : i - 1 + 1 = i := by omega
        rw [hi] at e2
        have hDi := hDpos (i - 1) (by omega)
        have hDi' := hDpos i le_rfl
        unfold rhoD
        rw [hi]
        field_simp
        nlinarith [e]
      · simp only [if_neg h1, if_neg hn']
        have hk : 1 ≤ i - 1 := by omega
        obtain ⟨h2, -⟩ := rho_of_rInv hc hpos (i - 1) hk (by omega)
        obtain ⟨-, h3⟩ := rho_of_rInv hc hpos i hi1 (by omega)
        have hi : i - 1 + 1 = i := by omega
        have h2' : rInv c (i - 1) / (1 + rInv c (i - 1)) = rhoD c (i - 1) := h2
        have hnum : rInv c (i - 1) / ((1 + rInv c (i - 1)) * (1 + rInv c i)) =
            rhoD c (i - 1) * (1 - rhoD c i) := by
          rw [← h2', ← h3]; field_simp
        rw [hnum]
        have e := hrec i hi1
        have e1 := hratio (i - 1) hk (by omega)
        have e2 := hratio i hi1 (by omega)
        rw [hi] at e1
        have hDi := hDpos (i - 1) (by omega)
        have hDi' := hDpos i (by omega)
        have : c i ^ 2 * D c (i - 1) = D c i - D c (i + 1) := by linarith
        have hfin : c i ^ 2 = (D c i - D c (i + 1)) / D c (i - 1) := by
          field_simp; linarith
        rw [hfin, e2]
        unfold rhoD
        rw [hi]
        field_simp
  have hcO := cOf_sq n hn (aSeq r) (fun j h1 h2 => aSeq_pos r hrpos' j) i hi1 hin
  have hX : X n (rOf (aSeq r)) i = X n (rInv c) i :=
    X_congr (fun k h1 h2 => hrO k h1 h2) i hi1 hin hn
  have hcpos : 0 < cOf n (aSeq r) i := by
    have := (cOf_mem_Kplus hn (aSeq r) (fun j h1 h2 => aSeq_pos r hrpos' j)).1 i hi1 hin
    exact this
  have : cOf n (aSeq r) i ^ 2 = c i ^ 2 := by rw [hcO, hX, hsq]
  exact (pow_left_inj₀ hcpos.le (hc i hi1 hin).le two_ne_zero).mp this

end surj

end KplusBij

#print axioms KplusBij.cOf_inj
#print axioms KplusBij.cOf_surj
