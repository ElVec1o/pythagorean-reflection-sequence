/-
KplusGram.lean
==============
`lem:Kplus` (ii), first half: `G(c(a))` is the Gram matrix of the unit facet normals of the
orthoscheme `O(a)`, signed so that consecutive normals have negative inner product.

Facet normals (`lem:normals`, `OrthoschemeNormals.lean`) in `R^n` with basis `e_1..e_n`:
  `m_0 = e_1`, `m_j = a_{j+1} e_j - a_j e_{j+1}` (1 <= j <= n-1), `m_n = e_n`;
`u_0 = -m_0`, `u_j = m_j / |m_j|`.  With the convention `a~_0 = -1`, `a~_{n+1} = 1` all three
cases are the single formula `m_j = a~_{j+1} e_j - a~_j e_{j+1}` (`e_0 = e_{n+1} = 0`).
Theorem `gram_normals`: `<u_i,u_j> = G(c(a))_{ij}`.  No sorry.
-/
import KplusBij

namespace KplusGram

open Matrix KplusPath KplusForward

variable {n : ℕ}

/-- Standard basis vector `e_ℓ` of `R^n`, 1-indexed (`e_0 = e_{n+1} = 0`). -/
def eI (n ℓ : ℕ) : Fin n → ℝ := fun k => if (k : ℕ) + 1 = ℓ then 1 else 0

theorem eI_dot (p q : ℕ) :
    eI n p ⬝ᵥ eI n q = if p = q ∧ 1 ≤ p ∧ p ≤ n then 1 else 0 := by
  unfold dotProduct eI
  by_cases h : p = q ∧ 1 ≤ p ∧ p ≤ n
  · obtain ⟨rfl, h1, h2⟩ := h
    rw [if_pos ⟨rfl, h1, h2⟩]
    rw [Finset.sum_eq_single (⟨p - 1, by omega⟩ : Fin n)]
    · simp only [Fin.val_mk]
      rw [if_pos (by omega)]; simp
    · intro b _ hb
      have : (b : ℕ) + 1 ≠ p := fun hh => hb (Fin.ext (by simp; omega))
      simp [this]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : (k : ℕ) + 1 = p
    · by_cases h2 : (k : ℕ) + 1 = q
      · exfalso; apply h; have := k.isLt; omega
      · simp [h2]
    · simp [h1]

/-- Extended legs: `a~_0 = -1`, `a~_{n+1} = 1`. -/
def at_ (n : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ := if k = 0 then -1 else if k = n + 1 then 1 else a k

/-- Unnormalised facet normal `m_j = a~_{j+1} e_j - a~_j e_{j+1}`. -/
def mv (n : ℕ) (a : ℕ → ℝ) (j : ℕ) : Fin n → ℝ :=
  at_ n a (j + 1) • eI n j - at_ n a j • eI n (j + 1)

/-- Squared length of `m_j`. -/
def Nsq (n : ℕ) (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  (if 1 ≤ j then at_ n a (j + 1) ^ 2 else 0) + (if j + 1 ≤ n then at_ n a j ^ 2 else 0)

/-- Sign making consecutive normals have negative inner product: `u_0 = -m_0`. -/
def sg (j : ℕ) : ℝ := if j = 0 then -1 else 1

/-- Unit facet normal. -/
noncomputable def uv (n : ℕ) (a : ℕ → ℝ) (j : ℕ) : Fin n → ℝ :=
  (sg j / Real.sqrt (Nsq n a j)) • mv n a j

theorem mv_dot (a : ℕ → ℝ) (i j : ℕ) :
    mv n a i ⬝ᵥ mv n a j =
      (if i = j ∧ 1 ≤ i ∧ i ≤ n then at_ n a (i + 1) * at_ n a (j + 1) else 0)
      - (if i = j + 1 ∧ 1 ≤ i ∧ i ≤ n then at_ n a (i + 1) * at_ n a j else 0)
      - (if i + 1 = j ∧ 1 ≤ i + 1 ∧ i + 1 ≤ n then at_ n a i * at_ n a (j + 1) else 0)
      + (if i + 1 = j + 1 ∧ 1 ≤ i + 1 ∧ i + 1 ≤ n then at_ n a i * at_ n a j else 0) := by
  unfold mv
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    eI_dot]
  split_ifs <;> ring

/-! ### values of `a~`, `N^2`, `sg` -/

theorem at_zero : at_ n a 0 = -1 := by simp [at_]
theorem at_last : at_ n a (n + 1) = 1 := by simp [at_]
theorem at_mid {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : at_ n a k = a k := by
  unfold at_; rw [if_neg (by omega), if_neg (by omega)]

theorem Nsq_zero (hn : 1 ≤ n) : Nsq n a 0 = 1 := by
  unfold Nsq
  rw [if_neg (by omega), if_pos (by omega), at_zero]; norm_num

theorem Nsq_last (hn : 1 ≤ n) : Nsq n a n = 1 := by
  unfold Nsq
  rw [if_pos hn, if_neg (by omega), at_last]; norm_num

theorem Nsq_mid {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 1 ≤ n) :
    Nsq n a j = a (j + 1) ^ 2 + a j ^ 2 := by
  unfold Nsq
  rw [if_pos h1, if_pos h2, at_mid (by omega) h2, at_mid h1 (by omega)]

theorem Nsq_pos (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) (hn : 1 ≤ n) {j : ℕ} (hj : j ≤ n) :
    0 < Nsq n a j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; rw [Nsq_zero hn]; exact one_pos
  · by_cases h2 : j + 1 ≤ n
    · rw [Nsq_mid h h2]
      have := ha j h (by omega)
      positivity
    · have : j = n := by omega
      subst this; rw [Nsq_last hn]; exact one_pos

/-! ### diagonal -/

theorem entry_diag (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) (hn : 1 ≤ n) {j : ℕ} (hj : j ≤ n) :
    uv n a j ⬝ᵥ uv n a j = 1 := by
  unfold uv
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, mv_dot]
  have hN := Nsq_pos ha hn hj
  have hs : Real.sqrt (Nsq n a j) * Real.sqrt (Nsq n a j) = Nsq n a j :=
    Real.mul_self_sqrt hN.le
  have hsg : sg j * sg j = 1 := by unfold sg; split_ifs <;> norm_num
  have hd : (if j = j ∧ 1 ≤ j ∧ j ≤ n then at_ n a (j + 1) * at_ n a (j + 1) else 0)
      - (if j = j + 1 ∧ 1 ≤ j ∧ j ≤ n then at_ n a (j + 1) * at_ n a j else 0)
      - (if j + 1 = j ∧ 1 ≤ j + 1 ∧ j + 1 ≤ n then at_ n a j * at_ n a (j + 1) else 0)
      + (if j + 1 = j + 1 ∧ 1 ≤ j + 1 ∧ j + 1 ≤ n then at_ n a j * at_ n a j else 0)
      = Nsq n a j := by
    by_cases h1 : 1 ≤ j <;> by_cases h2 : j + 1 ≤ n <;> simp [Nsq, h1, h2, hj, sq]
  have hsq : Real.sqrt (Nsq n a j) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  rw [hd]
  field_simp
  rw [← hs] at *
  nlinarith [hsg, hs, hN]

/-! ### cOf at the three kinds of index -/

theorem cOf_first : cOf n a 1 = a 2 / Real.sqrt (a 1 ^ 2 + a 2 ^ 2) := by simp [cOf]

theorem cOf_last (hn : 2 ≤ n) :
    cOf n a n = a (n - 1) / Real.sqrt (a (n - 1) ^ 2 + a n ^ 2) := by
  unfold cOf; rw [if_neg (by omega), if_pos rfl]

theorem cOf_mid {i : ℕ} (h1 : 2 ≤ i) (h2 : i + 1 ≤ n) :
    cOf n a i = a (i - 1) * a (i + 1) /
      Real.sqrt ((a (i - 1) ^ 2 + a i ^ 2) * (a i ^ 2 + a (i + 1) ^ 2)) := by
  unfold cOf; rw [if_neg (by omega), if_neg (by omega)]

/-! ### adjacent entries -/

theorem mv_dot_adj (a : ℕ → ℝ) {I : ℕ} (hI : I + 1 ≤ n) :
    mv n a I ⬝ᵥ mv n a (I + 1) = -(at_ n a I * at_ n a (I + 1 + 1)) := by
  rw [mv_dot, if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, by omega, hI⟩, if_neg (by omega)]
  ring

theorem entry_adj (hn : 2 ≤ n) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) {I : ℕ} (hI : I + 1 ≤ n) :
    uv n a I ⬝ᵥ uv n a (I + 1) = -cOf n a (I + 1) := by
  unfold uv
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, mv_dot_adj a hI]
  by_cases hI0 : I = 0
  · subst hI0
    have hN1 : Nsq n a 1 = a 2 ^ 2 + a 1 ^ 2 := by
      have := Nsq_mid (n := n) (a := a) (j := 1) le_rfl (by omega)
      simpa using this
    have h2 : at_ n a (0 + 1 + 1) = a 2 := at_mid (by omega) hn
    have a1 := ha 1 le_rfl (by omega)
    have a2 := ha 2 (by omega) hn
    simp only [zero_add, Nsq_zero (n := n) (a := a) (by omega), hN1, at_zero, h2, sg]
    simp only [cOf_first, if_true, if_neg (by omega : ¬ (1 : ℕ) = 0)]
    have hs : 0 < Real.sqrt (a 2 ^ 2 + a 1 ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [add_comm (a 1 ^ 2) (a 2 ^ 2)]
    simp only [Real.sqrt_one]
    field_simp
  · by_cases hIn : I + 1 = n
    · have hI1 : 1 ≤ I := by omega
      have hn1 : n - 1 = I := by omega
      rw [hIn, cOf_last hn, hn1]
      have hNI : Nsq n a I = a n ^ 2 + a I ^ 2 := by
        have := Nsq_mid (n := n) (a := a) (j := I) hI1 (by omega)
        rwa [hIn] at this
      have hNn : Nsq n a n = 1 := Nsq_last (by omega)
      have hAI : at_ n a I = a I := at_mid hI1 (by omega)
      have hA2 : at_ n a (n + 1) = 1 := at_last
      have aI := ha I hI1 (by omega)
      have an := ha n (by omega) le_rfl
      have hs : 0 < Real.sqrt (a n ^ 2 + a I ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have e1 : (I + 1 + 1) = n + 1 := by omega
      simp only [hNI, hNn, hAI, e1, hA2, sg, if_neg hI0, hIn, if_neg (by omega : ¬ n = 0),
        Real.sqrt_one]
      rw [add_comm (a n ^ 2) (a I ^ 2)]
      field_simp
    · have hI1 : 1 ≤ I := by omega
      have hmid1 : 2 ≤ I + 1 := by omega
      rw [cOf_mid hmid1 (by omega)]
      simp only [Nat.add_sub_cancel]
      have hNI : Nsq n a I = a (I + 1) ^ 2 + a I ^ 2 := Nsq_mid hI1 hI
      have hNI1 : Nsq n a (I + 1) = a (I + 1 + 1) ^ 2 + a (I + 1) ^ 2 :=
        Nsq_mid (by omega) (by omega)
      have hAI : at_ n a I = a I := at_mid hI1 (by omega)
      have hAI2 : at_ n a (I + 1 + 1) = a (I + 1 + 1) := at_mid (by omega) (by omega)
      have aI := ha I hI1 (by omega)
      have aI1 := ha (I + 1) (by omega) (by omega)
      have aI2 := ha (I + 1 + 1) (by omega) (by omega)
      have s1 : 0 < Real.sqrt (a (I + 1) ^ 2 + a I ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have s2 : 0 < Real.sqrt (a (I + 1 + 1) ^ 2 + a (I + 1) ^ 2) :=
        Real.sqrt_pos.mpr (by positivity)
      have hprod : Real.sqrt ((a I ^ 2 + a (I + 1) ^ 2) * (a (I + 1) ^ 2 + a (I + 1 + 1) ^ 2)) =
          Real.sqrt (a (I + 1) ^ 2 + a I ^ 2) * Real.sqrt (a (I + 1 + 1) ^ 2 + a (I + 1) ^ 2) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1; ring
      simp only [hNI, hNI1, hAI, hAI2, sg, if_neg hI0, if_neg (by omega : ¬ I + 1 = 0), hprod]
      field_simp

/-! ### far entries and assembly -/

theorem entry_far (a : ℕ → ℝ) {I J : ℕ} (h1 : I ≠ J) (h2 : I + 1 ≠ J) (h3 : I ≠ J + 1) :
    uv n a I ⬝ᵥ uv n a J = 0 := by
  unfold uv
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, mv_dot]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

/-- **`lem:Kplus` (ii), Gram identity.**  For legs `a_1..a_n > 0` (`n >= 2`), the Gram matrix of
the unit facet normals `u_0..u_n` of `O(a)` is exactly `G(c(a))`. -/
theorem gram_normals (hn : 2 ≤ n) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) (i j : Fin (n + 1)) :
    uv n a i ⬝ᵥ uv n a j = pg (cOf n a) n i j := by
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : (i : ℕ) = j
  · have : (i : ℕ) = j := hij
    rw [show (j : ℕ) = i from hij.symm, entry_diag ha (by omega) (by omega)]
    simp [pg, hij]
  · by_cases h1 : (i : ℕ) + 1 = j
    · rw [← h1, entry_adj hn ha (by omega)]
      simp [pg, hij, h1]
    · by_cases h2 : (j : ℕ) + 1 = i
      · rw [dotProduct_comm, ← h2, entry_adj hn ha (by omega)]
        simp only [pg]
        rw [if_neg hij, if_neg h1, if_pos h2, ← h2]
      · rw [entry_far a hij h1 (by omega)]
        simp [pg, hij, h1, h2]

end KplusGram

#print axioms KplusGram.gram_normals
