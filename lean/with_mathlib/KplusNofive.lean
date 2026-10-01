/-
KplusNofive.lean
================
`thm:nofive` of `merged_novel_paper.tex`: for every `n >= 5` there is no `c ∈ [1,∞)^n` with `G(c)`
of signature `(n-1,1,1)`.  We prove the stronger statement: no `c ≥ 1` has exactly ONE negative
eigenvalue together with `det G(c) = 0`.

Route (the paper's, with interlacing replaced by `SylvesterNeg`):
  * `KplusIsolate.isolate_range`: any `c_i > 1` has `n-3 <= i <= 4`;
  * `n >= 8`: no such `i`, so `c = 1`; then `det = 0` forces `n ≡ 1 (mod 3)`, so `n >= 10` and the
    all-ones path has three disjoint non-adjacent triples, each with `Q = -1`: three negative
    directions;
  * `n = 5, 6`: the continuant gives `det G ≠ 0`;
  * `n = 7`: `det G = 1 - t^2 = 0` forces `t = 1`, the all-ones path, which has two such triples.
No sorry.
-/
import KplusIsolate
import KplusBij

namespace KplusNofive

open Matrix KplusPath KplusIsolate

variable {c : ℕ → ℝ} {n : ℕ}

/-- A `G`-orthogonal family of negative vectors gives that many negative eigenvalues. -/
theorem neg_family {k : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : G.IsHermitian)
    (vs : Fin k → (Fin (n + 1) → ℝ)) (piv : Fin k → Fin (n + 1))
    (hpiv : ∀ i j, vs i (piv j) = if i = j then 1 else 0)
    (hoff : ∀ i j, i ≠ j → vs i ⬝ᵥ (G *ᵥ vs j) = 0)
    (hdiag : ∀ i, vs i ⬝ᵥ (G *ᵥ vs i) < 0) :
    k ≤ Fintype.card {i // hG.eigenvalues i < 0} := by
  have hlin : LinearIndependent ℝ vs := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrFun hg (piv j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpiv, mul_ite, mul_one, mul_zero,
      Pi.zero_apply] at this
    simpa using this
  let U : Submodule ℝ (Fin (n + 1) → ℝ) := Submodule.span ℝ (Set.range vs)
  have hfin : Module.finrank ℝ U = k := by
    rw [finrank_span_eq_card hlin]; simp
  have hneg : ∀ x ∈ U, x ≠ 0 → x ⬝ᵥ (G *ᵥ x) < 0 := by
    intro x hx hx0
    obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
    have hQ : (∑ i, f i • vs i) ⬝ᵥ (G *ᵥ ∑ i, f i • vs i) = ∑ i, f i ^ 2 * (vs i ⬝ᵥ (G *ᵥ vs i)) := by
      simp only [mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · ring
      · intro j _ hj
        first | rw [hoff i j (Ne.symm hj)] | rw [hoff j i hj]
        ring
      · simp
    rw [hQ]
    obtain ⟨i0, hi0⟩ : ∃ i, f i ≠ 0 := by
      by_contra h; push Not at h; apply hx0; simp [h]
    have h1 : ∀ i, f i ^ 2 * (vs i ⬝ᵥ (G *ᵥ vs i)) ≤ 0 := fun i =>
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hdiag i).le
    have h2 : f i0 ^ 2 * (vs i0 ⬝ᵥ (G *ᵥ vs i0)) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (hdiag i0)
    have h3 := Finset.single_le_sum
      (f := fun i => -(f i ^ 2 * (vs i ⬝ᵥ (G *ᵥ vs i)))) (fun i _ => neg_nonneg.mpr (h1 i))
      (Finset.mem_univ i0)
    simp only [Finset.sum_neg_distrib] at h3
    linarith
  have := SylvesterNeg.finrank_neg_le G hG U hneg
  rwa [hfin] at this

/-! ### triples in the all-ones path -/

/-- Indicator of the triple `{m, m+1, m+2}`. -/
def tvec (n m : ℕ) : Fin (n + 1) → ℝ := fun x => if m ≤ x.val ∧ x.val ≤ m + 2 then 1 else 0

theorem tvec_cross (c : ℕ → ℝ) {m m' : ℕ} (h : m + 4 ≤ m' ∨ m' + 4 ≤ m) :
    tvec n m ⬝ᵥ (pg c n *ᵥ tvec n m') = 0 := by
  simp only [dotProduct, mulVec]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : m ≤ x.val ∧ x.val ≤ m + 2
  · have : ∑ y, pg c n x y * tvec n m' y = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : m' ≤ y.val ∧ y.val ≤ m' + 2
      · rw [pg_far x y (by omega)]; ring
      · simp [tvec, hy]
    rw [this]; ring
  · simp [tvec, hx]

theorem tvec_self (c : ℕ → ℝ) (hc1 : ∀ k, 1 ≤ k → k ≤ n → c k = 1) {m : ℕ} (hm : m + 2 ≤ n) :
    tvec n m ⬝ᵥ (pg c n *ᵥ tvec n m) = -1 := by
  let r0 : Fin (n + 1) := ⟨m, by omega⟩
  let r1 : Fin (n + 1) := ⟨m + 1, by omega⟩
  let r2 : Fin (n + 1) := ⟨m + 2, by omega⟩
  have htv : tvec n m = Pi.single r0 1 + Pi.single r1 1 + Pi.single r2 1 := by
    funext x
    simp only [tvec, Pi.add_apply, Pi.single_apply, Fin.ext_iff, r0, r1, r2]
    by_cases h0 : (x : ℕ) = m
    · simp [h0]
    · by_cases h1 : (x : ℕ) = m + 1
      · simp [h1]
      · by_cases h2 : (x : ℕ) = m + 2
        · simp [h2]
        · have : ¬ (m ≤ x.val ∧ x.val ≤ m + 2) := by omega
          simp [this, h0, h1, h2]
  rw [htv]
  simp only [mulVec_add, dotProduct_add, add_dotProduct, bil_single]
  have c1 : c (m + 1) = 1 := hc1 _ (by omega) (by omega)
  have c2 : c (m + 2) = 1 := hc1 _ (by omega) (by omega)
  rw [pg_diag r0, pg_diag r1, pg_diag r2,
    show pg c n r0 r1 = -c (m + 1) from pg_succ r0 r1 (by simp [r0, r1]),
    show pg c n r1 r0 = -c (m + 1) from pg_pred r1 r0 (by simp [r0, r1]),
    show pg c n r1 r2 = -c (m + 2) from pg_succ r1 r2 (by simp [r1, r2]),
    show pg c n r2 r1 = -c (m + 2) from pg_pred r2 r1 (by simp [r1, r2]),
    show pg c n r0 r2 = 0 from pg_far r0 r2 (Or.inl (by simp [r0, r2])),
    show pg c n r2 r0 = 0 from pg_far r2 r0 (Or.inr (by simp [r0, r2])), c1, c2]
  ring

/-- `k` separated triples in the all-ones path give `k` negative eigenvalues. -/
theorem ones_negCount (hc1 : ∀ m, 1 ≤ m → m ≤ n → c m = 1) {k : ℕ} (hk : 4 * k + 2 ≤ n + 4) :
    k ≤ negCount c n := by
  unfold negCount
  refine neg_family (pg c n) (pg_herm c n) (fun j : Fin k => tvec n (4 * j.val))
    (fun j => ⟨4 * j.val, by have := j.isLt; omega⟩) ?_ ?_ ?_
  · intro i j
    simp only [tvec, Fin.ext_iff]
    have := i.isLt; have := j.isLt
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro i j hij
    have h' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    exact tvec_cross c (by omega)
  · intro i
    have := i.isLt
    rw [tvec_self c hc1 (by omega)]; norm_num

/-! ### the all-ones continuant -/

theorem D_ones_succ3 (k : ℕ) : D (fun _ => (1 : ℝ)) (k + 3) = - D (fun _ => (1 : ℝ)) k := by
  have e1 : D (fun _ => (1 : ℝ)) (k + 3) =
      D (fun _ => (1 : ℝ)) (k + 2) - (1 : ℝ) ^ 2 * D (fun _ => (1 : ℝ)) (k + 1) := rfl
  have e2 : D (fun _ => (1 : ℝ)) (k + 2) =
      D (fun _ => (1 : ℝ)) (k + 1) - (1 : ℝ) ^ 2 * D (fun _ => (1 : ℝ)) k := rfl
  rw [e1, e2]; ring

theorem D_ones_zero_iff (k : ℕ) : D (fun _ => (1 : ℝ)) k = 0 ↔ k % 3 = 2 := by
  have key : ∀ q r : ℕ, r < 3 →
      D (fun _ => (1 : ℝ)) (3 * q + r) = (-1) ^ q * D (fun _ => (1 : ℝ)) r := by
    intro q
    induction q with
    | zero => intro r _; simp
    | succ q ih =>
      intro r hr
      have : 3 * (q + 1) + r = (3 * q + r) + 3 := by ring
      rw [this, D_ones_succ3, ih r hr, pow_succ]; ring
  have hk : k = 3 * (k / 3) + k % 3 := by omega
  have hr : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [hk, key (k / 3) (k % 3) hr]
  have hmod : (3 * (k / 3) + k % 3) % 3 = k % 3 := by omega
  rw [hmod]
  have hne : ((-1 : ℝ) ^ (k / 3)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [mul_eq_zero, or_iff_right hne]
  interval_cases h : k % 3 <;> simp [D]

/-- All-ones case: one negative eigenvalue and a zero determinant is impossible for `n >= 5`. -/
theorem ones_case (hn : 5 ≤ n) (hc1 : ∀ m, 1 ≤ m → m ≤ n → c m = 1) (hneg : negCount c n = 1)
    (hdet : (pg c n).det = 0) : False := by
  have hD : D c (n + 1) = 0 := by rw [← (pg_det_eq_D c n).1]; exact hdet
  have hcong : D c (n + 1) = D (fun _ => (1 : ℝ)) (n + 1) :=
    KplusBij.D_congr (c' := fun _ => (1 : ℝ)) (fun i h1 h2 => hc1 i h1 h2) (n + 1) le_rfl
  rw [hcong] at hD
  have hmod := (D_ones_zero_iff (n + 1)).mp hD
  by_cases h7 : n = 7
  · have := ones_negCount (c := c) (n := n) hc1 (k := 2) (by omega)
    omega
  · have := ones_negCount (c := c) (n := n) hc1 (k := 3) (by omega)
    omega

/-- **`thm:nofive`.**  For `n >= 5` there is no `c ∈ [1,∞)^n` with `G(c)` having exactly one
negative eigenvalue and `det G(c) = 0`; in particular none of signature `(n-1,1,1)`. -/
theorem nofive (hn : 5 ≤ n) (hge : ∀ k, 1 ≤ k → k ≤ n → 1 ≤ c k) (hneg : negCount c n = 1)
    (hdet : (pg c n).det = 0) : False := by
  have hD : D c (n + 1) = 0 := by rw [← (pg_det_eq_D c n).1]; exact hdet
  have hrange : ∀ i, 1 ≤ i → i ≤ n → 1 < c i → n ≤ i + 3 ∧ i ≤ 4 :=
    fun i h1 h2 h3 => isolate_range hge hneg h1 h2 h3
  have hc1 : ∀ k, 1 ≤ k → k ≤ n → (k + 3 < n ∨ 4 < k) → c k = 1 := by
    intro k hk1 hk2 hk3
    by_contra h
    have hgt : 1 < c k := lt_of_le_of_ne (hge k hk1 hk2) (Ne.symm h)
    have := hrange k hk1 hk2 hgt
    omega
  by_cases hone : ∀ k, 1 ≤ k → k ≤ n → c k = 1
  · exact ones_case hn hone hneg hdet
  · push Not at hone
    obtain ⟨i, hi1, hin, hci⟩ := hone
    have hgt : 1 < c i := lt_of_le_of_ne (hge i hi1 hin) (Ne.symm hci)
    have hr := hrange i hi1 hin hgt
    have hn7 : n ≤ 7 := by omega
    interval_cases n
    · have a1 : c 1 = 1 := hc1 1 le_rfl (by omega) (by omega)
      have a5 : c 5 = 1 := hc1 5 (by omega) le_rfl (by omega)
      have e : D c 6 = c 2 ^ 2 * c 4 ^ 2 := by simp [D, a1, a5]; ring
      have h2 := hge 2 (by omega) (by omega)
      have h4 := hge 4 (by omega) (by omega)
      rw [e] at hD
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h4)]
    · have a1 : c 1 = 1 := hc1 1 le_rfl (by omega) (by omega)
      have a2 : c 2 = 1 := hc1 2 (by omega) (by omega) (by omega)
      have a5 : c 5 = 1 := hc1 5 (by omega) (by omega) (by omega)
      have a6 : c 6 = 1 := hc1 6 (by omega) le_rfl (by omega)
      have e : D c 7 = 1 := by simp [D, a1, a2, a5, a6]
      rw [e] at hD
      norm_num at hD
    · have a1 : c 1 = 1 := hc1 1 le_rfl (by omega) (by omega)
      have a2 : c 2 = 1 := hc1 2 (by omega) (by omega) (by omega)
      have a3 : c 3 = 1 := hc1 3 (by omega) (by omega) (by omega)
      have a5 : c 5 = 1 := hc1 5 (by omega) (by omega) (by omega)
      have a6 : c 6 = 1 := hc1 6 (by omega) (by omega) (by omega)
      have a7 : c 7 = 1 := hc1 7 (by omega) le_rfl (by omega)
      have e : D c 8 = 1 - c 4 ^ 2 := by simp [D, a1, a2, a3, a5, a6, a7]
      rw [e] at hD
      have h4 := hge 4 (by omega) (by omega)
      have : c 4 = 1 := by nlinarith
      have hall : ∀ k, 1 ≤ k → k ≤ 7 → c k = 1 := by
        intro k hk1 hk2
        by_cases hk4 : k = 4
        · subst hk4; exact this
        · exact hc1 k hk1 hk2 (by omega)
      exact ones_case (by omega) hall hneg hdet

end KplusNofive

#print axioms KplusNofive.neg_family
#print axioms KplusNofive.nofive
