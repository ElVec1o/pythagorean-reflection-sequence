/-
KplusIsolate.lean
=================
`lem:isolate` of `merged_novel_paper.tex`:

  Suppose `G(c)` has signature `(n-1,1,1)` (in particular exactly ONE negative eigenvalue) with
  all `c_i >= 1`.  If `c_i > 1`, then the path `P_{n+1}` contains no three consecutive vertices
  disjoint from and non-adjacent to the edge `e_i = {i-1, i}`.  Consequently `n-3 <= i <= 4`.

The paper uses Cauchy interlacing; here the two test vectors `e_{i-1}+e_i` (`Q = 2 - 2c_i < 0`)
and `e_{a-1}+e_a+e_{a+1}` (`Q = 3 - 2c_a - 2c_{a+1} <= -1`) span a 2-dimensional negative-definite
subspace (their cross term vanishes), and `SylvesterNeg.finrank_neg_le` bounds that dimension by
the number of negative eigenvalues.  No sorry.
-/
import KplusPath
import SylvesterNeg

namespace KplusIsolate

open Matrix KplusPath

variable {c : ℕ → ℝ} {n : ℕ}

theorem pg_herm (c : ℕ → ℝ) (n : ℕ) : (pg c n).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  ext i j
  simp only [transpose_apply, pg]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all

/-- Number of negative eigenvalues of `G(c)`. -/
noncomputable def negCount (c : ℕ → ℝ) (n : ℕ) : ℕ :=
  Fintype.card {i // (pg_herm c n).eigenvalues i < 0}

/-- `bil G u w = u^T G w`. -/
theorem bil_single (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) :
    (Pi.single p (1 : ℝ) : Fin (n + 1) → ℝ) ⬝ᵥ (G *ᵥ (Pi.single q (1 : ℝ) : Fin (n + 1) → ℝ))
      = G p q := by
  simp [Matrix.mulVec_single_one, dotProduct_single]

theorem pg_diag (x : Fin (n + 1)) : pg c n x x = 1 := by simp [pg]

theorem pg_succ (x y : Fin (n + 1)) (h : (x : ℕ) + 1 = y) : pg c n x y = -c y := by
  simp only [pg]; rw [if_neg (by omega), if_pos h]

theorem pg_pred (x y : Fin (n + 1)) (h : (y : ℕ) + 1 = x) : pg c n x y = -c x := by
  simp only [pg]; rw [if_neg (by omega), if_neg (by omega), if_pos h]

theorem pg_far (x y : Fin (n + 1)) (h1 : (x : ℕ) + 2 ≤ y ∨ (y : ℕ) + 2 ≤ x) : pg c n x y = 0 := by
  simp only [pg]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem isolate (hge : ∀ k, 1 ≤ k → k ≤ n → 1 ≤ c k) (hsig : negCount c n = 1)
    {i a : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) (hci : 1 < c i) (ha1 : 1 ≤ a) (han : a + 1 ≤ n)
    (hsep : a + 4 ≤ i ∨ i + 3 ≤ a) : False := by
  let G := pg c n
  let p : Fin (n + 1) := ⟨i - 1, by omega⟩
  let q : Fin (n + 1) := ⟨i, by omega⟩
  let r0 : Fin (n + 1) := ⟨a - 1, by omega⟩
  let r1 : Fin (n + 1) := ⟨a, by omega⟩
  let r2 : Fin (n + 1) := ⟨a + 1, by omega⟩
  let v1 : Fin (n + 1) → ℝ := Pi.single p 1 + Pi.single q 1
  let v2 : Fin (n + 1) → ℝ := Pi.single r0 1 + Pi.single r1 1 + Pi.single r2 1
  have B11 : v1 ⬝ᵥ (G *ᵥ v1) = 2 - 2 * c i := by
    simp only [v1, mulVec_add, dotProduct_add, add_dotProduct, bil_single]
    rw [show G p p = 1 from pg_diag p, show G q q = 1 from pg_diag q,
      show G p q = -c i from pg_succ p q (by simp [p, q]; omega),
      show G q p = -c i from pg_pred q p (by simp [p, q]; omega)]
    ring
  have B22 : v2 ⬝ᵥ (G *ᵥ v2) = 3 - 2 * c a - 2 * c (a + 1) := by
    simp only [v2, mulVec_add, dotProduct_add, add_dotProduct, bil_single]
    rw [show G r0 r0 = 1 from pg_diag r0, show G r1 r1 = 1 from pg_diag r1,
      show G r2 r2 = 1 from pg_diag r2,
      show G r0 r1 = -c a from pg_succ r0 r1 (by simp [r0, r1]; omega),
      show G r1 r0 = -c a from pg_pred r1 r0 (by simp [r0, r1]; omega),
      show G r1 r2 = -c (a + 1) from pg_succ r1 r2 (by simp [r1, r2]),
      show G r2 r1 = -c (a + 1) from pg_pred r2 r1 (by simp [r1, r2]),
      show G r0 r2 = 0 from pg_far r0 r2 (Or.inl (by simp [r0, r2]; omega)),
      show G r2 r0 = 0 from pg_far r2 r0 (Or.inr (by simp [r0, r2]; omega))]
    ring
  have hfar : ∀ x ∈ ({p, q} : Set (Fin (n + 1))), ∀ y ∈ ({r0, r1, r2} : Set (Fin (n + 1))),
      G x y = 0 ∧ G y x = 0 := by
    intro x hx y hy
    have hx' : (x : ℕ) = i - 1 ∨ (x : ℕ) = i := by
      rcases hx with rfl | rfl <;> simp [p, q]
    have hy' : (y : ℕ) = a - 1 ∨ (y : ℕ) = a ∨ (y : ℕ) = a + 1 := by
      rcases hy with rfl | rfl | rfl <;> simp [r0, r1, r2]
    constructor
    · exact pg_far x y (by omega)
    · exact pg_far y x (by omega)
  have B12 : v1 ⬝ᵥ (G *ᵥ v2) = 0 := by
    simp only [v1, v2, mulVec_add, dotProduct_add, add_dotProduct, bil_single]
    rw [(hfar p (by simp) r0 (by simp)).1, (hfar p (by simp) r1 (by simp)).1,
      (hfar p (by simp) r2 (by simp)).1, (hfar q (by simp) r0 (by simp)).1,
      (hfar q (by simp) r1 (by simp)).1, (hfar q (by simp) r2 (by simp)).1]
    ring
  have B21 : v2 ⬝ᵥ (G *ᵥ v1) = 0 := by
    simp only [v1, v2, mulVec_add, dotProduct_add, add_dotProduct, bil_single]
    rw [(hfar p (by simp) r0 (by simp)).2, (hfar p (by simp) r1 (by simp)).2,
      (hfar p (by simp) r2 (by simp)).2, (hfar q (by simp) r0 (by simp)).2,
      (hfar q (by simp) r1 (by simp)).2, (hfar q (by simp) r2 (by simp)).2]
    ring
  have hca := hge a ha1 (by omega)
  have hca1 := hge (a + 1) (by omega) han
  -- the negative-definite plane
  have hlin : LinearIndependent ℝ ![v1, v2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hp := congrFun hst p
    have hr := congrFun hst r1
    have hpq : p ≠ q := by
      intro h; have := congrArg Fin.val h; change i - 1 = i at this; omega
    have hpr0 : p ≠ r0 := by
      intro h; have := congrArg Fin.val h; change i - 1 = a - 1 at this; omega
    have hpr1 : p ≠ r1 := by
      intro h; have := congrArg Fin.val h; change i - 1 = a at this; omega
    have hpr2 : p ≠ r2 := by
      intro h; have := congrArg Fin.val h; change i - 1 = a + 1 at this; omega
    have hqr1 : q ≠ r1 := by
      intro h; have := congrArg Fin.val h; change i = a at this; omega
    have hr1r0 : r1 ≠ r0 := by
      intro h; have := congrArg Fin.val h; change a = a - 1 at this; omega
    have hr1r2 : r1 ≠ r2 := by
      intro h; have := congrArg Fin.val h; change a = a + 1 at this; omega
    have e1 : v1 p = 1 := by
      simp [v1, Pi.single_apply, hpq]
    have e2 : v2 p = 0 := by
      simp [v2, Pi.single_apply, hpr0, hpr1, hpr2]
    have e3 : v1 r1 = 0 := by
      simp [v1, Pi.single_apply, hpr1.symm, hqr1.symm]
    have e4 : v2 r1 = 1 := by
      simp [v2, Pi.single_apply, hr1r0, hr1r2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hp hr
    rw [e1, e2] at hp
    rw [e3, e4] at hr
    constructor <;> linarith
  let U : Submodule ℝ (Fin (n + 1) → ℝ) := Submodule.span ℝ (Set.range ![v1, v2])
  have hfin : Module.finrank ℝ U = 2 := by
    rw [finrank_span_eq_card hlin]; simp
  have hneg : ∀ x ∈ U, x ≠ 0 → x ⬝ᵥ (G *ᵥ x) < 0 := by
    intro x hx hx0
    obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hx0 ⊢
    set α := f 0
    set β := f 1
    have hQ : (α • v1 + β • v2) ⬝ᵥ (G *ᵥ (α • v1 + β • v2)) =
        α ^ 2 * (v1 ⬝ᵥ (G *ᵥ v1)) + β ^ 2 * (v2 ⬝ᵥ (G *ᵥ v2)) := by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, B12, B21]
      ring
    rw [hQ, B11, B22]
    have hαβ : α ≠ 0 ∨ β ≠ 0 := by
      by_contra h; push Not at h; apply hx0; rw [h.1, h.2]; simp
    rcases hαβ with h | h
    · have : 0 < α ^ 2 := by positivity
      nlinarith [sq_nonneg β]
    · have : 0 < β ^ 2 := by positivity
      nlinarith [sq_nonneg α]
  have := SylvesterNeg.finrank_neg_le G (pg_herm c n) U hneg
  rw [hfin] at this
  unfold negCount at hsig
  omega

/-- **`lem:isolate`, consequence.**  With one negative eigenvalue and all `c_k >= 1`, a weight
`c_i > 1` forces `n - 3 <= i <= 4`. -/
theorem isolate_range (hge : ∀ k, 1 ≤ k → k ≤ n → 1 ≤ c k) (hsig : negCount c n = 1)
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) (hci : 1 < c i) : n ≤ i + 3 ∧ i ≤ 4 := by
  constructor
  · by_contra h
    exact isolate hge hsig hi1 hin hci (a := i + 3) (by omega) (by omega) (Or.inr le_rfl)
  · by_contra h
    exact isolate hge hsig hi1 hin hci (a := 1) le_rfl (by omega) (Or.inl (by omega))

end KplusIsolate

#print axioms KplusIsolate.isolate
#print axioms KplusIsolate.isolate_range
