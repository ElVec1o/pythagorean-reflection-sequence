/-
PerronSym.lean
==============
`lem:perron` of `paper/journal/merged_novel_paper.tex`, the symmetric Perron--Frobenius step:

  `C` symmetric, entrywise `>= 0`, with connected support graph, scaled so its largest
  eigenvalue is `1`.  Then `I - C` is positive semidefinite of rank exactly `N - 1`.

Mathlib has no Perron--Frobenius theorem.  This proves the symmetric case directly, WITHOUT the
spectral theorem: "largest eigenvalue is 1" is taken in its equivalent form
  (H1) `x^T C x <= x^T x` for all `x`   (all eigenvalues `<= 1`), and
  (H2) `C v = v` for some `v != 0`      (`1` is an eigenvalue).
Proof: for an eigenvector `x`, `|x|` is again an eigenvector (Rayleigh equality case via PSD
`x^T A x = 0 <=> A x = 0`); the eigen-equation plus connectivity forces `|x| > 0`; subtracting a
multiple of `x` from a second eigenvector kills one coordinate hence all, so the eigenspace is a
line.  No `sorry`.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PerronSym

open Matrix

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise absolute value. -/
def absVec (x : n → ℝ) : n → ℝ := fun i => |x i|

theorem quad_le_quad_abs (C : Matrix n n ℝ) (hnn : ∀ i j, 0 ≤ C i j) (x : n → ℝ) :
    x ⬝ᵥ (C *ᵥ x) ≤ absVec x ⬝ᵥ (C *ᵥ absVec x) := by
  simp only [dotProduct, mulVec, absVec, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 : x i * x j ≤ |x i| * |x j| := by
    rw [← abs_mul]; exact le_abs_self _
  have := mul_le_mul_of_nonneg_left h1 (hnn i j)
  nlinarith [this]

theorem psd_of_quad (C : Matrix n n ℝ) (hC : C.IsSymm)
    (hle : ∀ x : n → ℝ, x ⬝ᵥ (C *ᵥ x) ≤ x ⬝ᵥ x) : (1 - C).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one, hC.eq]
  · have : x ⬝ᵥ ((1 - C) *ᵥ x) = x ⬝ᵥ x - x ⬝ᵥ (C *ᵥ x) := by
      rw [sub_mulVec, one_mulVec, dotProduct_sub]
    simp only [star_trivial, this]
    linarith [hle x]

/-- A nonzero eigenvector's absolute value is again an eigenvector. -/
theorem abs_eigen (C : Matrix n n ℝ) (hC : C.IsSymm) (hnn : ∀ i j, 0 ≤ C i j)
    (hle : ∀ x : n → ℝ, x ⬝ᵥ (C *ᵥ x) ≤ x ⬝ᵥ x) (x : n → ℝ) (hx : C *ᵥ x = x) :
    C *ᵥ absVec x = absVec x := by
  have hP := psd_of_quad C hC hle
  have hxx : x ⬝ᵥ (C *ᵥ x) = x ⬝ᵥ x := by rw [hx]
  have huu : absVec x ⬝ᵥ absVec x = x ⬝ᵥ x := by
    simp only [dotProduct, absVec]
    exact Finset.sum_congr rfl fun i _ => by rw [← sq, ← sq, sq_abs]
  have h1 := quad_le_quad_abs C hnn x
  have hz : (absVec x) ⬝ᵥ ((1 - C) *ᵥ absVec x) = 0 := by
    have e : (absVec x) ⬝ᵥ ((1 - C) *ᵥ absVec x) =
        absVec x ⬝ᵥ absVec x - absVec x ⬝ᵥ (C *ᵥ absVec x) := by
      rw [sub_mulVec, one_mulVec, dotProduct_sub]
    have := hP.dotProduct_mulVec_nonneg (absVec x)
    simp only [star_trivial] at this
    rw [e] at this ⊢
    linarith
  have := (hP.dotProduct_mulVec_zero_iff (absVec x)).mp (by simpa [star_trivial] using hz)
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at this
  exact this.symm

/-- Support-graph connectivity. -/
def Connected (C : Matrix n n ℝ) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun a b => 0 < C a b) i j

/-- A nonnegative eigenvector vanishing at one site vanishes everywhere. -/
theorem eigen_zero_propagate (C : Matrix n n ℝ) (hnn : ∀ i j, 0 ≤ C i j)
    (u : n → ℝ) (hu : ∀ i, 0 ≤ u i) (hCu : C *ᵥ u = u) {i j : n}
    (hij : Relation.ReflTransGen (fun a b => 0 < C a b) i j) (hi : u i = 0) : u j = 0 := by
  induction hij with
  | refl => exact hi
  | @tail b c _ hbc ih =>
    have hsum : ∑ k, C b k * u k = 0 := by
      have := congrFun hCu b
      simp only [mulVec, dotProduct] at this
      rw [this]; exact ih
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (hnn b k) (hu k))).mp hsum c (Finset.mem_univ _)
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hbc.ne'
    · exact h

/-- Every nonzero eigenvector for eigenvalue `1` has all coordinates nonzero. -/
theorem eigen_entries_ne_zero (C : Matrix n n ℝ) (hC : C.IsSymm) (hnn : ∀ i j, 0 ≤ C i j)
    (hconn : Connected C) (hle : ∀ x : n → ℝ, x ⬝ᵥ (C *ᵥ x) ≤ x ⬝ᵥ x)
    (x : n → ℝ) (hx : C *ᵥ x = x) (hne : x ≠ 0) : ∀ i, x i ≠ 0 := by
  have hCu := abs_eigen C hC hnn hle x hx
  obtain ⟨i1, hi1⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  intro i hxi
  have hui : absVec x i = 0 := by simp [absVec, hxi]
  have := eigen_zero_propagate C hnn (absVec x) (fun _ => abs_nonneg _) hCu (hconn i i1) hui
  exact hi1 (by simpa [absVec] using this)

/-- The eigenspace for `1` is a line. -/
theorem eigen_line (C : Matrix n n ℝ) (hC : C.IsSymm) (hnn : ∀ i j, 0 ≤ C i j)
    (hconn : Connected C) (hle : ∀ x : n → ℝ, x ⬝ᵥ (C *ᵥ x) ≤ x ⬝ᵥ x)
    (x : n → ℝ) (hx : C *ᵥ x = x) (hne : x ≠ 0) (y : n → ℝ) (hy : C *ᵥ y = y) :
    ∃ t : ℝ, y = t • x := by
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  refine ⟨y i0 / x i0, ?_⟩
  set z : n → ℝ := y - (y i0 / x i0) • x with hzdef
  have hz : C *ᵥ z = z := by
    rw [hzdef, mulVec_sub, mulVec_smul, hx, hy]
  have hz0 : z i0 = 0 := by
    simp [hzdef]; field_simp; ring
  by_cases hzz : z = 0
  · exact sub_eq_zero.mp hzz
  · exact absurd hz0 (eigen_entries_ne_zero C hC hnn hconn hle z hz hzz i0)

/-- **`lem:perron` (symmetric Perron--Frobenius step).**  If `C` is symmetric, entrywise
nonnegative, with connected support, and its largest eigenvalue is `1` (in the form H1, H2),
then `I - C` is positive semidefinite, the `1`-eigenspace is spanned by an entrywise POSITIVE
vector, and `rank (I - C) = N - 1`. -/
theorem perron_sym (C : Matrix n n ℝ) (hC : C.IsSymm) (hnn : ∀ i j, 0 ≤ C i j)
    (hconn : Connected C) (hle : ∀ x : n → ℝ, x ⬝ᵥ (C *ᵥ x) ≤ x ⬝ᵥ x)
    (hex : ∃ v : n → ℝ, v ≠ 0 ∧ C *ᵥ v = v) :
    (1 - C).PosSemidef ∧
    (∃ v : n → ℝ, (∀ i, 0 < v i) ∧ C *ᵥ v = v ∧ ∀ y, C *ᵥ y = y → ∃ t : ℝ, y = t • v) ∧
    (1 - C).rank + 1 = Fintype.card n := by
  obtain ⟨x, hxne, hx⟩ := hex
  have hu := abs_eigen C hC hnn hle x hx
  have hune : absVec x ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h'; push Not at h'; exact hxne (funext h')
    exact hi (abs_eq_zero.mp (congrFun h i))
  have hpos : ∀ i, 0 < absVec x i := fun i =>
    abs_pos.mpr (eigen_entries_ne_zero C hC hnn hconn hle x hx hxne i)
  have hline := fun y hy => eigen_line C hC hnn hconn hle (absVec x) hu hune y hy
  refine ⟨psd_of_quad C hC hle, ⟨absVec x, hpos, hu, hline⟩, ?_⟩
  have hker : LinearMap.ker (1 - C).mulVecLin = Submodule.span ℝ {absVec x} := by
    ext y
    simp only [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_span_singleton]
    constructor
    · intro h
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h
      obtain ⟨t, ht⟩ := hline y h.symm
      exact ⟨t, ht.symm⟩
    · rintro ⟨t, rfl⟩
      rw [sub_mulVec, one_mulVec, mulVec_smul, hu, sub_eq_zero]
  have h1 : Module.finrank ℝ (LinearMap.ker (1 - C).mulVecLin) = 1 := by
    rw [hker]; exact finrank_span_singleton hune
  have h2 := LinearMap.finrank_range_add_finrank_ker (1 - C).mulVecLin
  rw [h1, Module.finrank_fintype_fun_eq_card] at h2
  exact h2

/-! ### Scaling: any such `C` has a largest eigenvalue `lam > 0`, and `C / lam` meets H1, H2 -/

omit [DecidableEq n] in
theorem exists_pos_of_entry (C : Matrix n n ℝ) (hnn : ∀ i j, 0 ≤ C i j) {i j : n}
    (hij : 0 < C i j) : ∃ x : n → ℝ, 0 < x ⬝ᵥ x ∧ 0 < x ⬝ᵥ (C *ᵥ x) := by
  classical
  let x : n → ℝ := fun a => if a = i ∨ a = j then 1 else 0
  refine ⟨x, ?_, ?_⟩
  · have : x i * x i ≤ ∑ a, x a * x a :=
      Finset.single_le_sum (f := fun a => x a * x a) (fun a _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    have hxi : x i = 1 := by simp [x]
    rw [hxi] at this
    simp [dotProduct] at this ⊢; linarith
  · have hxi : x i = 1 := by simp [x]
    have hxj : x j = 1 := by simp [x]
    have h1 : x i * (C i j * x j) ≤ ∑ b, x i * (C i b * x b) :=
      Finset.single_le_sum (f := fun b => x i * (C i b * x b))
        (fun b _ => mul_nonneg (by simp only [x]; split_ifs <;> norm_num)
          (mul_nonneg (hnn _ _) (by simp only [x]; split_ifs <;> norm_num)))
        (Finset.mem_univ j)
    have h2 : ∑ b, x i * (C i b * x b) ≤ ∑ a, ∑ b, x a * (C a b * x b) :=
      Finset.single_le_sum (f := fun a => ∑ b, x a * (C a b * x b))
        (fun a _ => Finset.sum_nonneg fun b _ =>
          mul_nonneg (by simp only [x]; split_ifs <;> norm_num)
            (mul_nonneg (hnn _ _) (by simp only [x]; split_ifs <;> norm_num)))
        (Finset.mem_univ i)
    have h3 : 0 < x i * (C i j * x j) := by rw [hxi, hxj]; simpa using hij
    have : x ⬝ᵥ (C *ᵥ x) = ∑ a, ∑ b, x a * (C a b * x b) := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
    rw [this]; linarith

/-- The top eigenvalue of a symmetric matrix bounds its quadratic form. -/
theorem quad_le_top (C : Matrix n n ℝ) (hA : C.IsHermitian) (lam : ℝ)
    (hlam : ∀ j, hA.eigenvalues j ≤ lam) (x : n → ℝ) :
    x ⬝ᵥ (C *ᵥ x) ≤ lam * (x ⬝ᵥ x) := by
  have hD : (Matrix.diagonal fun j => lam - hA.eigenvalues j).PosSemidef :=
    PosSemidef.diagonal fun j => by simpa using hlam j
  have hU := hD.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix n n ℝ)
  have hspec := hA.spectral_theorem
  have hUU : (hA.eigenvectorUnitary : Matrix n n ℝ) * (star (hA.eigenvectorUnitary : Matrix n n ℝ))
      = 1 := by
    have := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    simpa only [Unitary.coe_star] using this
  have hCdec : C = (hA.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
    conv_lhs => rw [hspec]
    simp [Unitary.conjStarAlgAut_apply]
  have hd : (Matrix.diagonal fun j => lam - hA.eigenvalues j) =
      lam • (1 : Matrix n n ℝ) - Matrix.diagonal hA.eigenvalues := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  have hrepr : (lam • (1 : Matrix n n ℝ) - C) =
      (hA.eigenvectorUnitary : Matrix n n ℝ) * (Matrix.diagonal fun j => lam - hA.eigenvalues j)
        * (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ := by
    rw [hd]
    have e : (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ = star (hA.eigenvectorUnitary : Matrix n n ℝ) :=
      rfl
    rw [e, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hUU, ← hCdec]
  have hpsd : (lam • (1 : Matrix n n ℝ) - C).PosSemidef := by rw [hrepr]; exact hU
  have := hpsd.dotProduct_mulVec_nonneg x
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at this
  linarith

/-- **`lem:perron`, scaled form.** `C` symmetric, entrywise `>= 0`, connected support, not
identically zero.  Then there is a largest eigenvalue `lam > 0` of `C` and, with
`C' = C / lam`, the matrix `I - C'` is PSD, the `1`-eigenspace of `C'` is spanned by an entrywise
positive vector, and `rank (I - C') = N - 1`. -/
theorem perron_scaled (C : Matrix n n ℝ) (hC : C.IsSymm) (hnn : ∀ i j, 0 ≤ C i j)
    (hconn : Connected C) (hedge : ∃ i j, 0 < C i j) :
    ∃ (hA : C.IsHermitian) (i0 : n), 0 < hA.eigenvalues i0 ∧
      (∀ j, hA.eigenvalues j ≤ hA.eigenvalues i0) ∧
      (1 - (hA.eigenvalues i0)⁻¹ • C).PosSemidef ∧
      (∃ v : n → ℝ, (∀ i, 0 < v i) ∧ ((hA.eigenvalues i0)⁻¹ • C) *ᵥ v = v ∧
        ∀ y, ((hA.eigenvalues i0)⁻¹ • C) *ᵥ y = y → ∃ t : ℝ, y = t • v) ∧
      (1 - (hA.eigenvalues i0)⁻¹ • C).rank + 1 = Fintype.card n := by
  have hA : C.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hC
  obtain ⟨i, j, hij⟩ := hedge
  haveI : Nonempty n := ⟨i⟩
  obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues
    (Finset.univ_nonempty)
  have hmax' : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues i0 := fun j => hmax j (Finset.mem_univ _)
  set lam := hA.eigenvalues i0 with hlamdef
  obtain ⟨x, hx1, hx2⟩ := exists_pos_of_entry C hnn hij
  have hlampos : 0 < lam := by
    have := quad_le_top C hA lam hmax' x
    by_contra h
    push Not at h
    nlinarith
  refine ⟨hA, i0, hlampos, hmax', ?_⟩
  have hC' : (lam⁻¹ • C).IsSymm := by
    simpa using hC.smul lam⁻¹
  have hnn' : ∀ a b, 0 ≤ (lam⁻¹ • C) a b := fun a b => by
    simp only [smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hlampos.le) (hnn a b)
  have hconn' : Connected (lam⁻¹ • C) := by
    intro a b
    refine (hconn a b).mono ?_
    intro p q hpq
    simp only [smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hlampos) hpq
  have hle : ∀ y : n → ℝ, y ⬝ᵥ ((lam⁻¹ • C) *ᵥ y) ≤ y ⬝ᵥ y := by
    intro y
    have := quad_le_top C hA lam hmax' y
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    calc lam⁻¹ * (y ⬝ᵥ (C *ᵥ y)) ≤ lam⁻¹ * (lam * (y ⬝ᵥ y)) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hlampos.le)
      _ = y ⬝ᵥ y := by field_simp
  have hex : ∃ v : n → ℝ, v ≠ 0 ∧ (lam⁻¹ • C) *ᵥ v = v := by
    refine ⟨⇑(hA.eigenvectorBasis i0), ?_, ?_⟩
    · intro h
      apply (hA.eigenvectorBasis.orthonormal.ne_zero i0)
      ext k; exact congrFun h k
    · rw [smul_mulVec, hA.mulVec_eigenvectorBasis i0, smul_smul, inv_mul_cancel₀ hlampos.ne',
        one_smul]
  obtain ⟨h1, h2, h3⟩ := perron_sym (lam⁻¹ • C) hC' hnn' hconn' hle hex
  exact ⟨h1, h2, h3⟩

end PerronSym

#print axioms PerronSym.perron_sym
#print axioms PerronSym.perron_scaled
