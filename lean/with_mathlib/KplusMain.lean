/-
KplusMain.lean
==============
`lem:Kplus` (i) and the membership half of (ii) of `merged_novel_paper.tex`, assembled.

For `c ∈ R_{>0}^n` (`n >= 1`), TFAE:
  (a) `c ∈ K^+`  : `G(c)` is positive semidefinite of rank `n`;
  (b) `D_1..D_n > 0` and `D_{n+1} = 0`;
  (c) the Perron root of `C(c) = I - G(c)` is `1`.
And `c(a) ∈ K^+` for every `a ∈ R_{>0}^n`, `n >= 2` (the forward formula).

(a)<=>(c): `KplusLocus.perronRoot_iff_inK` (from `PerronSym.perron_sym`).
(a)=>(b): the Perron kernel vector is entrywise positive, so a vector supported on the first
          `m+1 <= n` coordinates is never in the kernel; leading blocks are PSD and nonsingular.
(b)=>(a): `KplusLDL.psd_of_D` + Perron.   No sorry.
-/
import KplusLocus
import KplusLDL
import KplusForward

namespace KplusMain

open Matrix KplusPath KplusLocus PerronSym

/-- Zero-padding: the quadratic form of a submatrix is the quadratic form of the padded vector. -/
theorem pad_dot {N M : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (f : Fin M → Fin N)
    (hf : Function.Injective f) (y : Fin M → ℝ) :
    (Function.extend f y (0 : Fin N → ℝ)) ⬝ᵥ (B *ᵥ Function.extend f y (0 : Fin N → ℝ)) =
      y ⬝ᵥ ((B.submatrix f f) *ᵥ y) := by
  have hext : ∀ j, Function.extend f y (0 : Fin N → ℝ) (f j) = y j := fun j => hf.extend_apply y (0 : Fin N → ℝ) j
  have hout : ∀ i, i ∉ Set.range f → Function.extend f y (0 : Fin N → ℝ) i = 0 := by
    intro i hi
    have : ¬∃ a, f a = i := fun ⟨a, ha⟩ => hi ⟨a, ha⟩
    simpa using Function.extend_apply' y (0 : Fin N → ℝ) i this
  simp only [dotProduct, mulVec, submatrix_apply]
  symm
  refine Fintype.sum_of_injective f hf _ _ ?_ ?_
  · intro i hi
    rw [hout i hi]; simp
  · intro j
    rw [hext j]
    congr 1
    refine Fintype.sum_of_injective f hf _ _ ?_ ?_
    · intro i hi
      rw [hout i hi]; simp
    · intro k; rw [hext k]

variable {c : ℕ → ℝ} {n : ℕ}

/-- `(a) => (b)`, leading minors: `det G_m > 0` for `m + 1 <= n`. -/
theorem leading_det_pos (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i) (hK : InK c n) (m : ℕ)
    (hm : m + 1 ≤ n) : 0 < (pg c m).det := by
  have hP := hK.1
  have hRoot := (perronRoot_iff_inK hc).mpr hK
  obtain ⟨-, ⟨v, hvpos, hCv, hline⟩, -⟩ := perron_sym (Cm c n) (Cm_symm c n)
    (Cm_nonneg hc) (Cm_connected hc) hRoot.1 hRoot.2
  have hle : m + 1 ≤ n + 1 := by omega
  let f : Fin (m + 1) → Fin (n + 1) := Fin.castLE hle
  have hf : Function.Injective f := Fin.castLE_injective hle
  have hsub : (pg c n).submatrix f f = pg c m := by
    ext i j; simp [pg, f]
  have hPsub : (pg c m).PosSemidef := by
    rw [← hsub]; exact hP.submatrix f
  have hnn := hPsub.det_nonneg
  refine lt_of_le_of_ne hnn (fun h0 => ?_)
  obtain ⟨y, hy, hy0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0.symm
  set yt : Fin (n + 1) → ℝ := Function.extend f y (0 : Fin (n + 1) → ℝ) with hyt
  have hq : yt ⬝ᵥ (pg c n *ᵥ yt) = 0 := by
    rw [hyt, pad_dot (pg c n) f hf y, hsub, hy0]; simp
  have hker : pg c n *ᵥ yt = 0 := by
    have := (hP.dotProduct_mulVec_zero_iff yt).mp (by simpa [star_trivial] using hq)
    exact this
  have hCy : Cm c n *ᵥ yt = yt := by
    have : Cm c n *ᵥ yt = yt - pg c n *ᵥ yt := by simp [Cm, sub_mulVec]
    rw [this, hker, sub_zero]
  obtain ⟨t, ht⟩ := hline yt hCy
  have hlast : yt (Fin.last n) = 0 := by
    have hn : ¬∃ a, f a = Fin.last n := by
      rintro ⟨a, ha⟩
      have := congrArg Fin.val ha
      simp only [f, Fin.val_castLE, Fin.val_last] at this
      have := a.isLt; omega
    simpa [hyt] using Function.extend_apply' y (0 : Fin (n + 1) → ℝ) _ hn
  have ht0 : t = 0 := by
    have := congrFun ht (Fin.last n)
    rw [hlast] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · exact absurd h (hvpos _).ne'
  apply hy
  funext j
  have := hf.extend_apply y (0 : Fin (n + 1) → ℝ) j
  rw [← hyt, ht, ht0] at this
  simpa using this.symm

/-- `(a) => (b)`. -/
theorem D_of_inK (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i) (hK : InK c n) :
    (∀ k, 1 ≤ k → k ≤ n → 0 < D c k) ∧ D c (n + 1) = 0 := by
  refine ⟨fun k hk1 hkn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [← (pg_det_eq_D c m).1]
    exact leading_det_pos hc hK m hkn
  · rw [← (pg_det_eq_D c n).1]
    obtain ⟨v, hv, hv0⟩ := exists_ker_of_rank_lt (pg c n) hK.2
    exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hv0⟩

/-- `(b) => (a)`. -/
theorem inK_of_D (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i)
    (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < D c k) (hlast : D c (n + 1) = 0) : InK c n := by
  have hP := KplusLDL.psd_of_D c n hpos hlast
  have hdet : (pg c n).det = 0 := by rw [(pg_det_eq_D c n).1]; exact hlast
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply (perronRoot_iff_inK hc).mp
  refine ⟨fun x => ?_, ⟨v, hv, ?_⟩⟩
  · have := hP.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at this
    have e2 : x ⬝ᵥ (pg c n *ᵥ x) = x ⬝ᵥ x - x ⬝ᵥ (Cm c n *ᵥ x) := by
      have e : 1 - Cm c n = pg c n := by simp [Cm]
      rw [← e, sub_mulVec, one_mulVec, dotProduct_sub]
    linarith
  · have : Cm c n *ᵥ v = v - pg c n *ᵥ v := by simp [Cm, sub_mulVec]
    rw [this, hv0, sub_zero]

/-- **`lem:Kplus` (i).**  For positive `c`: `K^+` membership, the `D`-conditions, and
"Perron root of `C(c)` equals `1`" are equivalent. -/
theorem kplus_equiv (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i) :
    (InK c n ↔ ((∀ k, 1 ≤ k → k ≤ n → 0 < D c k) ∧ D c (n + 1) = 0)) ∧
    (InK c n ↔ PerronRoot1 c n) :=
  ⟨⟨D_of_inK hc, fun h => inK_of_D hc h.1 h.2⟩, (perronRoot_iff_inK hc).symm⟩

/-- **`lem:Kplus` (ii), membership.**  For legs `a_1..a_n > 0` (`n >= 2`), `c(a) ∈ K^+`. -/
theorem cOf_mem_Kplus (hn : 2 ≤ n) (a : ℕ → ℝ) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < KplusForward.cOf n a i) ∧ InK (KplusForward.cOf n a) n := by
  have hcpos : ∀ i, 1 ≤ i → i ≤ n → 0 < KplusForward.cOf n a i := by
    intro i hi1 hin
    unfold KplusForward.cOf
    have a1 := ha i hi1 hin
    by_cases h1 : i = 1
    · subst h1; simp only [if_true]
      have := ha 2 (by omega) hn
      positivity
    · by_cases hn' : i = n
      · subst hn'; simp only [if_neg h1, if_true]
        have := ha (i - 1) (by omega) (by omega)
        positivity
      · simp only [if_neg h1, if_neg hn']
        have := ha (i - 1) (by omega) (by omega)
        have := ha (i + 1) (by omega) (by omega)
        positivity
  obtain ⟨-, hpos, hlast⟩ := KplusForward.forward_formula n hn a ha
  exact ⟨hcpos, inK_of_D hcpos hpos hlast⟩

end KplusMain

#print axioms KplusMain.kplus_equiv
#print axioms KplusMain.cOf_mem_Kplus
