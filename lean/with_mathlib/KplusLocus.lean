/-
KplusLocus.lean
===============
`lem:Kplus` (i) of `merged_novel_paper.tex`: for `c ∈ R_{>0}^n`, TFAE
  (a) `c ∈ K^+`, i.e. `G(c)` is positive semidefinite of rank `n`;
  (b) `D_1,...,D_n > 0` and `D_{n+1} = 0`;
  (c) the Perron root of `C(c) = I - G(c)` equals `1`
      (in the form: all eigenvalues `<= 1`, and `1` is an eigenvalue).

(a)<=>(c) is `PerronSym.perron_sym` plus rank-nullity.  (a)=>(b) uses the entrywise-positive
kernel vector from Perron--Frobenius.  (b)=>(a) uses an explicit LDL^T sum-of-squares identity
for the tridiagonal form (no Sylvester criterion, no interlacing needed).  No sorry.
-/
import KplusPath
import PerronSym

namespace KplusLocus

open Matrix KplusPath PerronSym

variable (c : ℕ → ℝ) (n : ℕ)

/-- `C(c) = I - G(c)`: weighted adjacency matrix of the path. -/
def Cm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := 1 - pg c n

theorem pg_symm : (pg c n).IsSymm := by
  ext i j
  simp only [transpose_apply, pg]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all

theorem Cm_symm : (Cm c n).IsSymm := by
  have := pg_symm c n
  unfold Cm
  ext i j
  have h := congrFun (congrFun this j) i
  simp only [transpose_apply, sub_apply, one_apply] at h ⊢
  rw [h]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem Cm_apply (i j : Fin (n + 1)) :
    Cm c n i j =
      if (i : ℕ) = j then 0 else if (i : ℕ) + 1 = j then c j
      else if (j : ℕ) + 1 = i then c i else 0 := by
  simp only [Cm, sub_apply, one_apply, pg]
  by_cases h : (i : ℕ) = j
  · have : i = j := Fin.ext h
    simp [this]
  · have : i ≠ j := fun e => h (by rw [e])
    simp only [this, h, if_false]
    split_ifs <;> simp

variable {c n}

theorem Cm_nonneg (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i) (i j : Fin (n + 1)) :
    0 ≤ Cm c n i j := by
  rw [Cm_apply]
  split_ifs with h1 h2 h3
  · exact le_rfl
  · exact (hc j (by omega) (by omega)).le
  · exact (hc i (by omega) (by omega)).le
  · exact le_rfl

theorem Cm_connected (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i) : Connected (Cm c n) := by
  have step : ∀ k (hk : k + 1 < n + 1),
      0 < Cm c n ⟨k, by omega⟩ ⟨k + 1, hk⟩ := by
    intro k hk
    have : Cm c n ⟨k, by omega⟩ ⟨k + 1, hk⟩ = c (k + 1) := by
      rw [Cm_apply]; simp
    rw [this]
    exact hc (k + 1) (by omega) (by omega)
  have from0 : ∀ k (hk : k < n + 1),
      Relation.ReflTransGen (fun a b => 0 < Cm c n a b) ⟨0, by omega⟩ ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      exact (ih (by omega)).tail (step k hk)
  have symm : ∀ a b : Fin (n + 1), 0 < Cm c n a b → 0 < Cm c n b a := by
    intro a b h
    have := Cm_symm c n
    have e := congrFun (congrFun this a) b
    simp only [transpose_apply] at e
    rw [e]; exact h
  intro i j
  have hi := from0 i.val i.isLt
  have hj := from0 j.val j.isLt
  have hi' : Relation.ReflTransGen (fun a b => 0 < Cm c n a b) i ⟨0, by omega⟩ := by
    have := Relation.ReflTransGen.symmetric (fun a b h => symm a b h) hi
    simpa using this
  exact hi'.trans (by simpa using hj)

/-! ### (a) <=> (c): `K^+` is the Perron-root-one condition -/

/-- "The Perron root of `C(c)` is `1`": all eigenvalues `<= 1` and `1` is an eigenvalue. -/
def PerronRoot1 (c : ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ x : Fin (n + 1) → ℝ, x ⬝ᵥ (Cm c n *ᵥ x) ≤ x ⬝ᵥ x) ∧
    ∃ v : Fin (n + 1) → ℝ, v ≠ 0 ∧ Cm c n *ᵥ v = v

/-- Membership in `K`: `G(c)` is positive semidefinite of rank `n` (= `N - 1`, `N = n + 1`). -/
def InK (c : ℕ → ℝ) (n : ℕ) : Prop := (pg c n).PosSemidef ∧ (pg c n).rank = n

theorem exists_ker_of_rank_lt (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (h : M.rank = n) :
    ∃ v : Fin (n + 1) → ℝ, v ≠ 0 ∧ M *ᵥ v = 0 := by
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
  have hr : Module.finrank ℝ (LinearMap.range M.mulVecLin) = n := h
  have hk : Module.finrank ℝ (LinearMap.ker M.mulVecLin) = 1 := by omega
  have hne : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    intro hb; rw [hb] at hk; simp at hk
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  exact ⟨v, hv0, by simpa using hv⟩

theorem perronRoot_iff_inK (hc : ∀ i, 1 ≤ i → i ≤ n → 0 < c i) :
    PerronRoot1 c n ↔ InK c n := by
  have e : 1 - Cm c n = pg c n := by simp [Cm]
  constructor
  · rintro ⟨hle, hex⟩
    obtain ⟨h1, -, h3⟩ := perron_sym (Cm c n) (Cm_symm c n) (Cm_nonneg hc)
      (Cm_connected hc) hle hex
    rw [e] at h1 h3
    refine ⟨h1, ?_⟩
    simp only [Fintype.card_fin] at h3
    omega
  · rintro ⟨hP, hrk⟩
    refine ⟨fun x => ?_, ?_⟩
    · have := hP.dotProduct_mulVec_nonneg x
      simp only [star_trivial] at this
      have e2 : x ⬝ᵥ (pg c n *ᵥ x) = x ⬝ᵥ x - x ⬝ᵥ (Cm c n *ᵥ x) := by
        rw [← e, sub_mulVec, one_mulVec, dotProduct_sub]
      linarith
    · obtain ⟨v, hv, hv0⟩ := exists_ker_of_rank_lt (pg c n) hrk
      refine ⟨v, hv, ?_⟩
      have : Cm c n *ᵥ v = v - pg c n *ᵥ v := by
        simp [Cm, sub_mulVec]
      rw [this, hv0, sub_zero]

end KplusLocus

#print axioms KplusLocus.perronRoot_iff_inK
