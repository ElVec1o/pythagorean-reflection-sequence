/-
  PairingMatrix.lean
  ==================
  The passage from Definition `def:pairing` to the structure `Plan` of `SiteCost.lean`.

  Definition `def:pairing` of `paper/journal/paper2.tex` takes a pairing at a site to be a
  *bijection* between the arrivals and the departures, each matched pair paying `0`, `1` or `2`.
  `SiteCost.lean` and `MarkedSite.lean` work with the *multiplicity matrix* of such a bijection,
  the structure `Plan`.  This file proves that the two carry the same minimum, so that
  Lemma `lem:transport` and Corollary `cor:localcost` are statements about bijections:

  * `planOfBij`, `planOfBij_cost`  every bijection has a multiplicity matrix, which is a `Plan`
                                   of the same cost;
  * `bijOfMatrix`, `bijOfMatrix_cost`
                                   conversely every non-negative integer matrix with the class
                                   counts as row and column sums is the multiplicity matrix of
                                   a bijection, of the corresponding cost;
  * `bij_min`                      hence the minimum over bijections is the `siteValue` of
                                   Lemma `lem:transport`;
  * `MarkedSite.site_cost_bij`     Corollary `cor:localcost`, stated over bijections.

  No `sorry`.
-/

import MarkedSite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace SiteCost

/-! ## Pairings at a site as bijections -/

/-- The four classes of Definition `def:pairing`, numbered as the rows and columns of `Plan`:
`0 = (L,+)`, `1 = (L,-)`, `2 = (R,+)`, `3 = (R,-)`. -/
abbrev Cls := Fin 4

/-- The side of a class: `true` on the left. -/
def side (I : Cls) : Bool := I.val < 2

/-- The cost of a matched pair of Definition `def:pairing`: `0` on the same side with equal
signs, `2` on the same side with opposite signs, `1` on opposite sides. -/
def pairCost (I J : Cls) : ℕ := if side I = side J then (if I = J then 0 else 2) else 1

/-- The cost table, written out. -/
theorem pairCost_eq (I J : Cls) :
    pairCost I J = ![![0, 2, 1, 1], ![2, 0, 1, 1], ![1, 1, 0, 2], ![1, 1, 2, 0]] I J := by
  revert I J; decide

variable {A D : Type*} [Fintype A] [Fintype D]

/-- The number of arrivals (or departures) of class `I`. -/
def cnt (c : A → Cls) (I : Cls) : ℕ := (Finset.univ.filter fun a => c a = I).card

/-- The cost of a pairing at a site in the sense of Definition `def:pairing`: a bijection
between the arrivals and the departures, each matched pair paying `pairCost`. -/
def bijCost (ca : A → Cls) (cd : D → Cls) (σ : A ≃ D) : ℕ :=
  ∑ a : A, pairCost (ca a) (cd (σ a))

/-- The multiplicity matrix of a bijection: the number of class-`I` arrivals matched to a
class-`J` departure. -/
def mult (ca : A → Cls) (cd : D → Cls) (σ : A ≃ D) (I J : Cls) : ℕ :=
  (Finset.univ.filter fun a => ca a = I ∧ cd (σ a) = J).card

omit [Fintype D] in
theorem sum_mult_row (ca : A → Cls) (cd : D → Cls) (σ : A ≃ D) (I : Cls) :
    ∑ J, mult ca cd σ I J = cnt ca I := by
  simp only [mult, cnt, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ca a = I <;> simp [h]

theorem sum_mult_col (ca : A → Cls) (cd : D → Cls) (σ : A ≃ D) (J : Cls) :
    ∑ I, mult ca cd σ I J = cnt cd J := by
  simp only [mult, cnt, Finset.card_filter]
  rw [Finset.sum_comm, ← Equiv.sum_comp σ fun d => ite (cd d = J) 1 0]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : cd (σ a) = J <;> simp [h]

omit [Fintype D] in
theorem bijCost_eq_prod (ca : A → Cls) (cd : D → Cls) (σ : A ≃ D) :
    bijCost ca cd σ = ∑ p : Cls × Cls, mult ca cd σ p.1 p.2 * pairCost p.1 p.2 := by
  simp only [bijCost, mult, Finset.card_filter, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (ca a, cd (σ a))]
  · simp
  · rintro ⟨I, J⟩ _ hne
    have hno : ¬(ca a = I ∧ cd (σ a) = J) := by
      rintro ⟨rfl, rfl⟩; exact hne rfl
    simp [hno]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype D] in
theorem bijCost_eq_mult (ca : A → Cls) (cd : D → Cls) (σ : A ≃ D) :
    bijCost ca cd σ = ∑ I, ∑ J, mult ca cd σ I J * pairCost I J := by
  rw [bijCost_eq_prod]
  exact Fintype.sum_prod_type' fun I J => mult ca cd σ I J * pairCost I J

/-! ## From a bijection to a `Plan` -/

/-- The multiplicity matrix of a bijection is a `Plan`: the row sums are the arrival counts and
the column sums the departure counts. -/
def planOfBij (ca : A → Cls) (cd : D → Cls) (σ : A ≃ D) :
    Plan (cnt ca 0) (cnt ca 1) (cnt ca 2) (cnt ca 3)
      (cnt cd 0) (cnt cd 1) (cnt cd 2) (cnt cd 3) where
  x00 := mult ca cd σ 0 0
  x01 := mult ca cd σ 0 1
  x02 := mult ca cd σ 0 2
  x03 := mult ca cd σ 0 3
  x10 := mult ca cd σ 1 0
  x11 := mult ca cd σ 1 1
  x12 := mult ca cd σ 1 2
  x13 := mult ca cd σ 1 3
  x20 := mult ca cd σ 2 0
  x21 := mult ca cd σ 2 1
  x22 := mult ca cd σ 2 2
  x23 := mult ca cd σ 2 3
  x30 := mult ca cd σ 3 0
  x31 := mult ca cd σ 3 1
  x32 := mult ca cd σ 3 2
  x33 := mult ca cd σ 3 3
  row0 := by have := sum_mult_row ca cd σ 0; rw [Fin.sum_univ_four] at this; omega
  row1 := by have := sum_mult_row ca cd σ 1; rw [Fin.sum_univ_four] at this; omega
  row2 := by have := sum_mult_row ca cd σ 2; rw [Fin.sum_univ_four] at this; omega
  row3 := by have := sum_mult_row ca cd σ 3; rw [Fin.sum_univ_four] at this; omega
  col0 := by have := sum_mult_col ca cd σ 0; rw [Fin.sum_univ_four] at this; omega
  col1 := by have := sum_mult_col ca cd σ 1; rw [Fin.sum_univ_four] at this; omega
  col2 := by have := sum_mult_col ca cd σ 2; rw [Fin.sum_univ_four] at this; omega
  col3 := by have := sum_mult_col ca cd σ 3; rw [Fin.sum_univ_four] at this; omega

theorem planOfBij_cost (ca : A → Cls) (cd : D → Cls) (σ : A ≃ D) :
    (planOfBij ca cd σ).cost = bijCost ca cd σ := by
  rw [bijCost_eq_mult, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four,
    Fin.sum_univ_four, Fin.sum_univ_four]
  show 2 * (mult ca cd σ 0 1 + mult ca cd σ 1 0) + 2 * (mult ca cd σ 2 3 + mult ca cd σ 3 2)
      + (mult ca cd σ 0 2 + mult ca cd σ 0 3 + mult ca cd σ 1 2 + mult ca cd σ 1 3)
      + (mult ca cd σ 2 0 + mult ca cd σ 2 1 + mult ca cd σ 3 0 + mult ca cd σ 3 1)
    = mult ca cd σ 0 0 * 0 + mult ca cd σ 0 1 * 2 + mult ca cd σ 0 2 * 1 + mult ca cd σ 0 3 * 1
      + (mult ca cd σ 1 0 * 2 + mult ca cd σ 1 1 * 0 + mult ca cd σ 1 2 * 1
        + mult ca cd σ 1 3 * 1)
      + (mult ca cd σ 2 0 * 1 + mult ca cd σ 2 1 * 1 + mult ca cd σ 2 2 * 0
        + mult ca cd σ 2 3 * 2)
      + (mult ca cd σ 3 0 * 1 + mult ca cd σ 3 1 * 1 + mult ca cd σ 3 2 * 2
        + mult ca cd σ 3 3 * 0)
  omega

/-! ## From a matrix to a bijection -/

/-- The canonical set of matched pairs of a multiplicity matrix, tagged by the arrival class
first. -/
abbrev Blk (x : Cls → Cls → ℕ) : Type := Σ I : Cls, Σ J : Cls, Fin (x I J)

/-- The same matched pairs, tagged by the departure class first. -/
abbrev BlkT (x : Cls → Cls → ℕ) : Type := Σ J : Cls, Σ I : Cls, Fin (x I J)

/-- Transposing the tag. -/
def blkSwap (x : Cls → Cls → ℕ) : Blk x ≃ BlkT x where
  toFun b := ⟨b.2.1, b.1, b.2.2⟩
  invFun c := ⟨c.2.1, c.1, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_blk_fibre (x : Cls → Cls → ℕ) (I : Cls) :
    Fintype.card {b : Blk x // b.1 = I} = ∑ J, x I J := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sigma,
    Finset.sum_eq_single I]
  · simp
  · intro i _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem card_blkT_fibre (x : Cls → Cls → ℕ) (J : Cls) :
    Fintype.card {c : BlkT x // c.1 = J} = ∑ I, x I J := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sigma,
    Finset.sum_eq_single J]
  · simp
  · intro i _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem card_cnt (c : A → Cls) (I : Cls) : Fintype.card {a : A // c a = I} = cnt c I := by
  rw [Fintype.card_subtype]; rfl

/-- A class-preserving identification of the canonical matched pairs with the arrivals. -/
noncomputable def blkEquivArr (x : Cls → Cls → ℕ) (ca : A → Cls)
    (h : ∀ I, ∑ J, x I J = cnt ca I) : Blk x ≃ A :=
  Equiv.ofFiberEquiv (f := fun b : Blk x => b.1) (g := ca)
    fun I => Fintype.equivOfCardEq (by rw [card_blk_fibre, card_cnt, h])

theorem blkEquivArr_cls (x : Cls → Cls → ℕ) (ca : A → Cls) (h : ∀ I, ∑ J, x I J = cnt ca I)
    (b : Blk x) : ca (blkEquivArr x ca h b) = b.1 :=
  Equiv.ofFiberEquiv_map _ b

/-- A class-preserving identification of the canonical matched pairs with the departures. -/
noncomputable def blkTEquivDep (x : Cls → Cls → ℕ) (cd : D → Cls)
    (h : ∀ J, ∑ I, x I J = cnt cd J) : BlkT x ≃ D :=
  Equiv.ofFiberEquiv (f := fun c : BlkT x => c.1) (g := cd)
    fun J => Fintype.equivOfCardEq (by rw [card_blkT_fibre, card_cnt, h])

theorem blkTEquivDep_cls (x : Cls → Cls → ℕ) (cd : D → Cls) (h : ∀ J, ∑ I, x I J = cnt cd J)
    (c : BlkT x) : cd (blkTEquivDep x cd h c) = c.1 :=
  Equiv.ofFiberEquiv_map _ c

/-- The bijection realising a multiplicity matrix. -/
noncomputable def bijOfMatrix (x : Cls → Cls → ℕ) (ca : A → Cls) (cd : D → Cls)
    (hr : ∀ I, ∑ J, x I J = cnt ca I) (hc : ∀ J, ∑ I, x I J = cnt cd J) : A ≃ D :=
  (blkEquivArr x ca hr).symm.trans ((blkSwap x).trans (blkTEquivDep x cd hc))

theorem bijOfMatrix_cost (x : Cls → Cls → ℕ) (ca : A → Cls) (cd : D → Cls)
    (hr : ∀ I, ∑ J, x I J = cnt ca I) (hc : ∀ J, ∑ I, x I J = cnt cd J) :
    bijCost ca cd (bijOfMatrix x ca cd hr hc) = ∑ I, ∑ J, x I J * pairCost I J := by
  simp only [bijCost]
  rw [← Equiv.sum_comp (blkEquivArr x ca hr)
    fun a => pairCost (ca a) (cd (bijOfMatrix x ca cd hr hc a))]
  have key : ∀ b : Blk x,
      pairCost (ca (blkEquivArr x ca hr b))
        (cd (bijOfMatrix x ca cd hr hc (blkEquivArr x ca hr b))) = pairCost b.1 b.2.1 := by
    intro b
    rw [blkEquivArr_cls x ca hr b]
    congr 1
    simp only [bijOfMatrix, Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [blkTEquivDep_cls x cd hc]
    rfl
  rw [Finset.sum_congr rfl fun b _ => key b]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp

/-! ## The minimum over bijections -/

/-- The matrix of a `Plan`. -/
def matOf {Ap Am Bp Bm Cp Cm Dp Dm : ℕ} (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) : Cls → Cls → ℕ :=
  ![![p.x00, p.x01, p.x02, p.x03], ![p.x10, p.x11, p.x12, p.x13],
    ![p.x20, p.x21, p.x22, p.x23], ![p.x30, p.x31, p.x32, p.x33]]

theorem matOf_row {Ap Am Bp Bm Cp Cm Dp Dm : ℕ} (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) (I : Cls) :
    ∑ J, matOf p I J = ![Ap, Am, Bp, Bm] I := by
  have h0 := p.row0; have h1 := p.row1; have h2 := p.row2; have h3 := p.row3
  fin_cases I <;> rw [Fin.sum_univ_four] <;> assumption

theorem matOf_col {Ap Am Bp Bm Cp Cm Dp Dm : ℕ} (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) (J : Cls) :
    ∑ I, matOf p I J = ![Cp, Cm, Dp, Dm] J := by
  have h0 := p.col0; have h1 := p.col1; have h2 := p.col2; have h3 := p.col3
  fin_cases J <;> rw [Fin.sum_univ_four] <;> assumption

theorem matOf_cost {Ap Am Bp Bm Cp Cm Dp Dm : ℕ} (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) :
    ∑ I, ∑ J, matOf p I J * pairCost I J = p.cost := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four,
    Fin.sum_univ_four]
  show p.x00 * 0 + p.x01 * 2 + p.x02 * 1 + p.x03 * 1
      + (p.x10 * 2 + p.x11 * 0 + p.x12 * 1 + p.x13 * 1)
      + (p.x20 * 1 + p.x21 * 1 + p.x22 * 0 + p.x23 * 2)
      + (p.x30 * 1 + p.x31 * 1 + p.x32 * 2 + p.x33 * 0) = p.cost
  simp only [Plan.cost]
  omega

/-- **Lemma `lem:transport`, over bijections.**  The minimum cost of a bijection between the
arrivals and the departures at a site is `max(|alpha|,|beta|,|Phi|)`. -/
theorem bij_min (ca : A → Cls) (cd : D → Cls)
    (hbal : cnt ca 0 + cnt ca 1 + cnt ca 2 + cnt ca 3
      = cnt cd 0 + cnt cd 1 + cnt cd 2 + cnt cd 3) :
    IsLeast {n : ℕ | ∃ σ : A ≃ D, bijCost ca cd σ = n}
      (siteValue (cnt ca 0) (cnt ca 1) (cnt ca 2) (cnt ca 3)
        (cnt cd 0) (cnt cd 1) (cnt cd 2) (cnt cd 3)) := by
  obtain ⟨p, hp, -⟩ := exists_plan_cost_eq (cnt ca 0) (cnt ca 1) (cnt ca 2) (cnt ca 3)
    (cnt cd 0) (cnt cd 1) (cnt cd 2) (cnt cd 3) hbal
  have hr : ∀ I, ∑ J, matOf p I J = cnt ca I := by
    intro I; rw [matOf_row]; fin_cases I <;> rfl
  have hc : ∀ J, ∑ I, matOf p I J = cnt cd J := by
    intro J; rw [matOf_col]; fin_cases J <;> rfl
  refine ⟨⟨bijOfMatrix (matOf p) ca cd hr hc, ?_⟩, ?_⟩
  · rw [bijOfMatrix_cost, matOf_cost, hp]
  · rintro n ⟨σ, rfl⟩
    have h := cost_lower_bound (planOfBij ca cd σ)
    rwa [planOfBij_cost] at h

/-- **Corollary `cor:localcost`, over bijections.**  At a site of a realisation of Definition
`def:pairing`, the minimum cost of a bijection between the arrivals and the departures is
`max(|alpha_s|,|beta_s|)`, a function of the two deposits, the site, the displacement and the
marker data alone. -/
theorem MarkedSite.site_cost_bij (t : MarkedSite) (ca : A → Cls) (cd : D → Cls)
    (h0 : cnt ca 0 = t.Ap) (h1 : cnt ca 1 = t.Am) (h2 : cnt ca 2 = t.Bp) (h3 : cnt ca 3 = t.Bm)
    (h4 : cnt cd 0 = t.Cp) (h5 : cnt cd 1 = t.Cm) (h6 : cnt cd 2 = t.Dp) (h7 : cnt cd 3 = t.Dm) :
    IsLeast {n : ℕ | ∃ σ : A ≃ D, bijCost ca cd σ = n} t.cost := by
  have hbal : cnt ca 0 + cnt ca 1 + cnt ca 2 + cnt ca 3
      = cnt cd 0 + cnt cd 1 + cnt cd 2 + cnt cd 3 := by
    rw [h0, h1, h2, h3, h4, h5, h6, h7]; exact t.balanced
  have h := bij_min ca cd hbal
  rw [h0, h1, h2, h3, h4, h5, h6, h7, siteCost_eq _ _ _ _ _ _ _ _ t.Phi_le_min,
    t.alpha_eq, t.beta_eq] at h
  exact h

end SiteCost

#print axioms SiteCost.pairCost_eq
#print axioms SiteCost.sum_mult_row
#print axioms SiteCost.sum_mult_col
#print axioms SiteCost.bijCost_eq_mult
#print axioms SiteCost.planOfBij_cost
#print axioms SiteCost.card_blk_fibre
#print axioms SiteCost.card_blkT_fibre
#print axioms SiteCost.blkEquivArr_cls
#print axioms SiteCost.blkTEquivDep_cls
#print axioms SiteCost.bijOfMatrix_cost
#print axioms SiteCost.matOf_row
#print axioms SiteCost.matOf_col
#print axioms SiteCost.matOf_cost
#print axioms SiteCost.bij_min
#print axioms SiteCost.MarkedSite.site_cost_bij
