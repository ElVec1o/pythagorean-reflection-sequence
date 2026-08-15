/-
  Realisation.lean
  ================
  Definition `def:pairing` of `paper/journal/paper2.tex` over a whole edge path, and with it
  Corollary `cor:lRclosed`, Corollary `cor:marker` and the parts of Proposition `prop:cut`
  that quantify over a realisation rather than over a single site.

  `SiteCost.lean` and `MarkedSite.lean` treat one site.  This file adds the global data:

  * `PathData`        the marker data, the displacement `k^*` and the deposits `d_j`, with the
                      span `[A,B]` of Corollary `cor:lRclosed`;
  * `Realisation`     a realisation of Definition `def:pairing`: an up/down split of the
                      crossings of each edge whose support is an interval containing `0`, a
                      sign split on each crossing, and a pairing at every site;
  * `lR_closed`       Corollary `cor:lRclosed`: the minimum cost is
                      `sum_span m_j + sum_sites max(|alpha_s|,|beta_s|)`;
  * `rigidity`        Corollary `cor:lRclosed`, second clause: every minimum-cost realisation
                      has support exactly the span, `m_j = max(|d_j|,|f_j|)` forced to `2` where
                      that vanishes, and every site pairing at its minimum;
  * `marker_near`, `marker_far_left`, `marker_far_right`
                      Corollary `cor:marker`, the two junction costs;
  * `cut_no_cross`    Proposition `prop:cut`, first sentence, at the level of a realisation: in
                      a minimum-cost realisation no strand crosses a cut site;
  * `gap_run_cut`     Proposition `prop:cut`, last sentence: a maximal gap run of `L` edges
                      contributes exactly its `L-1` interior sites to the cut set, and neither
                      of its two end sites.

  NOT formalised here: the component count `c >= |Z|` of Proposition `prop:cut`.  A
  `Realisation` carries the pairing at each site but not the strand graph those pairings
  assemble into, so "number of components" is not expressible against this structure.

  No `sorry`.
-/

import MarkedSite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum

namespace SiteCost

/-- `[s = 0]`: the virtual arrival of Definition `def:pairing`. -/
def vArr (s : ℤ) : ℕ := if s = 0 then 1 else 0

/-! ## The global data of Definition `def:pairing` -/

/-- The data of Definition `def:pairing` other than the realisation: the marker data
`(eps^*, delta^*)`, the displacement `k^*`, and the deposits `d_j` on the integer edges, with
`d_j = f_j (mod 2)`.  `A` and `B` are the ends of the *span*, the least interval of edges
containing `0`, every `j` with `d_j /= 0` and every `j` with `f_j /= 0`: `houter` says the
interval contains all of them, `hAmin` and `hBmin` that it is the least such. -/
structure PathData where
  kstar : ℤ
  eps : ℤ
  delta : Bool
  heps : eps = 1 ∨ eps = -1
  d : ℤ → ℤ
  hpar : ∀ j, (d j - travel kstar j) % 2 = 0
  A : ℤ
  B : ℤ
  hA : A ≤ 0
  hB : 0 ≤ B
  houter : ∀ j, j < A ∨ B < j → d j = 0 ∧ travel kstar j = 0
  hAmin : A = 0 ∨ d A ≠ 0 ∨ travel kstar A ≠ 0
  hBmin : B = 0 ∨ d B ≠ 0 ∨ travel kstar B ≠ 0

namespace PathData

variable (P : PathData)

/-- The travel indicator of edge `j`. -/
def f (j : ℤ) : ℤ := travel P.kstar j

/-- `[s = k^*]`: the virtual departure. -/
def vD (s : ℤ) : ℕ := if s = P.kstar then 1 else 0
/-- `[s = k^*][delta^* = 0]`. -/
def vL (s : ℤ) : ℕ := if P.delta then 0 else P.vD s
/-- `[s = k^*][delta^* = 1]`. -/
def vR (s : ℤ) : ℕ := if P.delta then P.vD s else 0

/-- `alpha_s` of Corollary `cor:localcost`. -/
def alphaAt (s : ℤ) : ℤ := P.d (s - 1) - vArr s + P.eps * P.vL s
/-- `beta_s` of Corollary `cor:localcost`. -/
def betaAt (s : ℤ) : ℤ := P.d s - P.eps * P.vR s
/-- `Phi_s` of Corollary `cor:localcost`. -/
def PhiAt (s : ℤ) : ℤ := P.f (s - 1) + vArr s - P.vL s

/-- `Site(s) = max(|alpha_s|,|beta_s|)`, the site cost of Corollary `cor:localcost`. -/
def siteCost (s : ℤ) : ℕ := max (P.alphaAt s).natAbs (P.betaAt s).natAbs

/-- A *cut* site of Proposition `prop:cut`. -/
def cut (s : ℤ) : Prop := P.alphaAt s = 0 ∧ P.betaAt s = 0 ∧ P.PhiAt s = 0

/-- `max(|d_j|,|f_j|)`, forced to `2` where that vanishes: the crossing count of Corollary
`cor:lRclosed`. -/
def mu (j : ℤ) : ℕ :=
  if P.d j = 0 ∧ travel P.kstar j = 0 then 2
  else max (P.d j).natAbs (travel P.kstar j).natAbs

/-- The crossing count of a minimum-cost realisation: `mu` on the span, `0` off it. -/
def mm (j : ℤ) : ℕ := if P.A ≤ j ∧ j ≤ P.B then P.mu j else 0

/-- The value of Corollary `cor:lRclosed`. -/
def lR : ℕ :=
  (∑ j ∈ Finset.Icc P.A P.B, P.mu j) + ∑ s ∈ Finset.Icc P.A (P.B + 1), P.siteCost s

/-! ### The least admissible crossing count -/

theorem mu_par (j : ℤ) : ((P.mu j : ℤ) - travel P.kstar j) % 2 = 0 := by
  have hp := P.hpar j
  have hc := travel_cases P.kstar j
  simp only [mu]; split_ifs <;> omega

theorem mu_ge_f (j : ℤ) : (travel P.kstar j).natAbs ≤ P.mu j := by
  have hc := travel_cases P.kstar j
  simp only [mu]; split_ifs <;> omega

theorem mu_ge_d (j : ℤ) : (P.d j).natAbs ≤ P.mu j := by
  have hc := travel_cases P.kstar j
  simp only [mu]; split_ifs <;> omega

theorem mu_pos (j : ℤ) : 1 ≤ P.mu j := by
  have hc := travel_cases P.kstar j
  simp only [mu]; split_ifs <;> omega

theorem mm_eq_mu {j : ℤ} (h : P.A ≤ j ∧ j ≤ P.B) : P.mm j = P.mu j := by
  simp only [mm, if_pos h]

theorem mm_eq_zero {j : ℤ} (h : ¬(P.A ≤ j ∧ j ≤ P.B)) : P.mm j = 0 := by
  simp only [mm, if_neg h]

theorem mm_par (j : ℤ) : ((P.mm j : ℤ) - travel P.kstar j) % 2 = 0 := by
  by_cases h : P.A ≤ j ∧ j ≤ P.B
  · rw [P.mm_eq_mu h]; exact P.mu_par j
  · rw [P.mm_eq_zero h]
    obtain ⟨-, h2⟩ := P.houter j (by omega)
    simp [h2]

theorem mm_ge_f (j : ℤ) : (travel P.kstar j).natAbs ≤ P.mm j := by
  by_cases h : P.A ≤ j ∧ j ≤ P.B
  · rw [P.mm_eq_mu h]; exact P.mu_ge_f j
  · rw [P.mm_eq_zero h]
    obtain ⟨-, h2⟩ := P.houter j (by omega)
    simp [h2]

theorem mm_ge_d (j : ℤ) : (P.d j).natAbs ≤ P.mm j := by
  by_cases h : P.A ≤ j ∧ j ≤ P.B
  · rw [P.mm_eq_mu h]; exact P.mu_ge_d j
  · rw [P.mm_eq_zero h]
    obtain ⟨h1, -⟩ := P.houter j (by omega)
    simp [h1]

theorem mm_ne_zero {j : ℤ} (h : P.A ≤ j ∧ j ≤ P.B) : P.mm j ≠ 0 := by
  rw [P.mm_eq_mu h]; have := P.mu_pos j; omega

/-! ### The crossing data of the minimum-cost realisation -/

/-- Up-crossings of edge `j`. -/
def cu (j : ℤ) : ℕ := (((P.mm j : ℤ) + travel P.kstar j).toNat) / 2
/-- Down-crossings of edge `j`. -/
def cdn (j : ℤ) : ℕ := (((P.mm j : ℤ) - travel P.kstar j).toNat) / 2
/-- `+` down-crossings of edge `j`. -/
def cpd (j : ℤ) : ℕ := ((P.d j - travel P.kstar j).toNat) / 2
/-- `+` up-crossings of edge `j`. -/
def cpu (j : ℤ) : ℕ := ((travel P.kstar j - P.d j).toNat) / 2

theorem cu_add_cdn (j : ℤ) : P.cu j + P.cdn j = P.mm j := by
  have h1 := P.mm_par j
  have h2 := P.mm_ge_f j
  simp only [cu, cdn]; omega

theorem cu_sub_cdn (j : ℤ) : (P.cu j : ℤ) - P.cdn j = travel P.kstar j := by
  have h1 := P.mm_par j
  have h2 := P.mm_ge_f j
  simp only [cu, cdn]; omega

theorem cpu_le_cu (j : ℤ) : P.cpu j ≤ P.cu j := by
  have h1 := P.mm_par j
  have h2 := P.mm_ge_f j
  have h3 := P.mm_ge_d j
  have h4 := P.hpar j
  simp only [cu, cpu]; omega

theorem cpd_le_cdn (j : ℤ) : P.cpd j ≤ P.cdn j := by
  have h1 := P.mm_par j
  have h2 := P.mm_ge_f j
  have h3 := P.mm_ge_d j
  have h4 := P.hpar j
  simp only [cdn, cpd]; omega

theorem cd_eq (j : ℤ) : P.d j = 2 * (P.cpd j : ℤ) - P.cdn j + P.cu j - 2 * P.cpu j := by
  have h1 := P.mm_par j
  have h2 := P.mm_ge_f j
  have h3 := P.mm_ge_d j
  have h4 := P.hpar j
  simp only [cu, cdn, cpd, cpu]; omega

end PathData

/-! ## The site of a realisation -/

/-- The site data at `s` of an up/down split and a sign split on the edges. -/
def siteAt (P : PathData) (u dn pu pd : ℤ → ℕ)
    (hpu : ∀ j, pu j ≤ u j) (hpd : ∀ j, pd j ≤ dn j)
    (hf : ∀ j, (u j : ℤ) - dn j = travel P.kstar j) (s : ℤ) : MarkedSite where
  kstar := P.kstar
  s := s
  eps := P.eps
  delta := P.delta
  heps := P.heps
  uL := u (s - 1)
  dnL := dn (s - 1)
  puL := pu (s - 1)
  pdL := pd (s - 1)
  uR := u s
  dnR := dn s
  puR := pu s
  pdR := pd s
  hpuL := hpu _
  hpdL := hpd _
  hpuR := hpu _
  hpdR := hpd _
  hfL := hf _
  hfR := hf _

/-- A pairing at a site: Definition `def:pairing` read through the multiplicity matrix, which
`PairingMatrix.lean` shows carries the same minimum as a bijection. -/
abbrev PlanAt (t : MarkedSite) : Type := Plan t.Ap t.Am t.Bp t.Bm t.Cp t.Cm t.Dp t.Dm

theorem exists_opt (t : MarkedSite) : ∃ p : PlanAt t, p.cost = t.cost := t.site_cost.1

/-- A pairing at `t` of minimum cost. -/
noncomputable def optPlan (t : MarkedSite) : PlanAt t := (exists_opt t).choose

theorem optPlan_cost (t : MarkedSite) : (optPlan t).cost = t.cost := (exists_opt t).choose_spec

/-! ## Realisations -/

/-- A realisation of Definition `def:pairing`.  Edge `j` is crossed `u j` times upward, of
which `pu j` carry `+`, and `dn j` times downward, of which `pd j` carry `+`; `hf` says the edge
realises the travel indicator and `hd` that it realises the deposit; the support of the crossing
count `u + dn` is the interval `[a,b]`, which contains `0`.  At every site there is a pairing.
The constraints `m_j >= max(|d_j|,|f_j|)` and `m_j = d_j (mod 2)` of Definition `def:pairing`
are consequences of `hf`, `hd`, `hpu` and `hpd`, and appear below as `Realisation.m_ge`. -/
structure Realisation (P : PathData) where
  a : ℤ
  b : ℤ
  ha : a ≤ 0
  hb : 0 ≤ b
  u : ℤ → ℕ
  dn : ℤ → ℕ
  pu : ℤ → ℕ
  pd : ℤ → ℕ
  hpu : ∀ j, pu j ≤ u j
  hpd : ∀ j, pd j ≤ dn j
  hf : ∀ j, (u j : ℤ) - dn j = travel P.kstar j
  hd : ∀ j, P.d j = 2 * (pd j : ℤ) - dn j + u j - 2 * pu j
  hsupp : ∀ j, u j + dn j ≠ 0 ↔ (a ≤ j ∧ j ≤ b)
  pair : ∀ s : ℤ, PlanAt (siteAt P u dn pu pd hpu hpd hf s)

namespace Realisation

variable {P : PathData} (R : Realisation P)

/-- The crossing count of edge `j`. -/
def m (j : ℤ) : ℕ := R.u j + R.dn j

/-- The site of the realisation at `s`. -/
def site (s : ℤ) : MarkedSite := siteAt P R.u R.dn R.pu R.pd R.hpu R.hpd R.hf s

/-- The cost of a realisation: the total crossing count plus the pairing costs. -/
def cost : ℕ :=
  (∑ j ∈ Finset.Icc R.a R.b, R.m j) + ∑ s ∈ Finset.Icc R.a (R.b + 1), (R.pair s).cost

theorem site_dL (s : ℤ) : (R.site s).dL = P.d (s - 1) := (R.hd (s - 1)).symm

theorem site_dR (s : ℤ) : (R.site s).dR = P.d s := (R.hd s).symm

/-- The site cost of a realisation is the `Site(s)` of Corollary `cor:localcost`, a function of
the deposits, the site, the displacement and the marker data alone. -/
theorem site_cost_eq (s : ℤ) : (R.site s).cost = P.siteCost s := by
  simp only [MarkedSite.cost, PathData.siteCost, PathData.alphaAt, PathData.betaAt,
    R.site_dL, R.site_dR]
  rfl

theorem site_alpha (s : ℤ) :
    alpha (R.site s).Ap (R.site s).Am (R.site s).Cp (R.site s).Cm = P.alphaAt s := by
  rw [MarkedSite.alpha_eq, R.site_dL]; rfl

theorem site_beta (s : ℤ) :
    beta (R.site s).Bp (R.site s).Bm (R.site s).Dp (R.site s).Dm = P.betaAt s := by
  rw [MarkedSite.beta_eq, R.site_dR]; rfl

theorem site_Phi (s : ℤ) :
    Phi (R.site s).Ap (R.site s).Am (R.site s).Cp (R.site s).Cm = P.PhiAt s := by
  rw [MarkedSite.Phi_eq]; rfl

/-- Every pairing of a realisation costs at least the site cost. -/
theorem pair_cost_ge (s : ℤ) : P.siteCost s ≤ (R.pair s).cost := by
  have h := (MarkedSite.site_cost (R.site s)).2 ⟨R.pair s, rfl⟩
  rwa [R.site_cost_eq] at h

/-- **The constraint of Definition `def:pairing` on the crossing counts.**  On its support the
crossing count of a realisation is at least `max(|d_j|,|f_j|)` and at least `2` where that
vanishes, so it is at least `mu_j`. -/
theorem m_ge {j : ℤ} (hj : R.a ≤ j ∧ j ≤ R.b) : P.mu j ≤ R.m j := by
  have h1 := R.hpu j
  have h2 := R.hpd j
  have h3 := R.hf j
  have h4 := R.hd j
  have h5 := (R.hsupp j).2 hj
  simp only [m] at h5 ⊢
  simp only [PathData.mu]
  split_ifs <;> omega

/-- Off its support a realisation has no crossings. -/
theorem m_zero {j : ℤ} (hj : ¬(R.a ≤ j ∧ j ≤ R.b)) : R.m j = 0 := by
  by_contra h
  exact hj ((R.hsupp j).1 h)

/-- The support of a realisation contains the span. -/
theorem span_le : R.a ≤ P.A ∧ P.B ≤ R.b := by
  constructor
  · rcases P.hAmin with h | h | h
    · have := R.ha; omega
    · by_contra hc
      have h0 := R.m_zero (j := P.A) (by omega)
      have h1 := R.hd P.A
      have h2 := R.hpu P.A
      have h3 := R.hpd P.A
      simp only [m] at h0
      omega
    · by_contra hc
      have h0 := R.m_zero (j := P.A) (by omega)
      have h1 := R.hf P.A
      simp only [m] at h0
      omega
  · rcases P.hBmin with h | h | h
    · have := R.hb; omega
    · by_contra hc
      have h0 := R.m_zero (j := P.B) (by omega)
      have h1 := R.hd P.B
      have h2 := R.hpu P.B
      have h3 := R.hpd P.B
      simp only [m] at h0
      omega
    · by_contra hc
      have h0 := R.m_zero (j := P.B) (by omega)
      have h1 := R.hf P.B
      simp only [m] at h0
      omega

/-- Both virtual events sit at a site of the support window `[a, b+1]`: site `0` because the
support contains edge `0`, and site `k^*` because an edge between `0` and `k^*` carries a non-zero
travel indicator and is therefore in the support. -/
theorem virtual_in_window : R.a ≤ P.kstar ∧ P.kstar ≤ R.b + 1 := by
  have hra := R.ha
  have hrb := R.hb
  rcases lt_trichotomy P.kstar 0 with h | h | h
  · have h1 : travel P.kstar P.kstar = -1 := by unfold travel; split_ifs <;> omega
    have h2 := R.hf P.kstar
    have h3 : R.u P.kstar + R.dn P.kstar ≠ 0 := by omega
    have h4 := (R.hsupp P.kstar).1 h3
    omega
  · omega
  · have h1 : travel P.kstar (P.kstar - 1) = 1 := by unfold travel; split_ifs <;> omega
    have h2 := R.hf (P.kstar - 1)
    have h3 : R.u (P.kstar - 1) + R.dn (P.kstar - 1) ≠ 0 := by omega
    have h4 := (R.hsupp (P.kstar - 1)).1 h3
    omega

/-- Off the window every count at a site vanishes, virtual events included, so its pairing costs
`0`.  Summing the pairing costs over `[a, b+1]` is therefore the full sum of Definition
`def:pairing` over all sites. -/
theorem pair_cost_zero_outside (s : ℤ) (hs : ¬(R.a ≤ s ∧ s ≤ R.b + 1)) :
    (R.pair s).cost = 0 := by
  have hk := R.virtual_in_window
  have hra := R.ha
  have hrb := R.hb
  have e1 : R.u (s - 1) + R.dn (s - 1) = 0 := by
    by_contra hc; have := (R.hsupp (s - 1)).1 hc; omega
  have e2 : R.u s + R.dn s = 0 := by
    by_contra hc; have := (R.hsupp s).1 hc; omega
  have hs0 : s ≠ 0 := by omega
  have p1 := R.hpu (s - 1)
  have p2 := R.hpd (s - 1)
  have p3 := R.hpu s
  have p4 := R.hpd s
  have hAp : (siteAt P R.u R.dn R.pu R.pd R.hpu R.hpd R.hf s).Ap = 0 := by
    simp only [siteAt, MarkedSite.Ap, MarkedSite.vA]; split_ifs <;> omega
  have hAm : (siteAt P R.u R.dn R.pu R.pd R.hpu R.hpd R.hf s).Am = 0 := by
    simp only [siteAt, MarkedSite.Am]; omega
  have hBp : (siteAt P R.u R.dn R.pu R.pd R.hpu R.hpd R.hf s).Bp = 0 := by
    simp only [siteAt, MarkedSite.Bp]; omega
  have hBm : (siteAt P R.u R.dn R.pu R.pd R.hpu R.hpd R.hf s).Bm = 0 := by
    simp only [siteAt, MarkedSite.Bm]; omega
  have r0 := (R.pair s).row0
  have r1 := (R.pair s).row1
  have r2 := (R.pair s).row2
  have r3 := (R.pair s).row3
  simp only [Plan.cost]
  omega

theorem edge_subset : Finset.Icc P.A P.B ⊆ Finset.Icc R.a R.b :=
  Finset.Icc_subset_Icc R.span_le.1 R.span_le.2

theorem site_subset : Finset.Icc P.A (P.B + 1) ⊆ Finset.Icc R.a (R.b + 1) :=
  Finset.Icc_subset_Icc R.span_le.1 (by have := R.span_le.2; omega)

theorem edge_sum_ge : ∑ j ∈ Finset.Icc P.A P.B, P.mu j ≤ ∑ j ∈ Finset.Icc R.a R.b, R.m j :=
  le_trans
    (Finset.sum_le_sum fun _ hj => R.m_ge (Finset.mem_Icc.1 (R.edge_subset hj)))
    (Finset.sum_le_sum_of_subset R.edge_subset)

theorem site_sum_ge :
    ∑ s ∈ Finset.Icc P.A (P.B + 1), P.siteCost s
      ≤ ∑ s ∈ Finset.Icc R.a (R.b + 1), (R.pair s).cost :=
  le_trans (Finset.sum_le_sum fun s _ => R.pair_cost_ge s)
    (Finset.sum_le_sum_of_subset R.site_subset)

/-- **Corollary `cor:lRclosed`, lower bound.** -/
theorem cost_ge : P.lR ≤ R.cost := by
  have h1 := R.edge_sum_ge
  have h2 := R.site_sum_ge
  simp only [PathData.lR, cost]
  omega

end Realisation

/-! ## The minimum-cost realisation -/

/-- The realisation of Corollary `cor:lRclosed`: support exactly the span, crossing counts
`max(|d_j|,|f_j|)` forced to `2` where that vanishes, and a minimum-cost pairing at every
site. -/
noncomputable def PathData.canon (P : PathData) : Realisation P where
  a := P.A
  b := P.B
  ha := P.hA
  hb := P.hB
  u := P.cu
  dn := P.cdn
  pu := P.cpu
  pd := P.cpd
  hpu := P.cpu_le_cu
  hpd := P.cpd_le_cdn
  hf := P.cu_sub_cdn
  hd := P.cd_eq
  hsupp := fun j => by
    rw [P.cu_add_cdn j]
    exact ⟨fun h => by by_contra hc; exact h (P.mm_eq_zero hc), fun h => P.mm_ne_zero h⟩
  pair := fun _ => optPlan _

theorem PathData.canon_cost (P : PathData) : P.canon.cost = P.lR := by
  simp only [Realisation.cost, PathData.lR, canon]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_Icc.1 hj
    show P.cu j + P.cdn j = P.mu j
    rw [P.cu_add_cdn j, P.mm_eq_mu hj']
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [optPlan_cost]
    exact P.canon.site_cost_eq s

/-- **Corollary `cor:lRclosed`.**  The minimum cost of a realisation of Definition
`def:pairing` is the sum over the span of `max(|d_j|,|f_j|)`, forced to `2` where that vanishes,
plus the sum over the sites of the span of `max(|alpha_s|,|beta_s|)`. -/
theorem lR_closed (P : PathData) : IsLeast {n : ℕ | ∃ R : Realisation P, R.cost = n} P.lR :=
  ⟨⟨P.canon, P.canon_cost⟩, by rintro n ⟨R, rfl⟩; exact R.cost_ge⟩

/-! ## Rigidity -/

namespace Realisation

variable {P : PathData} (R : Realisation P)

/-- **Corollary `cor:lRclosed`, second clause.**  Every minimum-cost realisation has support
exactly the span, crossing counts `max(|d_j|,|f_j|)` forced to `2` where that vanishes, and
every site pairing at its minimum. -/
theorem rigidity (hmin : R.cost = P.lR) :
    R.a = P.A ∧ R.b = P.B ∧ (∀ j, R.m j = P.mm j) ∧
      (∀ s ∈ Finset.Icc P.A (P.B + 1), (R.pair s).cost = P.siteCost s) := by
  have hedge := R.edge_sum_ge
  have hsite := R.site_sum_ge
  have hE : ∑ j ∈ Finset.Icc R.a R.b, R.m j = ∑ j ∈ Finset.Icc P.A P.B, P.mu j := by
    simp only [cost, PathData.lR] at hmin; omega
  have hS : ∑ s ∈ Finset.Icc R.a (R.b + 1), (R.pair s).cost
      = ∑ s ∈ Finset.Icc P.A (P.B + 1), P.siteCost s := by
    simp only [cost, PathData.lR] at hmin; omega
  have hin : ∑ j ∈ Finset.Icc P.A P.B, P.mu j ≤ ∑ j ∈ Finset.Icc P.A P.B, R.m j :=
    Finset.sum_le_sum fun j hj => R.m_ge (Finset.mem_Icc.1 (R.edge_subset hj))
  have hsub : ∑ j ∈ Finset.Icc P.A P.B, R.m j ≤ ∑ j ∈ Finset.Icc R.a R.b, R.m j :=
    Finset.sum_le_sum_of_subset R.edge_subset
  have hEq : ∑ j ∈ Finset.Icc P.A P.B, R.m j = ∑ j ∈ Finset.Icc P.A P.B, P.mu j := by omega
  have hsd : ∑ j ∈ Finset.Icc R.a R.b \ Finset.Icc P.A P.B, R.m j = 0 := by
    have hh := Finset.sum_sdiff (f := R.m) R.edge_subset
    omega
  have hz : ∀ j ∈ Finset.Icc R.a R.b \ Finset.Icc P.A P.B, R.m j = 0 :=
    Finset.sum_eq_zero_iff.1 hsd
  have hab : R.a = P.A ∧ R.b = P.B := by
    have hla := R.span_le.1
    have hlb := R.span_le.2
    have hra := R.ha
    have hrb := R.hb
    constructor
    · by_contra hc
      have h2 : R.a ∈ Finset.Icc R.a R.b \ Finset.Icc P.A P.B := by
        simp only [Finset.mem_sdiff, Finset.mem_Icc]
        omega
      exact (R.hsupp R.a).2 ⟨le_refl _, by omega⟩ (hz _ h2)
    · by_contra hc
      have h2 : R.b ∈ Finset.Icc R.a R.b \ Finset.Icc P.A P.B := by
        simp only [Finset.mem_sdiff, Finset.mem_Icc]
        omega
      exact (R.hsupp R.b).2 ⟨by omega, le_refl _⟩ (hz _ h2)
  refine ⟨hab.1, hab.2, ?_, ?_⟩
  · intro j
    by_cases hj : P.A ≤ j ∧ j ≤ P.B
    · rw [P.mm_eq_mu hj]
      have hterm := (Finset.sum_eq_sum_iff_of_le (f := P.mu) (g := R.m)
        (fun i hi => R.m_ge (Finset.mem_Icc.1 (R.edge_subset hi)))).1 hEq.symm
      exact (hterm j (Finset.mem_Icc.2 hj)).symm
    · rw [P.mm_eq_zero hj]
      exact R.m_zero (by rw [hab.1, hab.2]; exact hj)
  · have hS' : ∑ s ∈ Finset.Icc P.A (P.B + 1), (R.pair s).cost
        = ∑ s ∈ Finset.Icc P.A (P.B + 1), P.siteCost s := by
      rw [← hS, hab.1, hab.2]
    exact fun s hs =>
      ((Finset.sum_eq_sum_iff_of_le (fun i _ => R.pair_cost_ge i)).1 hS'.symm s hs).symm

/-- **Proposition `prop:cut`, first sentence, over a realisation.**  At a cut site of the span
every minimum-cost realisation matches each arrival with a departure on its own side: no strand
crosses. -/
theorem cut_no_cross (hmin : R.cost = P.lR) (s : ℤ) (hs : s ∈ Finset.Icc P.A (P.B + 1))
    (hcut : P.cut s) : (R.pair s).cross = 0 := by
  obtain ⟨-, -, -, hp⟩ := R.rigidity hmin
  obtain ⟨ha, hb, hf⟩ := hcut
  refine cut_forces_no_cross (R.site s).Ap (R.site s).Am (R.site s).Bp (R.site s).Bm
    (R.site s).Cp (R.site s).Cm (R.site s).Dp (R.site s).Dm
    (by rw [R.site_alpha]; exact ha) (by rw [R.site_beta]; exact hb)
    (by rw [R.site_Phi]; exact hf) (R.pair s) ?_
  refine (hp s hs).trans ?_
  simp only [siteValue, PathData.siteCost]
  rw [R.site_alpha, R.site_beta, R.site_Phi, ha, hb, hf]
  simp

end Realisation

/-! ## Corollary `cor:marker`: the two junctions -/

namespace PathData

variable (P : PathData)

/-- **Corollary `cor:marker`, the near junction.**  For `k^* /= 0` the cost of the junction at
site `0` is `max(|d_{-1} - 1|, |d_0|)`, for all four marker data. -/
theorem marker_near (hk : P.kstar ≠ 0) :
    P.siteCost 0 = max (P.d (-1) - 1).natAbs (P.d 0).natAbs := by
  have hD : P.vD 0 = 0 := by simp [vD, Ne.symm hk]
  have hL : P.vL 0 = 0 := by simp [vL, hD]
  have hR : P.vR 0 = 0 := by simp [vR, hD]
  simp only [siteCost, alphaAt, betaAt, vArr, hL, hR]
  norm_num

/-- **Corollary `cor:marker`, the far junction, `delta^* = 0`.**  At site `k^* /= 0` the cost is
`max(|d_{k^*-1} + eps^*|, |d_{k^*}|)`. -/
theorem marker_far_left (hk : P.kstar ≠ 0) (hd : P.delta = false) :
    P.siteCost P.kstar = max (P.d (P.kstar - 1) + P.eps).natAbs (P.d P.kstar).natAbs := by
  have hD : P.vD P.kstar = 1 := by simp [vD]
  have hL : P.vL P.kstar = 1 := by simp [vL, hd, hD]
  have hR : P.vR P.kstar = 0 := by simp [vR, hd]
  have hA : vArr P.kstar = 0 := by simp [vArr, hk]
  simp only [siteCost, alphaAt, betaAt, hA, hL, hR]
  norm_num

/-- **Corollary `cor:marker`, the far junction, `delta^* = 1`.**  At site `k^* /= 0` the cost is
`max(|d_{k^*-1}|, |d_{k^*} - eps^*|)`. -/
theorem marker_far_right (hk : P.kstar ≠ 0) (hd : P.delta = true) :
    P.siteCost P.kstar = max (P.d (P.kstar - 1)).natAbs (P.d P.kstar - P.eps).natAbs := by
  have hD : P.vD P.kstar = 1 := by simp [vD]
  have hL : P.vL P.kstar = 0 := by simp [vL, hd]
  have hR : P.vR P.kstar = 1 := by simp [vR, hd, hD]
  have hA : vArr P.kstar = 0 := by simp [vArr, hk]
  simp only [siteCost, alphaAt, betaAt, hA, hL, hR]
  norm_num

/-- **Corollary `cor:marker`, the dependence clause.**  At `d_L = 1`, `d_R = 0` the far junction
costs `2` and `0` for `delta^* = 0` and `eps^* = +1, -1`, and `1` and `1` for `delta^* = 1`: it is
not independent of the marker data.  Nor is it the mirror image of the near junction, whose form
`max(|d_L - 1|, |d_R|)` read with the two deposits exchanged gives `1` on the same cell. -/
theorem marker_far_depends :
    max ((1 : ℤ) + 1).natAbs (0 : ℤ).natAbs = 2 ∧
    max ((1 : ℤ) + (-1)).natAbs (0 : ℤ).natAbs = 0 ∧
    max (1 : ℤ).natAbs ((0 : ℤ) - 1).natAbs = 1 ∧
    max (1 : ℤ).natAbs ((0 : ℤ) - (-1)).natAbs = 1 ∧
    max ((0 : ℤ) - 1).natAbs (1 : ℤ).natAbs = 1 := by decide

/-! ## Proposition `prop:cut`, the gap runs -/

/-- **Proposition `prop:cut`, last sentence.**  A maximal run of `L = r - l + 1` gap edges of
the bulk, flanked by non-zero deposits and carrying no virtual event at any of its sites,
contributes exactly its `L - 1` interior sites `l+1, ..., r` to the set of cut sites; neither of
its two end sites `l` and `r+1` is cut. -/
theorem gap_run_cut (l r : ℤ) (hlr : l ≤ r)
    (hgap : ∀ j, l ≤ j → j ≤ r → P.d j = 0 ∧ travel P.kstar j = 0)
    (hL : P.d (l - 1) ≠ 0) (hR : P.d (r + 1) ≠ 0)
    (hnov : ∀ s, l ≤ s → s ≤ r + 1 → s ≠ 0 ∧ s ≠ P.kstar) :
    (∀ s, l < s → s ≤ r → P.cut s) ∧ ¬ P.cut l ∧ ¬ P.cut (r + 1) := by
  refine ⟨fun s h1 h2 => ?_, ?_, ?_⟩
  · obtain ⟨hs0, hsk⟩ := hnov s (by omega) (by omega)
    obtain ⟨hd1, hf1⟩ := hgap (s - 1) (by omega) (by omega)
    obtain ⟨hd2, -⟩ := hgap s (by omega) (by omega)
    have hA : vArr s = 0 := by simp [vArr, hs0]
    have hD : P.vD s = 0 := by simp [vD, hsk]
    have hLv : P.vL s = 0 := by simp [vL, hD]
    have hRv : P.vR s = 0 := by simp [vR, hD]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [alphaAt, betaAt, PhiAt, f, hA, hLv, hRv, hd1, hd2, hf1] <;> norm_num
  · obtain ⟨hs0, hsk⟩ := hnov l (by omega) (by omega)
    have hA : vArr l = 0 := by simp [vArr, hs0]
    have hD : P.vD l = 0 := by simp [vD, hsk]
    have hLv : P.vL l = 0 := by simp [vL, hD]
    rintro ⟨hcon, -, -⟩
    exact hL (by simpa [alphaAt, hA, hLv] using hcon)
  · obtain ⟨hs0, hsk⟩ := hnov (r + 1) (by omega) (by omega)
    have hD : P.vD (r + 1) = 0 := by simp [vD, hsk]
    have hRv : P.vR (r + 1) = 0 := by simp [vR, hD]
    rintro ⟨-, hcon, -⟩
    exact hR (by simpa [betaAt, hRv] using hcon)

/-! ## Non-vacuity -/

/-- The smallest configuration: `k^* = 0`, marker data `(eps^*,delta^*) = (+1,0)`, and no
deposits.  Its span is the single edge `0`. -/
def emptyPath : PathData where
  kstar := 0
  eps := 1
  delta := false
  heps := Or.inl rfl
  d := fun _ => 0
  hpar := fun j => by simp [travel_of_kstar_zero]
  A := 0
  B := 0
  hA := le_refl 0
  hB := le_refl 0
  houter := fun j _ => ⟨rfl, travel_of_kstar_zero j⟩
  hAmin := Or.inl rfl
  hBmin := Or.inl rfl

/-- The single gap edge is forced to `2` crossings and both of its sites are free, the virtual
arrival and the virtual departure being matched to each other. -/
theorem emptyPath_facts :
    emptyPath.mu 0 = 2 ∧ emptyPath.siteCost 0 = 0 ∧ emptyPath.siteCost 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [emptyPath, PathData.mu, PathData.siteCost, PathData.alphaAt, PathData.betaAt,
      PathData.vL, PathData.vR, PathData.vD, vArr, travel_of_kstar_zero]

end PathData

end SiteCost

#print axioms SiteCost.PathData.emptyPath_facts
#print axioms SiteCost.PathData.mu_par
#print axioms SiteCost.PathData.mu_ge_f
#print axioms SiteCost.PathData.mu_ge_d
#print axioms SiteCost.PathData.cu_add_cdn
#print axioms SiteCost.PathData.cu_sub_cdn
#print axioms SiteCost.PathData.cpu_le_cu
#print axioms SiteCost.PathData.cpd_le_cdn
#print axioms SiteCost.PathData.cd_eq
#print axioms SiteCost.Realisation.virtual_in_window
#print axioms SiteCost.Realisation.pair_cost_zero_outside
#print axioms SiteCost.PathData.marker_far_depends
#print axioms SiteCost.Realisation.site_cost_eq
#print axioms SiteCost.Realisation.m_ge
#print axioms SiteCost.Realisation.span_le
#print axioms SiteCost.Realisation.cost_ge
#print axioms SiteCost.PathData.canon_cost
#print axioms SiteCost.lR_closed
#print axioms SiteCost.Realisation.rigidity
#print axioms SiteCost.Realisation.cut_no_cross
#print axioms SiteCost.PathData.marker_near
#print axioms SiteCost.PathData.marker_far_left
#print axioms SiteCost.PathData.marker_far_right
#print axioms SiteCost.PathData.gap_run_cut
