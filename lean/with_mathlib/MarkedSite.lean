/-
  MarkedSite.lean
  ===============
  Corollary `cor:localcost` of `paper/journal/paper2.tex`, section 5.5 (`sec:sitecost`), in
  full: the site cost law at every site of a realisation of Definition `def:pairing`, the two
  sites carrying a virtual event included.

  `SiteCost.lean` proves Lemma `lem:transport`, the collapse step, the read-off at a site
  carrying no virtual event, and the interior case of `cor:localcost`.  What is added here is
  the travel indicator `f`, the marker data `(eps^*, delta^*)`, the virtual arrival at site `0`
  and the virtual departure at site `k^*`, and with them the eight remaining site types of the
  proof of `cor:localcost`, its independence clause, and Corollary `cor:marker`.

  Everything is finite integer arithmetic; every proof is closed by `omega` or `simp`, with no
  `sorry`.
-/

import SiteCost

namespace SiteCost

/-! ## The travel indicator -/

/-- The travel indicator of Definition `def:pairing`: `f j = 1` for `0 <= j < k^*`,
`f j = -1` for `k^* <= j < 0`, and `0` otherwise. -/
def travel (kstar j : ℤ) : ℤ :=
  if 0 ≤ j ∧ j < kstar then 1 else if kstar ≤ j ∧ j < 0 then -1 else 0

theorem travel_cases (kstar j : ℤ) :
    travel kstar j = 0 ∨ travel kstar j = 1 ∨ travel kstar j = -1 := by
  unfold travel; split_ifs <;> omega

theorem travel_of_kstar_zero (j : ℤ) : travel 0 j = 0 := by
  unfold travel; split_ifs <;> omega

/-- The local data of a site, as the proof of `cor:localcost` uses it: `f` jumps only at the
two sites carrying a virtual event and by exactly one unit there; the two virtual events
coincide only when `k^* = 0`, and then `f` vanishes on both adjacent edges. -/
theorem travel_site_facts (kstar s a v fL fR : ℤ)
    (ha : a = if s = 0 then 1 else 0) (hv : v = if s = kstar then 1 else 0)
    (hfL : fL = travel kstar (s - 1)) (hfR : fR = travel kstar s) :
    fL + a = fR + v ∧
    (fL = 0 ∨ fL = 1 ∨ fL = -1) ∧ (fR = 0 ∨ fR = 1 ∨ fR = -1) ∧
    (a = 0 ∨ a = 1) ∧ (v = 0 ∨ v = 1) ∧
    (a = 0 ∨ v = 0 ∨ (fL = 0 ∧ fR = 0)) := by
  subst ha; subst hv; subst hfL; subst hfR
  unfold travel; split_ifs <;> omega

/-! ## The arithmetic core of `cor:localcost` -/

/-- **The eight site types of `cor:localcost`.**  Write `f` for the travel indicator of the
left edge and `f'` for that of the right edge, `a = [s = 0]` for the virtual arrival,
`v = [s = k^*]` for the virtual departure, `l = v[delta^* = 0]` and `r = v[delta^* = 1]` for
its two possible sides, and `e = eps^*`, so that
`alpha = d - a + e l`, `beta = d' - e r` and `Phi = f + a - l`.  Then
`|Phi| <= min(|alpha|,|beta|)`.  The only inputs are that `d` and `d'` carry the parities of
`f` and `f'` and the site facts of `travel_site_facts`. -/
theorem Phi_le_min_core (dL dR fL fR a v l r e : ℤ)
    (hfL : fL = 0 ∨ fL = 1 ∨ fL = -1) (hfR : fR = 0 ∨ fR = 1 ∨ fR = -1)
    (hbal : fL + a = fR + v)
    (ha : a = 0 ∨ a = 1) (hv : v = 0 ∨ v = 1)
    (hboth : a = 0 ∨ v = 0 ∨ (fL = 0 ∧ fR = 0))
    (hsplit : (l = v ∧ r = 0) ∨ (l = 0 ∧ r = v))
    (he : e = 1 ∨ e = -1)
    (hpL : (dL - fL) % 2 = 0) (hpR : (dR - fR) % 2 = 0) :
    (fL + a - l).natAbs ≤ min (dL - a + e * l).natAbs (dR - e * r).natAbs := by
  rcases he with rfl | rfl <;> rcases hsplit with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-! ## A site of a realisation, with its virtual events -/

/-- One site `s` of a realisation of Definition `def:pairing`.  `kstar` is the displacement and
`(eps, delta)` the marker data, `delta = true` meaning `delta^* = 1`.  The eight crossing counts
are those of the two edges adjacent to `s`: the left edge is crossed `uL` times upward, of which
`puL` carry `+`, and `dnL` times downward, of which `pdL` carry `+`, and likewise on the right.
`hfL` and `hfR` say that the two edges realise the travel indicator. -/
structure MarkedSite where
  kstar : ℤ
  s : ℤ
  eps : ℤ
  delta : Bool
  heps : eps = 1 ∨ eps = -1
  uL : ℕ
  dnL : ℕ
  puL : ℕ
  pdL : ℕ
  uR : ℕ
  dnR : ℕ
  puR : ℕ
  pdR : ℕ
  hpuL : puL ≤ uL
  hpdL : pdL ≤ dnL
  hpuR : puR ≤ uR
  hpdR : pdR ≤ dnR
  hfL : (uL : ℤ) - dnL = travel kstar (s - 1)
  hfR : (uR : ℤ) - dnR = travel kstar s

namespace MarkedSite

variable (t : MarkedSite)

/-- `[s = 0]`: the virtual arrival of class `(L,+)` of Definition `def:pairing`. -/
def vA : ℕ := if t.s = 0 then 1 else 0
/-- `[s = k^*]`: the virtual departure. -/
def vD : ℕ := if t.s = t.kstar then 1 else 0
/-- `[s = k^*][delta^* = 0]`: the virtual departure when it sits on the left. -/
def vL : ℕ := if t.delta then 0 else t.vD
/-- `[s = k^*][delta^* = 1]`: the virtual departure when it sits on the right. -/
def vR : ℕ := if t.delta then t.vD else 0
/-- `[eps^* = +1]`. -/
def epsP : ℕ := if t.eps = 1 then 1 else 0
/-- `[eps^* = -1]`. -/
def epsM : ℕ := if t.eps = 1 then 0 else 1

/-- Arrivals of class `(L,+)`: the `+` up-crossings of the left edge, and the virtual arrival
if `s = 0`. -/
def Ap : ℕ := t.puL + t.vA
/-- Arrivals of class `(L,-)`. -/
def Am : ℕ := t.uL - t.puL
/-- Arrivals of class `(R,+)`: the `+` down-crossings of the right edge. -/
def Bp : ℕ := t.pdR
/-- Arrivals of class `(R,-)`. -/
def Bm : ℕ := t.dnR - t.pdR
/-- Departures of class `(L,+)`: the `+` down-crossings of the left edge, and the virtual
departure if it sits on the left and carries `+`. -/
def Cp : ℕ := t.pdL + t.vL * t.epsP
/-- Departures of class `(L,-)`. -/
def Cm : ℕ := (t.dnL - t.pdL) + t.vL * t.epsM
/-- Departures of class `(R,+)`: the `+` up-crossings of the right edge, and the virtual
departure if it sits on the right and carries `+`. -/
def Dp : ℕ := t.puR + t.vR * t.epsP
/-- Departures of class `(R,-)`. -/
def Dm : ℕ := (t.uR - t.puR) + t.vR * t.epsM

/-- The deposit on the left edge, `d = 2 p^d - dn + u - 2 p^u`. -/
def dL : ℤ := 2 * (t.pdL : ℤ) - t.dnL + t.uL - 2 * t.puL
/-- The deposit on the right edge. -/
def dR : ℤ := 2 * (t.pdR : ℤ) - t.dnR + t.uR - 2 * t.puR
/-- The travel indicator of the left edge. -/
def fL : ℤ := travel t.kstar (t.s - 1)
/-- The travel indicator of the right edge. -/
def fR : ℤ := travel t.kstar t.s

/-- The value of `cor:localcost` at the site, `max(|alpha_s|,|beta_s|)` with the two read-offs
written out.  It is a function of the two deposits, the site, the displacement and the marker
data alone. -/
def cost : ℕ :=
  max (t.dL - t.vA + t.eps * t.vL).natAbs (t.dR - t.eps * t.vR).natAbs

theorem vA_cast : (t.vA : ℤ) = if t.s = 0 then 1 else 0 := by
  simp only [vA]; split_ifs <;> simp

theorem vD_cast : (t.vD : ℤ) = if t.s = t.kstar then 1 else 0 := by
  simp only [vD]; split_ifs <;> simp

theorem split : ((t.vL : ℤ) = t.vD ∧ (t.vR : ℤ) = 0) ∨ ((t.vL : ℤ) = 0 ∧ (t.vR : ℤ) = t.vD) := by
  simp only [vL, vR]; split_ifs <;> simp

/-! ### The read-off from Definition `def:pairing` -/

/-- **`cor:localcost`, read-off (i).**  `alpha_s = d_{s-1} - [s=0] + eps^*[s=k^*][delta^*=0]`. -/
theorem alpha_eq : alpha t.Ap t.Am t.Cp t.Cm = t.dL - t.vA + t.eps * t.vL := by
  have h1 := t.hpuL; have h2 := t.hpdL; have h3 := t.heps
  simp only [alpha, Ap, Am, Cp, Cm, dL, vA, vL, vD, epsP, epsM]
  split_ifs <;> push_cast <;> omega

/-- **`cor:localcost`, read-off (ii).**  `beta_s = d_s - eps^*[s=k^*][delta^*=1]`. -/
theorem beta_eq : beta t.Bp t.Bm t.Dp t.Dm = t.dR - t.eps * t.vR := by
  have h1 := t.hpuR; have h2 := t.hpdR; have h3 := t.heps
  simp only [beta, Bp, Bm, Dp, Dm, dR, vR, vD, epsP, epsM]
  split_ifs <;> push_cast <;> omega

/-- **`cor:localcost`, read-off (iii).**  `Phi_s = f_{s-1} + [s=0] - [s=k^*][delta^*=0]`. -/
theorem Phi_eq : Phi t.Ap t.Am t.Cp t.Cm = t.fL + t.vA - t.vL := by
  have h1 := t.hpuL; have h2 := t.hpdL; have h4 := t.hfL
  simp only [Phi, Ap, Am, Cp, Cm, fL, vA, vL, vD, epsP, epsM]
  split_ifs <;> push_cast <;> omega

/-- The arrivals and the departures balance at every site: this is the statement that the
travel indicator jumps exactly at the two sites carrying a virtual event. -/
theorem balanced : t.Ap + t.Am + t.Bp + t.Bm = t.Cp + t.Cm + t.Dp + t.Dm := by
  have h1 := t.hpuL; have h2 := t.hpdL; have h3 := t.hpuR; have h4 := t.hpdR
  have h5 := t.hfL; have h6 := t.hfR
  have hb : travel t.kstar (t.s - 1) + (if t.s = 0 then (1 : ℤ) else 0)
      = travel t.kstar t.s + (if t.s = t.kstar then (1 : ℤ) else 0) :=
    (travel_site_facts t.kstar t.s _ _ _ _ rfl rfl rfl rfl).1
  simp only [Ap, Am, Bp, Bm, Cp, Cm, Dp, Dm, vA, vL, vR, vD, epsP, epsM]
  split_ifs at hb ⊢ <;> omega

/-- **The inequality of `cor:localcost`.**  `|Phi_s| <= min(|alpha_s|,|beta_s|)` at every site
of a realisation, the two sites carrying a virtual event included. -/
theorem Phi_le_min :
    (Phi t.Ap t.Am t.Cp t.Cm).natAbs ≤
      min (alpha t.Ap t.Am t.Cp t.Cm).natAbs (beta t.Bp t.Bm t.Dp t.Dm).natAbs := by
  obtain ⟨hbal, hfLc, hfRc, hac, hvc, hboth⟩ :=
    travel_site_facts t.kstar t.s (t.vA : ℤ) (t.vD : ℤ) t.fL t.fR t.vA_cast t.vD_cast rfl rfl
  have hpL : (t.dL - t.fL) % 2 = 0 := by
    have := t.hfL; simp only [dL, fL]; omega
  have hpR : (t.dR - t.fR) % 2 = 0 := by
    have := t.hfR; simp only [dR, fR]; omega
  rw [t.alpha_eq, t.beta_eq, t.Phi_eq]
  exact Phi_le_min_core t.dL t.dR t.fL t.fR t.vA t.vD t.vL t.vR t.eps
    hfLc hfRc hbal hac hvc hboth t.split t.heps hpL hpR

/-! ### The site cost -/

/-- **Corollary `cor:localcost`.**  The minimum pairing cost at a site of a realisation of
Definition `def:pairing` is `max(|alpha_s|,|beta_s|)`, at every site, the two sites carrying a
virtual event included. -/
theorem site_cost :
    IsLeast {n : ℕ | ∃ p : Plan t.Ap t.Am t.Bp t.Bm t.Cp t.Cm t.Dp t.Dm, p.cost = n} t.cost := by
  have hv := transport_min t.Ap t.Am t.Bp t.Bm t.Cp t.Cm t.Dp t.Dm t.balanced
  rwa [siteCost_eq _ _ _ _ _ _ _ _ t.Phi_le_min, t.alpha_eq, t.beta_eq] at hv

/-- **`cor:localcost`, the independence clause.**  Two sites with the same displacement, the
same site index, the same marker data and the same two deposits have the same minimum pairing
cost, whatever their crossing counts, their sign splits and their travel indicators. -/
theorem cost_indep (t t' : MarkedSite) (hk : t.kstar = t'.kstar) (hs : t.s = t'.s)
    (he : t.eps = t'.eps) (hd : t.delta = t'.delta) (hdL : t.dL = t'.dL) (hdR : t.dR = t'.dR) :
    t.cost = t'.cost := by
  simp only [cost, vA, vL, vR, vD, hk, hs, he, hd, hdL, hdR]

/-- **`cor:localcost`, interior case.**  At a site carrying no virtual event the minimum
pairing cost is `max(|d_{s-1}|,|d_s|)`. -/
theorem cost_interior (h0 : t.s ≠ 0) (hk : t.s ≠ t.kstar) :
    t.cost = max t.dL.natAbs t.dR.natAbs := by
  have hA : t.vA = 0 := by simp [vA, h0]
  have hD : t.vD = 0 := by simp [vD, hk]
  have hL : t.vL = 0 := by simp [vL, hD]
  have hR : t.vR = 0 := by simp [vR, hD]
  simp [cost, hA, hL, hR]

/-! ### Corollary `cor:marker`: the two junctions -/

/-- **Corollary `cor:marker`, the near junction.**  At site `0`, with `k^* /= 0` so that the
virtual departure sits elsewhere, the cost is `max(|d_L - 1|,|d_R|)` for all four marker data:
it depends on the sign of the last bulk deposit, not on its magnitude alone. -/
theorem cost_marker_near (h0 : t.s = 0) (hk : t.kstar ≠ 0) :
    t.cost = max (t.dL - 1).natAbs t.dR.natAbs := by
  have hA : t.vA = 1 := by simp [vA, h0]
  have hD : t.vD = 0 := by simp [vD, h0, Ne.symm hk]
  have hL : t.vL = 0 := by simp [vL, hD]
  have hR : t.vR = 0 := by simp [vR, hD]
  simp [cost, hA, hL, hR]

/-- **Corollary `cor:marker`, the far junction, `delta^* = 0`.**  At site `k^* /= 0` the cost is
`max(|d_L + eps^*|,|d_R|)`. -/
theorem cost_marker_far_left (hk : t.s = t.kstar) (h0 : t.kstar ≠ 0) (hd : t.delta = false) :
    t.cost = max (t.dL + t.eps).natAbs t.dR.natAbs := by
  have hA : t.vA = 0 := by simp [vA, hk, h0]
  have hD : t.vD = 1 := by simp [vD, hk]
  have hL : t.vL = 1 := by simp [vL, hd, hD]
  have hR : t.vR = 0 := by simp [vR, hd]
  simp [cost, hA, hL, hR]

/-- **Corollary `cor:marker`, the far junction, `delta^* = 1`.**  At site `k^* /= 0` the cost is
`max(|d_L|,|d_R - eps^*|)`. -/
theorem cost_marker_far_right (hk : t.s = t.kstar) (h0 : t.kstar ≠ 0) (hd : t.delta = true) :
    t.cost = max t.dL.natAbs (t.dR - t.eps).natAbs := by
  have hA : t.vA = 0 := by simp [vA, hk, h0]
  have hD : t.vD = 1 := by simp [vD, hk]
  have hL : t.vL = 0 := by simp [vL, hd]
  have hR : t.vR = 1 := by simp [vR, hd, hD]
  simp [cost, hA, hL, hR]

end MarkedSite

end SiteCost

#print axioms SiteCost.travel_cases
#print axioms SiteCost.travel_of_kstar_zero
#print axioms SiteCost.travel_site_facts
#print axioms SiteCost.Phi_le_min_core
#print axioms SiteCost.MarkedSite.alpha_eq
#print axioms SiteCost.MarkedSite.beta_eq
#print axioms SiteCost.MarkedSite.Phi_eq
#print axioms SiteCost.MarkedSite.balanced
#print axioms SiteCost.MarkedSite.Phi_le_min
#print axioms SiteCost.MarkedSite.site_cost
#print axioms SiteCost.MarkedSite.cost_indep
#print axioms SiteCost.MarkedSite.cost_interior
#print axioms SiteCost.MarkedSite.cost_marker_near
#print axioms SiteCost.MarkedSite.cost_marker_far_left
#print axioms SiteCost.MarkedSite.cost_marker_far_right
