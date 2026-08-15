/-
  CutCross.lean
  =============
  The middle sentence of Proposition `prop:cut` of `paper/journal/paper2.tex`: at an interior
  site of the span which is *not* cut, some minimum-cost pairing lets a strand cross.

  `SiteCost.exists_plan_cost_eq` exhibits a minimum-cost pairing of cross mass
  `max(|Phi|, min(|alpha|,|beta|))`, which settles every case except
  `min(|alpha|,|beta|) = 0` with `Phi = 0`.  There the paper's argument runs the construction at
  the cross mass `P = 2` instead, which is admissible because the two caps `m_{s-1}, m_s` of
  Lemma `lem:transport` are at least `2`; that is not local to the site, and is the reason this
  file works over a `Realisation` rather than over a `Plan`.

  Formalised here:

  * `split_exists_adm`      the mass split of Lemma `lem:transport` at an arbitrary admissible
                            cross mass `P`, in place of the single value `max(F, min(A,B))`
                            used by `SiteCost.split_exists`;
  * `exists_plan_of_cross`  the attainment half of Lemma `lem:transport` at an arbitrary
                            admissible `P`: a pairing of cost `P + (|alpha|-P)^+ + (|beta|-P)^+`
                            and cross mass exactly `P`;
  * `exists_min_plan_cross` the site-level statement: at a site which is not cut, and whose two
                            caps are at least `2` when `Phi = 0`, some minimum-cost pairing has
                            positive cross mass;
  * `Realisation.capL_two`, `Realisation.capR_two`
                            the two caps, discharged on the span: an edge with `f = 0` carries at
                            least `2` crossings, and an edge with `|f| = 1` is accompanied by a
                            virtual event on its side, which supplies the missing unit;
  * `Realisation.exists_cross_of_not_cut`
                            Proposition `prop:cut`, middle sentence.

  Everything is finite integer arithmetic; every proof is closed by `omega`, with no `sorry`.
-/

import Realisation

namespace SiteCost

/-! ## The mass split at a prescribed cross mass -/

/-- The split of `SiteCost.split_exists`, at an arbitrary admissible cross mass `P` rather than
at the single value `max(F, min(A,B))`.  `P` is admissible when it dominates the flow imbalance
`F`, carries its parity, and does not exceed either of the two caps. -/
theorem split_exists_adm (NaL NdL NaR NdR F P : ℕ)
    (hbal : NaL + NaR = NdL + NdR)
    (hF : F + NdL = NaL ∨ F + NaL = NdL)
    (hFP : F ≤ P) (hpar : (P + F) % 2 = 0)
    (hPL : P ≤ NaL + NdL) (hPR : P ≤ NaR + NdR) :
    ∃ gL gR piL piR : ℕ,
      gL + piL = NaL ∧ gL + piR = NdL ∧ gR + piR = NaR ∧ gR + piL = NdR ∧
      piL + piR = P := by
  refine ⟨NaL - (P + NaL - NdL) / 2, NaR - (P + NdL - NaL) / 2,
          (P + NaL - NdL) / 2, (P + NdL - NaL) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The bookkeeping of the attainment step at a prescribed cross mass:
`phi(P) = P + (|alpha| - P)^+ + (|beta| - P)^+`. -/
theorem cost_value_of_cross (mL mR piL piR A B P : ℕ)
    (hmL : 2 * mL = A - (piL + piR)) (hmR : 2 * mR = B - (piR + piL))
    (h5 : piL + piR = P) :
    2 * mL + 2 * mR + piL + piR = P + (A - P) + (B - P) := by
  omega

set_option maxHeartbeats 1000000 in
/-- **The attainment half of Lemma `lem:transport` at a prescribed cross mass.**  For every
admissible `P` there is a pairing of cost `phi(P) = P + (|alpha|-P)^+ + (|beta|-P)^+` whose cross
mass is exactly `P`.  Taking `P = max(|Phi|, min(|alpha|,|beta|))` recovers
`SiteCost.exists_plan_cost_eq`. -/
theorem exists_plan_of_cross (Ap Am Bp Bm Cp Cm Dp Dm P : ℕ)
    (hbal : Ap + Am + Bp + Bm = Cp + Cm + Dp + Dm)
    (hFP : (Phi Ap Am Cp Cm).natAbs ≤ P)
    (hpar : (P + (Phi Ap Am Cp Cm).natAbs) % 2 = 0)
    (hPL : P ≤ Ap + Am + Cp + Cm) (hPR : P ≤ Bp + Bm + Dp + Dm) :
    ∃ p : Plan Ap Am Bp Bm Cp Cm Dp Dm,
      p.cost = P + ((alpha Ap Am Cp Cm).natAbs - P) + ((beta Bp Bm Dp Dm).natAbs - P) ∧
      p.cross = P := by
  have hF : (Phi Ap Am Cp Cm).natAbs + (Cp + Cm) = Ap + Am ∨
            (Phi Ap Am Cp Cm).natAbs + (Ap + Am) = Cp + Cm := by
    simp only [Phi]; omega
  obtain ⟨gL, gR, piL, piR, h1, h2, h3, h4, h5⟩ :=
    split_exists_adm (Ap + Am) (Cp + Cm) (Bp + Bm) (Dp + Dm) (Phi Ap Am Cp Cm).natAbs P
      (by omega) hF hFP hpar (by omega) (by omega)
  clear hF hFP hpar hPL hPR hbal
  obtain ⟨a1, c1, mL, p1, p2, p3, p4, p5, p6, hmL', hmL⟩ :=
    split_choice Ap Am Cp Cm gL piL piR h1 h2
  obtain ⟨b1, d1, mR, q1, q2, q3, q4, q5, q6, hmR', hmR⟩ :=
    split_choice Bp Bm Dp Dm gR piR piL h3 h4
  rw [alpha_natAbs_swap] at hmR
  obtain ⟨a1', hA1⟩ : ∃ t, a1 + t = gL := ⟨gL - a1, by omega⟩
  obtain ⟨c1', hC1⟩ : ∃ t, c1 + t = gL := ⟨gL - c1, by omega⟩
  obtain ⟨b1', hB1⟩ : ∃ t, b1 + t = gR := ⟨gR - b1, by omega⟩
  obtain ⟨d1', hD1⟩ : ∃ t, d1 + t = gR := ⟨gR - d1, by omega⟩
  obtain ⟨rAp, e1⟩ : ∃ t, a1 + t = Ap := ⟨Ap - a1, by omega⟩
  obtain ⟨rAm, e2⟩ : ∃ t, a1' + t = Am := ⟨Am - a1', by omega⟩
  obtain ⟨sCp, e3⟩ : ∃ t, c1 + t = Cp := ⟨Cp - c1, by omega⟩
  obtain ⟨sCm, e4⟩ : ∃ t, c1' + t = Cm := ⟨Cm - c1', by omega⟩
  obtain ⟨rBp, e5⟩ : ∃ t, b1 + t = Bp := ⟨Bp - b1, by omega⟩
  obtain ⟨rBm, e6⟩ : ∃ t, b1' + t = Bm := ⟨Bm - b1', by omega⟩
  obtain ⟨sDp, e7⟩ : ∃ t, d1 + t = Dp := ⟨Dp - d1, by omega⟩
  obtain ⟨sDm, e8⟩ : ∃ t, d1' + t = Dm := ⟨Dm - d1', by omega⟩
  have f1 : a1 + a1' = c1 + c1' := by omega
  have f2 : b1 + b1' = d1 + d1' := by omega
  have f3 : rAp + rAm = piL := by omega
  have f4 : sDp + sDm = piL := by omega
  have f5 : rBp + rBm = piR := by omega
  have f6 : sCp + sCm = piR := by omega
  obtain ⟨p, hcost, hcross⟩ :=
    exists_plan_of_split Ap Am Bp Bm Cp Cm Dp Dm a1 a1' c1 c1' b1 b1' d1 d1'
      rAp rAm rBp rBm sCp sCm sDp sDm piL piR mL mR
      e1 e2 e3 e4 e5 e6 e7 e8 f1 f2 f3 f4 f5 f6 hmL' hmR'
  refine ⟨p, ?_, by rw [hcross, h5]⟩
  rw [hcost]
  exact cost_value_of_cross mL mR piL piR _ _ _ hmL hmR h5

/-! ## The site-level statement -/

/-- **Proposition `prop:cut`, middle sentence, at one site.**  At a site which is not cut some
minimum-cost pairing lets a strand cross.  The two cap hypotheses are needed only in the case
`Phi = 0` and `min(|alpha|,|beta|) = 0`, where the cross mass has to be forced up to `2`. -/
theorem exists_min_plan_cross (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (hbal : Ap + Am + Bp + Bm = Cp + Cm + Dp + Dm)
    (hphi : (Phi Ap Am Cp Cm).natAbs ≤
      min (alpha Ap Am Cp Cm).natAbs (beta Bp Bm Dp Dm).natAbs)
    (hne : ¬(alpha Ap Am Cp Cm = 0 ∧ beta Bp Bm Dp Dm = 0 ∧ Phi Ap Am Cp Cm = 0))
    (hcapL : Phi Ap Am Cp Cm = 0 → 2 ≤ Ap + Am + Cp + Cm)
    (hcapR : Phi Ap Am Cp Cm = 0 → 2 ≤ Bp + Bm + Dp + Dm) :
    ∃ p : Plan Ap Am Bp Bm Cp Cm Dp Dm,
      p.cost = siteValue Ap Am Bp Bm Cp Cm Dp Dm ∧ p.cross ≠ 0 := by
  have hpa : ((alpha Ap Am Cp Cm).natAbs + (Phi Ap Am Cp Cm).natAbs) % 2 = 0 := by
    simp only [alpha, Phi]; omega
  have hpb : ((beta Bp Bm Dp Dm).natAbs + (Phi Ap Am Cp Cm).natAbs) % 2 = 0 := by
    simp only [beta, Phi]; omega
  have hval : siteValue Ap Am Bp Bm Cp Cm Dp Dm =
      max (alpha Ap Am Cp Cm).natAbs (beta Bp Bm Dp Dm).natAbs :=
    siteCost_eq _ _ _ _ _ _ _ _ hphi
  by_cases hmin : min (alpha Ap Am Cp Cm).natAbs (beta Bp Bm Dp Dm).natAbs = 0
  · have hPhi0 : Phi Ap Am Cp Cm = 0 := by omega
    have hAB : (alpha Ap Am Cp Cm).natAbs ≠ 0 ∨ (beta Bp Bm Dp Dm).natAbs ≠ 0 := by
      rcases eq_or_ne (alpha Ap Am Cp Cm) 0 with ha | ha
      · rcases eq_or_ne (beta Bp Bm Dp Dm) 0 with hb | hb
        · exact absurd ⟨ha, hb, hPhi0⟩ hne
        · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    obtain ⟨p, hc, hx⟩ :=
      exists_plan_of_cross Ap Am Bp Bm Cp Cm Dp Dm 2 hbal (by omega) (by omega)
        (hcapL hPhi0) (hcapR hPhi0)
    exact ⟨p, by rw [hc, hval]; omega, by omega⟩
  · obtain ⟨p, hc, hx⟩ := exists_plan_cost_eq Ap Am Bp Bm Cp Cm Dp Dm hbal
    exact ⟨p, hc, by rw [hx]; omega⟩

/-! ## The two caps of a site of a realisation -/

namespace MarkedSite

/-- The left cap of Lemma `lem:transport` at a site: the crossing count of the left edge,
augmented by one for each virtual event of the site sitting on the left. -/
theorem capL_eq (t : MarkedSite) : t.Ap + t.Am + t.Cp + t.Cm = t.uL + t.dnL + t.vA + t.vL := by
  have h1 := t.hpuL; have h2 := t.hpdL
  simp only [Ap, Am, Cp, Cm, epsP, epsM]
  split_ifs <;> omega

/-- The right cap: the crossing count of the right edge, augmented by one for a virtual
departure of the site sitting on the right. -/
theorem capR_eq (t : MarkedSite) : t.Bp + t.Bm + t.Dp + t.Dm = t.uR + t.dnR + t.vR := by
  have h1 := t.hpuR; have h2 := t.hpdR
  simp only [Bp, Bm, Dp, Dm, epsP, epsM]
  split_ifs <;> omega

end MarkedSite

namespace PathData

variable (P : PathData)

/-- An edge of the span with vanishing travel indicator carries at least two crossings: either
its deposit vanishes too and the support condition forces `2`, or its deposit is even and
non-zero. -/
theorem two_le_mu_of_travel_zero (j : ℤ) (h : travel P.kstar j = 0) : 2 ≤ P.mu j := by
  have hp := P.hpar j
  rw [h] at hp
  simp only [mu, h, and_true]
  split_ifs with hc <;> omega

/-- The virtual departure sits on the left or on the right, never both. -/
theorem vD_split (s : ℤ) : P.vD s = P.vL s + P.vR s := by
  simp only [vL, vR]; split_ifs <;> omega

/-- `Phi_s = f_s + [s = k^*][delta^* = 1]`, the second reading of the flow imbalance: the travel
indicator of the *right* edge, augmented by a virtual departure sitting on the right. -/
theorem PhiAt_right (s : ℤ) : P.PhiAt s = travel P.kstar s + P.vR s := by
  have hb := (travel_site_facts P.kstar s (vArr s : ℤ) (P.vD s : ℤ)
    (travel P.kstar (s - 1)) (travel P.kstar s)
    (by simp only [vArr]; split_ifs <;> simp) (by simp only [vD]; split_ifs <;> simp)
    rfl rfl).1
  have hs := P.vD_split s
  simp only [PhiAt, f]
  omega

end PathData

/-! ## The caps on the span -/

namespace Realisation

variable {P : PathData} (R : Realisation P)

/-- The left cap of a site interior to the span is at least `2` when the flow imbalance
vanishes: either the left edge has no travel and then carries at least two crossings, or it has
travel and the vanishing of `Phi_s` forces a virtual event of `s` on the left. -/
theorem capL_two (s : ℤ) (h1 : P.A ≤ s - 1) (h2 : s - 1 ≤ P.B) (hPhi : P.PhiAt s = 0) :
    2 ≤ (R.site s).Ap + (R.site s).Am + (R.site s).Cp + (R.site s).Cm := by
  rw [MarkedSite.capL_eq]
  have e1 : (R.site s).uL = R.u (s - 1) := rfl
  have e2 : (R.site s).dnL = R.dn (s - 1) := rfl
  have e3 : (R.site s).vA = vArr s := rfl
  have e4 : (R.site s).vL = P.vL s := rfl
  rw [e1, e2, e3, e4]
  have hm : P.mu (s - 1) ≤ R.m (s - 1) :=
    R.m_ge ⟨le_trans R.span_le.1 h1, le_trans h2 R.span_le.2⟩
  simp only [m] at hm
  simp only [PathData.PhiAt, PathData.f] at hPhi
  rcases travel_cases P.kstar (s - 1) with h | h | h
  · have := P.two_le_mu_of_travel_zero (s - 1) h
    omega
  · have hf := P.mu_ge_f (s - 1)
    rw [h] at hf hPhi
    omega
  · have hf := P.mu_ge_f (s - 1)
    rw [h] at hf hPhi
    omega

/-- The right cap of a site interior to the span is at least `2` when the flow imbalance
vanishes. -/
theorem capR_two (s : ℤ) (h1 : P.A ≤ s) (h2 : s ≤ P.B) (hPhi : P.PhiAt s = 0) :
    2 ≤ (R.site s).Bp + (R.site s).Bm + (R.site s).Dp + (R.site s).Dm := by
  rw [MarkedSite.capR_eq]
  have e1 : (R.site s).uR = R.u s := rfl
  have e2 : (R.site s).dnR = R.dn s := rfl
  have e3 : (R.site s).vR = P.vR s := rfl
  rw [e1, e2, e3]
  have hm : P.mu s ≤ R.m s := R.m_ge ⟨le_trans R.span_le.1 h1, le_trans h2 R.span_le.2⟩
  simp only [m] at hm
  rw [P.PhiAt_right s] at hPhi
  rcases travel_cases P.kstar s with h | h | h
  · have := P.two_le_mu_of_travel_zero s h
    omega
  · have hf := P.mu_ge_f s
    rw [h] at hf hPhi
    omega
  · have hf := P.mu_ge_f s
    rw [h] at hf hPhi
    omega

/-- **Proposition `prop:cut`, middle sentence.**  At an interior site of the span which is not
cut, some minimum-cost pairing lets a strand cross. -/
theorem exists_cross_of_not_cut (s : ℤ) (hs1 : P.A + 1 ≤ s) (hs2 : s ≤ P.B)
    (hcut : ¬ P.cut s) :
    ∃ p : PlanAt (R.site s), p.cost = P.siteCost s ∧ p.cross ≠ 0 := by
  have hphi := MarkedSite.Phi_le_min (R.site s)
  have hval : siteValue (R.site s).Ap (R.site s).Am (R.site s).Bp (R.site s).Bm
      (R.site s).Cp (R.site s).Cm (R.site s).Dp (R.site s).Dm = P.siteCost s := by
    rw [siteCost_eq _ _ _ _ _ _ _ _ hphi, R.site_alpha, R.site_beta]; rfl
  have hne : ¬(alpha (R.site s).Ap (R.site s).Am (R.site s).Cp (R.site s).Cm = 0 ∧
      beta (R.site s).Bp (R.site s).Bm (R.site s).Dp (R.site s).Dm = 0 ∧
      Phi (R.site s).Ap (R.site s).Am (R.site s).Cp (R.site s).Cm = 0) := by
    rw [R.site_alpha, R.site_beta, R.site_Phi]; exact hcut
  obtain ⟨p, hc, hx⟩ :=
    exists_min_plan_cross (R.site s).Ap (R.site s).Am (R.site s).Bp (R.site s).Bm
      (R.site s).Cp (R.site s).Cm (R.site s).Dp (R.site s).Dm
      (MarkedSite.balanced _) hphi hne
      (fun h => R.capL_two s (by omega) (by omega) (by rw [← R.site_Phi]; exact h))
      (fun h => R.capR_two s (by omega) (by omega) (by rw [← R.site_Phi]; exact h))
  exact ⟨p, by rw [hc, hval], hx⟩

end Realisation

end SiteCost

#print axioms SiteCost.split_exists_adm
#print axioms SiteCost.cost_value_of_cross
#print axioms SiteCost.exists_plan_of_cross
#print axioms SiteCost.exists_min_plan_cross
#print axioms SiteCost.MarkedSite.capL_eq
#print axioms SiteCost.MarkedSite.capR_eq
#print axioms SiteCost.PathData.two_le_mu_of_travel_zero
#print axioms SiteCost.PathData.vD_split
#print axioms SiteCost.PathData.PhiAt_right
#print axioms SiteCost.Realisation.capL_two
#print axioms SiteCost.Realisation.capR_two
#print axioms SiteCost.Realisation.exists_cross_of_not_cut
