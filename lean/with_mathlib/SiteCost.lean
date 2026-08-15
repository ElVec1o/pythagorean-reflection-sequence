/-
  SiteCost.lean
  =============
  The site cost of the pairing optimisation of `paper/journal/paper2.tex`, section 5.5
  (`sec:sitecost`).

  Formalised here:

  * `Plan`              Definition `def:pairing`, restricted to one site: the four-class
                        transportation problem with supplies `(A+,A-,B+,B-)` (the arrivals)
                        and demands `(C+,C-,D+,D-)` (the departures), classes
                        `0 = (L,+), 1 = (L,-), 2 = (R,+), 3 = (R,-)`, a matched pair costing
                        `0` on the same side with equal signs, `2` on the same side with
                        opposite signs and `1` on opposite sides.

  * `transport_min`     Lemma `lem:transport`: the minimum cost is `max (|a|,|b|,|F|)` with
                        `a = (C+ - C-) - (A+ - A-)`, `b = (B+ - B-) - (D+ - D-)`,
                        `F = (A+ + A-) - (C+ + C-)`.  Both halves are proved:
                        `cost_lower_bound` and `exists_plan_cost_eq`.

  * `siteCost_eq`       Corollary `cor:localcost`, the step that consumes `lem:transport`:
                        when `|F| <= min(|a|,|b|)` the value collapses to `max(|a|,|b|)`.

  * `alpha_eq_dL`, `beta_eq_dR`, `Phi_eq_fL`
                        Corollary `cor:localcost`, the read-off: the three quantities at a
                        site equal the left deposit, the right deposit and the left travel
                        indicator, so the site cost sees neither the crossing counts nor the
                        sign splits.

  * `interior_site_cost` the interior case of `cor:localcost`: `Site = max(|d_{s-1}|,|d_s|)`.

  * `marker_forms_agree`, `marker_forms_differ`
                        Remark `rem:markerfalse`: the earlier junction form
                        `max(|d_L| - 1, |d_R|)` agrees with `max(|d_L - 1|, |d_R|)` on
                        `d_L >= 0` and fails at `d_L = -2`, `d_R = 1` (true value `3`,
                        earlier form `1`).

  * `cut_forces_no_cross`
                        Proposition `prop:cut`, first sentence: at a cut site every
                        minimum-cost pairing matches every arrival on its own side.

  NOT formalised here: that the pairing optimisation computes the relaxed word length
  (Remark `rem:pairingstatus`, an input of paper 1, verified there and not proved), and the
  global statements `cor:lRclosed` and the counting half of `prop:cut`, which quantify over
  realisations of a whole edge path rather than over a single site.

  Everything below is finite integer arithmetic; every proof is closed by `omega` or
  `decide`, with no `sorry`.
-/

import Mathlib.Order.Bounds.Basic

namespace SiteCost

/-! ## The optimisation at one site -/

/-- A pairing at one site: `xIJ` is the number of class-`I` arrivals matched to class-`J`
departures, with `0 = (L,+)`, `1 = (L,-)`, `2 = (R,+)`, `3 = (R,-)`.  The eight equations
say that every arrival and every departure is matched exactly once. -/
structure Plan (Ap Am Bp Bm Cp Cm Dp Dm : ℕ) where
  x00 : ℕ
  x01 : ℕ
  x02 : ℕ
  x03 : ℕ
  x10 : ℕ
  x11 : ℕ
  x12 : ℕ
  x13 : ℕ
  x20 : ℕ
  x21 : ℕ
  x22 : ℕ
  x23 : ℕ
  x30 : ℕ
  x31 : ℕ
  x32 : ℕ
  x33 : ℕ
  row0 : x00 + x01 + x02 + x03 = Ap
  row1 : x10 + x11 + x12 + x13 = Am
  row2 : x20 + x21 + x22 + x23 = Bp
  row3 : x30 + x31 + x32 + x33 = Bm
  col0 : x00 + x10 + x20 + x30 = Cp
  col1 : x01 + x11 + x21 + x31 = Cm
  col2 : x02 + x12 + x22 + x32 = Dp
  col3 : x03 + x13 + x23 + x33 = Dm

variable {Ap Am Bp Bm Cp Cm Dp Dm : ℕ}

/-- The cost of a pairing: `0` for a same-side matched pair with equal signs, `2` for a
same-side pair with opposite signs, `1` for a pair on opposite sides. -/
def Plan.cost (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) : ℕ :=
  2 * (p.x01 + p.x10) + 2 * (p.x23 + p.x32)
    + (p.x02 + p.x03 + p.x12 + p.x13) + (p.x20 + p.x21 + p.x30 + p.x31)

/-- The number of matched pairs that cross from one side to the other. -/
def Plan.cross (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) : ℕ :=
  (p.x02 + p.x03 + p.x12 + p.x13) + (p.x20 + p.x21 + p.x30 + p.x31)

/-- `alpha = (C+ - C-) - (A+ - A-)`, the left sign imbalance. -/
def alpha (Ap Am Cp Cm : ℕ) : ℤ := ((Cp : ℤ) - Cm) - ((Ap : ℤ) - Am)

/-- `beta = (B+ - B-) - (D+ - D-)`, the right sign imbalance. -/
def beta (Bp Bm Dp Dm : ℕ) : ℤ := ((Bp : ℤ) - Bm) - ((Dp : ℤ) - Dm)

/-- `Phi = (A+ + A-) - (C+ + C-)`, the left flow imbalance. -/
def Phi (Ap Am Cp Cm : ℕ) : ℤ := ((Ap : ℤ) + Am) - ((Cp : ℤ) + Cm)

/-- `max (|alpha|, |beta|, |Phi|)`, the value of Lemma `lem:transport`. -/
def siteValue (Ap Am Bp Bm Cp Cm Dp Dm : ℕ) : ℕ :=
  max (max (alpha Ap Am Cp Cm).natAbs (beta Bp Bm Dp Dm).natAbs) (Phi Ap Am Cp Cm).natAbs

theorem alpha_natAbs_swap (Bp Bm Dp Dm : ℕ) :
    (alpha Bp Bm Dp Dm).natAbs = (beta Bp Bm Dp Dm).natAbs := by
  simp only [alpha, beta]; omega

/-! ## The lower bound

Each bound is a linear-programming dual certificate written out: for potentials `u` on the
arrival classes and `v` on the departure classes with `u i + v j <= cost i j`, every plan
costs at least `sum u i * a i + sum v j * b j`.  The six certificates are
`u = (-1,1,0,0), v = (1,-1,0,0)` and its negative for `+-alpha`;
`u = (0,0,1,-1), v = (0,0,-1,1)` and its negative for `+-beta`;
`u = (1,1,0,0), v = (-1,-1,0,0)` and its negative for `+-Phi`. -/

theorem cost_ge_alpha (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) :
    alpha Ap Am Cp Cm ≤ (p.cost : ℤ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_, r0, r1, r2, r3, c0, c1, c2, c3⟩ := p
  simp only [Plan.cost, alpha]; omega

theorem cost_ge_neg_alpha (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) :
    -alpha Ap Am Cp Cm ≤ (p.cost : ℤ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_, r0, r1, r2, r3, c0, c1, c2, c3⟩ := p
  simp only [Plan.cost, alpha]; omega

theorem cost_ge_beta (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) :
    beta Bp Bm Dp Dm ≤ (p.cost : ℤ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_, r0, r1, r2, r3, c0, c1, c2, c3⟩ := p
  simp only [Plan.cost, beta]; omega

theorem cost_ge_neg_beta (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) :
    -beta Bp Bm Dp Dm ≤ (p.cost : ℤ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_, r0, r1, r2, r3, c0, c1, c2, c3⟩ := p
  simp only [Plan.cost, beta]; omega

theorem cost_ge_Phi (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) :
    Phi Ap Am Cp Cm ≤ (p.cost : ℤ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_, r0, r1, r2, r3, c0, c1, c2, c3⟩ := p
  simp only [Plan.cost, Phi]; omega

theorem cost_ge_neg_Phi (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) :
    -Phi Ap Am Cp Cm ≤ (p.cost : ℤ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_, r0, r1, r2, r3, c0, c1, c2, c3⟩ := p
  simp only [Plan.cost, Phi]; omega

/-- **Lower-bound half of Lemma `lem:transport`.**  Every pairing at a site costs at least
`max (|alpha|, |beta|, |Phi|)`. -/
theorem cost_lower_bound (p : Plan Ap Am Bp Bm Cp Cm Dp Dm) :
    siteValue Ap Am Bp Bm Cp Cm Dp Dm ≤ p.cost := by
  have h1 := cost_ge_alpha p
  have h2 := cost_ge_neg_alpha p
  have h3 := cost_ge_beta p
  have h4 := cost_ge_neg_beta p
  have h5 := cost_ge_Phi p
  have h6 := cost_ge_neg_Phi p
  simp only [siteValue]
  omega

/-! ## Attainment

The construction in the proof of `lem:transport`: fix the total cross mass `P`, split the
mass staying on each side between the two signs as evenly as the supplies allow, and fill
the two cross blocks by the northwest-corner rule (every entry there costs `1`, so any
filling does). -/

/-- A same-side block.  `a` arrivals carry `+` and `a'` carry `-`; `c` departures carry `+`
and `c'` carry `-`; the totals agree.  The block can be filled so that exactly `mL` pairs
carry opposite signs, `mL` being `|a - c|` in the equational form `mL + c = a` or
`mL + a = c`. -/
theorem same_side_block (a a' c c' mL : ℕ) (h : a + a' = c + c')
    (hm : mL + c = a ∨ mL + a = c) :
    ∃ y00 y01 y10 y11 : ℕ,
      y00 + y01 = a ∧ y10 + y11 = a' ∧ y00 + y10 = c ∧ y01 + y11 = c' ∧
      y01 + y10 = mL :=
  ⟨min a c, a - c, c - a, min a' c', by omega, by omega, by omega, by omega, by omega⟩

/-- A cross block, filled by the northwest-corner rule; every entry there costs `1`, so any
filling does. -/
theorem cross_block (r1 r2 s1 s2 : ℕ) (h : r1 + r2 = s1 + s2) :
    ∃ y00 y01 y10 y11 : ℕ,
      y00 + y01 = r1 ∧ y10 + y11 = r2 ∧ y00 + y10 = s1 ∧ y01 + y11 = s2 :=
  ⟨min r1 s1, r1 - min r1 s1, s1 - min r1 s1, r2 - (s1 - min r1 s1),
    by omega, by omega, by omega, by omega⟩

/-- The gluing step, stated without any truncated subtraction.  Of the arrivals of class
`(L,+)`, `a1` stay on the left and `rAp` cross; and so on.  `piL` units cross from left to
right, `piR` from right to left, `mL` and `mR` are the two same-side sign mismatches.  Then
a pairing exists, of cost `2 mL + 2 mR + piL + piR` and cross mass `piL + piR`. -/
theorem exists_plan_of_split (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (a1 a1' c1 c1' b1 b1' d1 d1' : ℕ)
    (rAp rAm rBp rBm sCp sCm sDp sDm : ℕ) (piL piR mL mR : ℕ)
    (hA0 : a1 + rAp = Ap) (hA1 : a1' + rAm = Am)
    (hC0 : c1 + sCp = Cp) (hC1 : c1' + sCm = Cm)
    (hB0 : b1 + rBp = Bp) (hB1 : b1' + rBm = Bm)
    (hD0 : d1 + sDp = Dp) (hD1 : d1' + sDm = Dm)
    (hgL : a1 + a1' = c1 + c1') (hgR : b1 + b1' = d1 + d1')
    (hpiL1 : rAp + rAm = piL) (hpiL2 : sDp + sDm = piL)
    (hpiR1 : rBp + rBm = piR) (hpiR2 : sCp + sCm = piR)
    (hmL : mL + c1 = a1 ∨ mL + a1 = c1) (hmR : mR + d1 = b1 ∨ mR + b1 = d1) :
    ∃ p : Plan Ap Am Bp Bm Cp Cm Dp Dm,
      p.cost = 2 * mL + 2 * mR + piL + piR ∧ p.cross = piL + piR := by
  obtain ⟨l00, l01, l10, l11, m1, m2, m3, m4, m5⟩ :=
    same_side_block a1 a1' c1 c1' mL hgL hmL
  obtain ⟨n22, n23, n32, n33, k1, k2, k3, k4, k5⟩ :=
    same_side_block b1 b1' d1 d1' mR hgR hmR
  obtain ⟨e02, e03, e12, e13, u1, u2, u3, u4⟩ :=
    cross_block rAp rAm sDp sDm (by omega)
  obtain ⟨e20, e21, e30, e31, w1, w2, w3, w4⟩ :=
    cross_block rBp rBm sCp sCm (by omega)
  refine ⟨{ x00 := l00, x01 := l01, x02 := e02, x03 := e03,
            x10 := l10, x11 := l11, x12 := e12, x13 := e13,
            x20 := e20, x21 := e21, x22 := n22, x23 := n23,
            x30 := e30, x31 := e31, x32 := n32, x33 := n33,
            row0 := by omega, row1 := by omega, row2 := by omega, row3 := by omega,
            col0 := by omega, col1 := by omega, col2 := by omega,
            col3 := by omega }, ?_, ?_⟩ <;>
    simp only [Plan.cost, Plan.cross] <;> omega

/-- The two feasible intervals for the sign split on one side are non-empty, and the
canonical choice lies in them. -/
theorem split_bounds (Ap Am Cp Cm gL piL piR a1 c1 : ℕ)
    (hgL1 : gL + piL = Ap + Am) (hgL2 : gL + piR = Cp + Cm)
    (ha1 : a1 = min (min Ap gL) (max (gL - Am) (gL - Cm)))
    (hc1 : c1 = min (min Cp gL) (max (gL - Am) (gL - Cm))) :
    a1 ≤ Ap ∧ gL ≤ a1 + Am ∧ a1 ≤ gL ∧ c1 ≤ Cp ∧ gL ≤ c1 + Cm ∧ c1 ≤ gL := by
  omega

/-- Twice the minimal same-side mismatch on one side is `(|alpha| - P)` truncated at `0`,
with `P = piL + piR` the total cross mass. -/
theorem sep_eq (Ap Am Cp Cm gL piL piR a1 c1 : ℕ)
    (hgL1 : gL + piL = Ap + Am) (hgL2 : gL + piR = Cp + Cm)
    (ha1 : a1 = min (min Ap gL) (max (gL - Am) (gL - Cm)))
    (hc1 : c1 = min (min Cp gL) (max (gL - Am) (gL - Cm))) :
    2 * (max a1 c1 - min a1 c1) = (alpha Ap Am Cp Cm).natAbs - (piL + piR) := by
  simp only [alpha]; omega

/-- The admissible cross mass, in the abstract: `NaL, NdL, NaR, NdR` are the four
arrival/departure totals, `F = |Phi|`, and `A`, `B` bound the two sign imbalances and carry
the parity of `F`.  Then `P = max (F, min (A,B))` splits into `piL` units crossing left to
right and `piR` crossing right to left, leaving `gL` and `gR` in place. -/
theorem split_exists (NaL NdL NaR NdR A B F P : ℕ)
    (hbal : NaL + NaR = NdL + NdR)
    (hF : F + NdL = NaL ∨ F + NaL = NdL)
    (hA : A ≤ NaL + NdL) (hB : B ≤ NaR + NdR)
    (hpar : (A + F) % 2 = 0) (hparB : (B + F) % 2 = 0)
    (hP : P = max F (min A B)) :
    ∃ gL gR piL piR : ℕ,
      gL + piL = NaL ∧ gL + piR = NdL ∧ gR + piR = NaR ∧ gR + piL = NdR ∧
      piL + piR = P := by
  refine ⟨NaL - (P + NaL - NdL) / 2, NaR - (P + NdL - NaL) / 2,
          (P + NaL - NdL) / 2, (P + NdL - NaL) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The canonical sign split on one side, packaged so that only subtraction-free facts and
the single cost equation leave the lemma. -/
theorem split_choice (Ap Am Cp Cm gL piL piR : ℕ)
    (hgL1 : gL + piL = Ap + Am) (hgL2 : gL + piR = Cp + Cm) :
    ∃ a1 c1 mL : ℕ,
      a1 ≤ Ap ∧ gL ≤ a1 + Am ∧ a1 ≤ gL ∧ c1 ≤ Cp ∧ gL ≤ c1 + Cm ∧ c1 ≤ gL ∧
      (mL + c1 = a1 ∨ mL + a1 = c1) ∧
      2 * mL = (alpha Ap Am Cp Cm).natAbs - (piL + piR) := by
  obtain ⟨a1, ha1⟩ : ∃ a1, a1 = min (min Ap gL) (max (gL - Am) (gL - Cm)) := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c1, c1 = min (min Cp gL) (max (gL - Am) (gL - Cm)) := ⟨_, rfl⟩
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ :=
    split_bounds Ap Am Cp Cm gL piL piR a1 c1 hgL1 hgL2 ha1 hc1
  exact ⟨a1, c1, max a1 c1 - min a1 c1, b1, b2, b3, b4, b5, b6, by omega,
    sep_eq Ap Am Cp Cm gL piL piR a1 c1 hgL1 hgL2 ha1 hc1⟩

/-- The final bookkeeping: `phi(P) = P + (|alpha| - P) + (|beta| - P)` at
`P = max (|Phi|, min (|alpha|,|beta|))` equals `max (|alpha|, |beta|, |Phi|)`. -/
theorem cost_value_eq (mL mR piL piR A B F : ℕ)
    (hmL : 2 * mL = A - (piL + piR)) (hmR : 2 * mR = B - (piR + piL))
    (h5 : piL + piR = max F (min A B)) :
    2 * mL + 2 * mR + piL + piR = max (max A B) F := by
  omega

set_option maxHeartbeats 1000000 in
/-- **Attainment half of Lemma `lem:transport`.**  Some pairing costs exactly
`max (|alpha|, |beta|, |Phi|)`, and its cross mass is `max (|Phi|, min (|alpha|,|beta|))`. -/
theorem exists_plan_cost_eq (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (hbal : Ap + Am + Bp + Bm = Cp + Cm + Dp + Dm) :
    ∃ p : Plan Ap Am Bp Bm Cp Cm Dp Dm,
      p.cost = siteValue Ap Am Bp Bm Cp Cm Dp Dm ∧
      p.cross = max (Phi Ap Am Cp Cm).natAbs
        (min (alpha Ap Am Cp Cm).natAbs (beta Bp Bm Dp Dm).natAbs) := by
  -- the inputs of `split_exists`
  have hF : (Phi Ap Am Cp Cm).natAbs + (Cp + Cm) = Ap + Am ∨
            (Phi Ap Am Cp Cm).natAbs + (Ap + Am) = Cp + Cm := by
    simp only [Phi]; omega
  have hA : (alpha Ap Am Cp Cm).natAbs ≤ (Ap + Am) + (Cp + Cm) := by
    simp only [alpha]; omega
  have hB : (beta Bp Bm Dp Dm).natAbs ≤ (Bp + Bm) + (Dp + Dm) := by
    simp only [beta]; omega
  have hpar : ((alpha Ap Am Cp Cm).natAbs + (Phi Ap Am Cp Cm).natAbs) % 2 = 0 := by
    simp only [alpha, Phi]; omega
  have hparB : ((beta Bp Bm Dp Dm).natAbs + (Phi Ap Am Cp Cm).natAbs) % 2 = 0 := by
    simp only [beta, Phi]; omega
  obtain ⟨gL, gR, piL, piR, h1, h2, h3, h4, h5⟩ :=
    split_exists (Ap + Am) (Cp + Cm) (Bp + Bm) (Dp + Dm)
      (alpha Ap Am Cp Cm).natAbs (beta Bp Bm Dp Dm).natAbs (Phi Ap Am Cp Cm).natAbs _
      (by omega) hF hA hB hpar hparB rfl
  clear hF hA hB hpar hparB hbal
  obtain ⟨a1, c1, mL, p1, p2, p3, p4, p5, p6, hmL', hmL⟩ :=
    split_choice Ap Am Cp Cm gL piL piR h1 h2
  obtain ⟨b1, d1, mR, q1, q2, q3, q4, q5, q6, hmR', hmR⟩ :=
    split_choice Bp Bm Dp Dm gR piR piL h3 h4
  rw [alpha_natAbs_swap] at hmR
  -- the eight complements, introduced without truncated subtraction
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
  refine ⟨p, ?_, ?_⟩
  · rw [hcost]
    simp only [siteValue]
    exact cost_value_eq mL mR piL piR _ _ _ hmL hmR h5
  · rw [hcross, h5]

/-- **Lemma `lem:transport` (the transportation value).**  The minimum cost of the
four-class transportation problem at a site is `max (|alpha|, |beta|, |Phi|)`. -/
theorem transport_min (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (hbal : Ap + Am + Bp + Bm = Cp + Cm + Dp + Dm) :
    IsLeast {n : ℕ | ∃ p : Plan Ap Am Bp Bm Cp Cm Dp Dm, p.cost = n}
      (siteValue Ap Am Bp Bm Cp Cm Dp Dm) := by
  obtain ⟨p, hp, -⟩ := exists_plan_cost_eq Ap Am Bp Bm Cp Cm Dp Dm hbal
  exact ⟨⟨p, hp⟩, by rintro n ⟨q, rfl⟩; exact cost_lower_bound q⟩

/-! ## Corollary `cor:localcost`: the local cost law -/

/-- The step of `cor:localcost` that consumes `lem:transport`: when the flow imbalance is
dominated by both sign imbalances, the site value is `max (|alpha|, |beta|)`, so it does not
see `Phi` at all. -/
theorem siteCost_eq (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (h : (Phi Ap Am Cp Cm).natAbs ≤
          min (alpha Ap Am Cp Cm).natAbs (beta Bp Bm Dp Dm).natAbs) :
    siteValue Ap Am Bp Bm Cp Cm Dp Dm =
      max (alpha Ap Am Cp Cm).natAbs (beta Bp Bm Dp Dm).natAbs := by
  simp only [siteValue]; omega

/-- **Proposition `prop:cut`, first sentence.**  At a cut site (`alpha = beta = Phi = 0`)
every minimum-cost pairing matches each arrival with a departure on its own side: no strand
crosses. -/
theorem cut_forces_no_cross (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (ha : alpha Ap Am Cp Cm = 0) (hb : beta Bp Bm Dp Dm = 0) (hf : Phi Ap Am Cp Cm = 0)
    (p : Plan Ap Am Bp Bm Cp Cm Dp Dm)
    (hmin : p.cost = siteValue Ap Am Bp Bm Cp Cm Dp Dm) : p.cross = 0 := by
  have hz : siteValue Ap Am Bp Bm Cp Cm Dp Dm = 0 := by
    simp [siteValue, ha, hb, hf]
  rw [hz] at hmin
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_, r0, r1, r2, r3, c0, c1, c2, c3⟩ := p
  simp only [Plan.cost] at hmin
  simp only [Plan.cross]
  omega

/-! ## The read-off from Definition `def:pairing` -/

/-- The crossing data of the two edges adjacent to one site, as in Definition
`def:pairing`: the left edge is crossed `uL` times upward, of which `puL` carry `+`, and
`dnL` times downward, of which `pdL` carry `+`; likewise on the right.  `hflow` is the
balance of arrivals against departures, which holds at a site carrying no virtual event. -/
structure SiteData where
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
  hflow : uL + dnR = dnL + uR

namespace SiteData

variable (s : SiteData)

/-- Arrivals of class `(L,+)`: the `+` up-crossings of the left edge. -/
def arrLp : ℕ := s.puL
/-- Arrivals of class `(L,-)`. -/
def arrLm : ℕ := s.uL - s.puL
/-- Arrivals of class `(R,+)`: the `+` down-crossings of the right edge. -/
def arrRp : ℕ := s.pdR
/-- Arrivals of class `(R,-)`. -/
def arrRm : ℕ := s.dnR - s.pdR
/-- Departures of class `(L,+)`: the `+` down-crossings of the left edge. -/
def depLp : ℕ := s.pdL
/-- Departures of class `(L,-)`. -/
def depLm : ℕ := s.dnL - s.pdL
/-- Departures of class `(R,+)`: the `+` up-crossings of the right edge. -/
def depRp : ℕ := s.puR
/-- Departures of class `(R,-)`. -/
def depRm : ℕ := s.uR - s.puR

/-- The deposit on the left edge, `d = 2 p^d - dn + u - 2 p^u`. -/
def dL : ℤ := 2 * (s.pdL : ℤ) - s.dnL + s.uL - 2 * s.puL
/-- The deposit on the right edge. -/
def dR : ℤ := 2 * (s.pdR : ℤ) - s.dnR + s.uR - 2 * s.puR
/-- The travel indicator of the left edge, `f = u - dn`. -/
def fL : ℤ := (s.uL : ℤ) - s.dnL

/-- **`cor:localcost`, read-off (i).**  The left sign imbalance is the left deposit; in
particular it does not depend on the crossing counts or on the sign splits except through
`d`. -/
theorem alpha_eq_dL : alpha s.arrLp s.arrLm s.depLp s.depLm = s.dL := by
  have h1 := s.hpuL; have h2 := s.hpdL
  simp only [alpha, arrLp, arrLm, depLp, depLm, dL]; omega

/-- **`cor:localcost`, read-off (ii).**  The right sign imbalance is the right deposit. -/
theorem beta_eq_dR : beta s.arrRp s.arrRm s.depRp s.depRm = s.dR := by
  have h1 := s.hpuR; have h2 := s.hpdR
  simp only [beta, arrRp, arrRm, depRp, depRm, dR]; omega

/-- **`cor:localcost`, read-off (iii).**  The flow imbalance is the left travel
indicator. -/
theorem Phi_eq_fL : Phi s.arrLp s.arrLm s.depLp s.depLm = s.fL := by
  have h1 := s.hpuL; have h2 := s.hpdL
  simp only [Phi, arrLp, arrLm, depLp, depLm, fL]; omega

theorem balanced :
    s.arrLp + s.arrLm + s.arrRp + s.arrRm = s.depLp + s.depLm + s.depRp + s.depRm := by
  have h1 := s.hpuL; have h2 := s.hpdL; have h3 := s.hpuR; have h4 := s.hpdR
  have h5 := s.hflow
  simp only [arrLp, arrLm, arrRp, arrRm, depLp, depLm, depRp, depRm]; omega

/-- **Corollary `cor:localcost`, interior case.**  At a site carrying no virtual event the
minimum pairing cost is `max (|d_{s-1}|, |d_s|)`: it depends on the two deposits alone, not
on the crossing counts and not on the sign splits.  The hypothesis is the inequality
`|f| <= min (|d_L|, |d_R|)` verified in `cor:localcost`; at an interior site it says that a
bulk deposit is even with `f = 0` and a travel deposit is odd with `|f| = 1`. -/
theorem interior_site_cost (h : s.fL.natAbs ≤ min s.dL.natAbs s.dR.natAbs) :
    IsLeast {n : ℕ | ∃ p : Plan s.arrLp s.arrLm s.arrRp s.arrRm s.depLp s.depLm s.depRp s.depRm,
        p.cost = n} (max s.dL.natAbs s.dR.natAbs) := by
  have hv := transport_min s.arrLp s.arrLm s.arrRp s.arrRm s.depLp s.depLm s.depRp s.depRm
      s.balanced
  have hcond : (Phi s.arrLp s.arrLm s.depLp s.depLm).natAbs ≤
      min (alpha s.arrLp s.arrLm s.depLp s.depLm).natAbs
          (beta s.arrRp s.arrRm s.depRp s.depRm).natAbs := by
    rw [s.alpha_eq_dL, s.beta_eq_dR, s.Phi_eq_fL]; exact h
  rwa [siteCost_eq _ _ _ _ _ _ _ _ hcond, s.alpha_eq_dL, s.beta_eq_dR] at hv

end SiteData

/-! ## Remark `rem:markerfalse`: the earlier marker form -/

/-- The earlier junction form `max(|d_L| - 1, |d_R|)` agrees with the correct form
`max(|d_L - 1|, |d_R|)` whenever the last bulk deposit is non-negative and the first travel
deposit is non-zero (it is odd, hence non-zero). -/
theorem marker_forms_agree (dL dR : ℤ) (h : 0 ≤ dL) (hR : 1 ≤ dR.natAbs) :
    max (dL - 1).natAbs dR.natAbs = max (dL.natAbs - 1) dR.natAbs := by
  omega

/-- The earlier form is nevertheless false: at `d_L = -2`, `d_R = 1` the correct value is
`3` and the earlier form gives `1`.  This is the smallest counterexample of Remark
`rem:markerfalse`. -/
theorem marker_forms_differ :
    max ((-2 : ℤ) - 1).natAbs (1 : ℤ).natAbs = 3 ∧
    max ((-2 : ℤ).natAbs - 1) (1 : ℤ).natAbs = 1 := by
  decide

end SiteCost

-- Axiom audit: no `sorry`, only Lean's foundational axioms (or none at all, which is the
-- legitimate output for a goal closed by `decide`, `rfl` or `omega`'s certificate checker).
#print axioms SiteCost.cost_lower_bound
#print axioms SiteCost.same_side_block
#print axioms SiteCost.cross_block
#print axioms SiteCost.exists_plan_of_split
#print axioms SiteCost.split_bounds
#print axioms SiteCost.sep_eq
#print axioms SiteCost.split_exists
#print axioms SiteCost.split_choice
#print axioms SiteCost.cost_value_eq
#print axioms SiteCost.exists_plan_cost_eq
#print axioms SiteCost.transport_min
#print axioms SiteCost.siteCost_eq
#print axioms SiteCost.cut_forces_no_cross
#print axioms SiteCost.SiteData.alpha_eq_dL
#print axioms SiteCost.SiteData.beta_eq_dR
#print axioms SiteCost.SiteData.Phi_eq_fL
#print axioms SiteCost.SiteData.balanced
#print axioms SiteCost.SiteData.interior_site_cost
#print axioms SiteCost.marker_forms_agree
#print axioms SiteCost.marker_forms_differ
