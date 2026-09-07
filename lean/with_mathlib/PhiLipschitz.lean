/-
  PhiLipschitz.lean
  =================
  Toward the open half of the metric identity.

  The lower bound of `l_T = l_R + 2c` is open.  It follows by induction on `Reaches` from
  ONE statement: that the corrected potential

      Phi g = lRTrue g + 2 * cTrue g

  moves by at most `1` along every generator.  That is measured true -- max jump exactly
  `1` on a depth-30 ball and on a 370500-element exhaustive sweep, with `0` violations of
  the identity itself to depth 29 (BLOCK 343/347) -- but is not proved.

  The naive route fails and it is worth recording why: the site sum moves by at most `1`
  and `cTrue` by at most `2` (one cut site, one boundary shield), so summing the parts
  gives `5`, not `1`.  The bound therefore needs an exact CANCELLATION between the site
  cost and the defect, not better bookkeeping on each.

  This file isolates the `s1`/`s2` half, where the geometry is fully pinned:
  `CorrectedSpan` already shows those two generators fix the span and the whole `mu` sum,
  so all movement sits at the single site `kstar`.  `siteSum_sub_eq_at_kstar` below reduces
  the site sum to that one site exactly, which is the shape the cancellation argument
  needs.

  What is NOT proved here: the cancellation itself, hence neither the `s1`/`s2` bound nor
  the `s3` bound nor the lower half of the identity.

  No `sorry`.
-/

import CorrectedSpan

namespace PhiLipschitz

open EltBridge EltBridge.Elt CorrectedSpan

/-- **A sum changes only where its summand does.**  If `f` and `g` agree off a single
point `k` of `S`, the sums differ by exactly the difference at `k`.  Elementary, but it is
the step that turns "the site cost moves only at `kstar`" into a statement about `lRTrue`. -/
theorem sum_eq_add_diff_of_eq_off {S : Finset ℤ} {f g : ℤ → ℤ} {k : ℤ} (hk : k ∈ S)
    (h : ∀ s ∈ S, s ≠ k → f s = g s) :
    ∑ s ∈ S, f s = (∑ s ∈ S, g s) + (f k - g k) := by
  rw [← Finset.add_sum_erase _ f hk, ← Finset.add_sum_erase _ g hk]
  have hrest : ∑ s ∈ S.erase k, f s = ∑ s ∈ S.erase k, g s :=
    Finset.sum_congr rfl fun s hs =>
      h s (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs)
  rw [hrest]; ring

/-- **`s1` moves the site sum only at `kstar`.**  `s1` fixes `kstar` and `d`, so
`siteCost_eq_of_ne_kstar` applies at every other site; combined with
`CorrectedSpan.ATrue_s1`/`BTrue_s1` (the summation range is unchanged) the whole
difference of site sums is the difference at `kstar` alone. -/
theorem siteSum_sub_eq_at_kstar_s1 (g : EltBridge.Elt) (hk : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1)) :
    (∑ s ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g) + 1),
        ((s1 g).toPathData.siteCost s : ℤ))
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), (g.toPathData.siteCost s : ℤ))
        + (((s1 g).toPathData.siteCost g.kstar : ℤ)
            - (g.toPathData.siteCost g.kstar : ℤ)) := by
  rw [ATrue_s1, BTrue_s1]
  refine sum_eq_add_diff_of_eq_off hk (fun s _ hs => ?_)
  have := siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hs
  exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) this

/-- **The same for `s2`.** -/
theorem siteSum_sub_eq_at_kstar_s2 (g : EltBridge.Elt) (hk : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1)) :
    (∑ s ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g) + 1),
        ((s2 g).toPathData.siteCost s : ℤ))
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), (g.toPathData.siteCost s : ℤ))
        + (((s2 g).toPathData.siteCost g.kstar : ℤ)
            - (g.toPathData.siteCost g.kstar : ℤ)) := by
  rw [ATrue_s2, BTrue_s2]
  refine sum_eq_add_diff_of_eq_off hk (fun s _ hs => ?_)
  have := siteCost_eq_of_ne_kstar (P := (s2 g).toPathData) (Q := g.toPathData) rfl rfl s hs
  exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) this

/-- **Hence the site sum moves by at most one under `s1`**, since the single site it can
move is bounded by `s1_siteCost_kstar`.  This is the first half of the `s1` case; the
other half is the defect `cTrue`, where the cancellation lives. -/
theorem siteSum_dist_le_one_s1 (g : EltBridge.Elt)
    (hk : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1)) :
    ((∑ s ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g) + 1),
        ((s1 g).toPathData.siteCost s : ℤ))
      - ∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), (g.toPathData.siteCost s : ℤ)) ^ 2 ≤ 1 := by
  rw [siteSum_sub_eq_at_kstar_s1 g hk]
  obtain ⟨h1, h2⟩ := s1_siteCost_kstar g
  have : (((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)) ^ 2
      ≤ 1 := by nlinarith
  simpa using this


/-! ### The cancellation, isolated: a cut site is exactly a zero-cost site

This is the lemma that makes the `site cost` / `defect` cancellation automatic rather
than a case analysis.  `cut s` asks for `alpha = beta = Phi = 0` while
`siteCost s = max |alpha| |beta|`, so one direction is immediate; the content is that
`alpha = beta = 0` already FORCES `Phi = 0`.

Proof, by hand before Lean: from `alpha s = 0` and `hpar` (`d j = travel k j mod 2`),
`Phi s` is even, since `eps = +-1` makes `eps * vL = vL (mod 2)`.  And `Phi s` lies in
`[-2, 2]` because `f (s-1)` is `-1, 0, 1` and the two indicators are `0, 1`.  Both extremes
are impossible: `Phi = 2` needs `vArr s = 1`, i.e. `s = 0`, together with
`travel k (-1) = 1`, but `travel` is `1` only for `0 <= j`; `Phi = -2` needs `vL s = 1`,
i.e. `s = kstar`, together with `travel k (kstar - 1) = -1`, but that value is only ever
`0` or `1`.  So `Phi = 0`.

Consequence: a site leaving the cut set is exactly a site whose cost rises from `0`, which
is the exchange the Lipschitz bound needs. -/
theorem cut_iff_siteCost_zero (P : SiteCost.PathData) (s : ℤ) :
    P.cut s ↔ P.siteCost s = 0 := by
  constructor
  · rintro ⟨ha, hb, -⟩
    unfold SiteCost.PathData.siteCost
    rw [ha, hb]; simp
  · intro h
    unfold SiteCost.PathData.siteCost at h
    have ha : P.alphaAt s = 0 := by
      have : (P.alphaAt s).natAbs = 0 := by omega
      omega
    have hb : P.betaAt s = 0 := by
      have : (P.betaAt s).natAbs = 0 := by omega
      omega
    refine ⟨ha, hb, ?_⟩
    have hp := P.hpar (s - 1)
    have he := P.heps
    revert ha
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.PhiAt SiteCost.PathData.f
      SiteCost.PathData.vL SiteCost.PathData.vD SiteCost.vArr SiteCost.travel at *
    split_ifs at * <;> omega

/-- **The defect counts exactly the zero-cost sites.**  Restating `cut_iff_siteCost_zero`
as a `Finset` identity, which is the form the potential needs: the cut sites of a window
are precisely the sites of that window carrying no cost. -/
theorem filter_cut_eq_filter_siteCost_zero (P : SiteCost.PathData) (S : Finset ℤ) :
    S.filter P.cut = S.filter (fun s => P.siteCost s = 0) := by
  apply Finset.filter_congr
  intro s _
  simpa using cut_iff_siteCost_zero P s


/-! ### The exchange, in the abstract

With `cut_iff_siteCost_zero` in hand the `s1`/`s2` cancellation is no longer a case
analysis over the geometry: it is one arithmetic fact about a single site.  Let `c` be the
site cost at `kstar` before the step and `c'` after.  The site sum moves by `c' - c`, and
the defect moves by `[c' = 0] - [c = 0]`, because a cut site is precisely a zero-cost site.
So the potential moves by

    (c' - c) + 2 * ([c' = 0] - [c = 0])

and the point is that this is bounded by `1` in absolute value whenever `|c' - c| <= 1`,
even though its two summands are bounded only by `1` and `2`.  The two movements are the
SAME event with opposite sign: a site can only leave the cut set by its cost rising off
`0`, and then the `+1` in the cost is paid back twice over by the lost cut.

This is why the naive estimate gives `5` and the truth is `1`. -/
theorem exchange_le_one (c c' : ℕ) (h1 : (c' : ℤ) ≤ (c : ℤ) + 1) (h2 : (c : ℤ) ≤ (c' : ℤ) + 1) :
    ((c' : ℤ) - (c : ℤ)
        + 2 * ((if c' = 0 then (1 : ℤ) else 0) - (if c = 0 then (1 : ℤ) else 0))) ≤ 1
      ∧ -1 ≤ ((c' : ℤ) - (c : ℤ)
        + 2 * ((if c' = 0 then (1 : ℤ) else 0) - (if c = 0 then (1 : ℤ) else 0))) := by
  by_cases hc : c = 0 <;> by_cases hc' : c' = 0 <;>
    simp only [hc, hc', if_true, if_false, if_neg, Nat.cast_zero] <;> omega

/-- **The same bound, stated on the squared difference**, which is the form an induction
on `Reaches` consumes without carrying an absolute value. -/
theorem exchange_sq_le_one (c c' : ℕ) (h1 : (c' : ℤ) ≤ (c : ℤ) + 1)
    (h2 : (c : ℤ) ≤ (c' : ℤ) + 1) :
    ((c' : ℤ) - (c : ℤ)
      + 2 * ((if c' = 0 then (1 : ℤ) else 0) - (if c = 0 then (1 : ℤ) else 0))) ^ 2 ≤ 1 := by
  obtain ⟨hu, hl⟩ := exchange_le_one c c' h1 h2
  nlinarith


/-! ### The boundary-shield case, `kstar = 0`

The one place where the exchange above does not immediately apply, because the shield's
firing condition depends on `delta` and therefore flips under both `s1` and `s2`.  It
closes, and the reason is rigid: `ShieldFires` forces `d (-1) = 0`, so `cut 0` reads
`-1 + eps = 0`, pinning `eps = 1` and `d 0 = 0`.  After the flip the two indicators swap
(`vL 0 : 1 -> 0` and `vR 0 : 0 -> 1`), giving `alpha = beta = -1` and a cost of exactly
one.  So the shield is lost and the cost rises by exactly one, and the potential moves by
`1 - 2 = -1`. -/

/-- **A firing shield at a cut site pins the marker data.** -/
theorem shield_cut_pins (g : EltBridge.Elt) (hs : ShieldFires g) (hc : g.toPathData.cut 0) :
    g.eps = 1 ∧ g.d 0 = 0 := by
  obtain ⟨hk, hd, hneg, -⟩ := hs
  obtain ⟨ha, hb, -⟩ := hc
  have hm1 : g.d (-1) = 0 := hneg (-1) (by norm_num)
  constructor
  · revert ha
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD SiteCost.vArr
    simp [EltBridge.Elt.toPathData, hk, hd, hm1]
    omega
  · revert hb
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
    simp [EltBridge.Elt.toPathData, hk, hd]

/-- **And then `s1` raises the cost at site `0` to exactly one.**  The `delta` flip swaps
the two marker indicators, so `alpha` and `beta` both become `-1`. -/
theorem siteCost_s1_zero_of_shield_cut (g : EltBridge.Elt) (hs : ShieldFires g)
    (hc : g.toPathData.cut 0) : (s1 g).toPathData.siteCost 0 = 1 := by
  obtain ⟨he, hd0⟩ := shield_cut_pins g hs hc
  obtain ⟨hk, hd, hneg, -⟩ := hs
  have hm1 : g.d (-1) = 0 := hneg (-1) (by norm_num)
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp [EltBridge.Elt.toPathData, EltBridge.Elt.s1, hk, hd, he, hd0, hm1]

/-- **So in the shield case the potential moves by exactly `-1`**: the site cost rises by
one and the shield term is lost, and the lost shield is worth two.  Stated on the three
moving quantities, so it can be plugged into the window bookkeeping without re-deriving
them. -/
theorem shield_case_delta (g : EltBridge.Elt) (hs : ShieldFires g)
    (hc : g.toPathData.cut 0) :
    ((s1 g).toPathData.siteCost 0 : ℤ) - (g.toPathData.siteCost 0 : ℤ)
      + 2 * ((0 : ℤ) - 1) = -1 := by
  rw [siteCost_s1_zero_of_shield_cut g hs hc,
    (cut_iff_siteCost_zero g.toPathData 0).mp hc]
  norm_num


/-! ### Window bookkeeping: a filter changes only where its predicate does -/

/-- **The count of a filter moves by the indicator difference at the one point where the
predicate moves.**  The `Finset` counterpart of `sum_eq_add_diff_of_eq_off`, and the last
piece of bookkeeping the `s1`/`s2` bound needs: `cut` moves only at `kstar`, so the cut
count of a window moves by `[cut' kstar] - [cut kstar]` and by nothing else. -/
theorem filter_card_eq_add_diff {S : Finset ℤ} {p q : ℤ → Prop}
    [DecidablePred p] [DecidablePred q] {k : ℤ} (hk : k ∈ S)
    (h : ∀ s ∈ S, s ≠ k → (p s ↔ q s)) :
    ((S.filter p).card : ℤ)
      = ((S.filter q).card : ℤ)
        + ((if p k then (1 : ℤ) else 0) - (if q k then (1 : ℤ) else 0)) := by
  classical
  have hcard : ∀ r : ℤ → Prop, ∀ _ : DecidablePred r,
      ((S.filter r).card : ℤ) = ∑ s ∈ S, (if r s then (1 : ℤ) else 0) := by
    intro r _
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hcard p inferInstance, hcard q inferInstance]
  refine sum_eq_add_diff_of_eq_off hk (fun s hsS hsk => ?_)
  have hiff := h s hsS hsk
  by_cases hps : p s
  · rw [if_pos hps, if_pos (hiff.mp hps)]
  · rw [if_neg hps, if_neg (fun hq => hps (hiff.mpr hq))]


/-! ### Disjointness of the two branches

The `s1`/`s2` argument splits on whether the moving site `kstar` is interior to the window
or on its boundary, and the shield lives only on the boundary.  That the two never overlap
is not an assumption: a firing shield forces the window to start at `0`, and `0` is then
not interior. -/

/-- **A firing shield pins the left end of the corrected span to `0`.**  `ShieldFires`
gives `kstar = 0`, so `travel` vanishes identically, and forbids deposits below `0`; hence
every occupied edge is `>= 0`, the minimum is `>= 0`, and the clamp `min 0 _` returns `0`. -/
theorem shieldFires_ATrue_zero (g : EltBridge.Elt) (hs : ShieldFires g) : ATrue g = 0 := by
  obtain ⟨hk, -, hneg, -⟩ := hs
  unfold ATrue
  split_ifs with hne
  · have hmin : 0 ≤ (occTrue g).min' hne := by
      refine Finset.le_min' _ _ _ (fun j hj => ?_)
      by_contra hlt
      push_neg at hlt
      have : g.d j ≠ 0 ∨ SiteCost.travel g.kstar j ≠ 0 := by
        have := Finset.mem_filter.mp hj
        simpa [occTrue] using this.2
      rcases this with hd | hf
      · exact hd (hneg j hlt)
      · exact hf (by rw [hk]; exact SiteCost.travel_of_kstar_zero j)
    omega
  · rfl

/-- **So the shield site is never interior**: if the shield fires, `0` is the left endpoint
of the window and `Finset.Ioo` excludes it.  This is what keeps the exchange bound (which
governs interior sites) and the shield case (which governs `0`) from double-counting. -/
theorem shield_site_not_interior (g : EltBridge.Elt) (hs : ShieldFires g) :
    (0 : ℤ) ∉ Finset.Ioo (ATrue g) (BTrue g + 1) := by
  rw [shieldFires_ATrue_zero g hs]
  simp


/-! ### The potential, and the `s1` bound at an interior cursor -/

/-- The corrected potential, over `ZZ` so that differences need no truncated subtraction. -/
noncomputable def PhiZ (g : EltBridge.Elt) : ℤ := (lRTrue g : ℤ) + 2 * (cTrue g : ℤ)

/-- **At an interior cursor the shield cannot fire.**  It would need `kstar = 0`, and then
`shieldFires_ATrue_zero` puts `0` at the left endpoint, where `Ioo` does not reach. -/
theorem not_shieldFires_of_interior (g : EltBridge.Elt)
    (hk : g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1)) : ¬ ShieldFires g := by
  intro hs
  have h0 : g.kstar = 0 := hs.1
  rw [h0] at hk
  exact shield_site_not_interior g hs hk

/-- **`cTrue` is just the interior cut count when the shield does not fire.** -/
theorem cTrue_eq_filter_of_not_shield (g : EltBridge.Elt) (hs : ¬ ShieldFires g) :
    (cTrue g : ℤ)
      = (((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card : ℤ) := by
  unfold cTrue
  rw [if_neg (fun h => hs h.1)]
  simp

/-- **The `s1` bound, at an interior cursor.**  Every ingredient is in place: the span and
the `mu` sum are fixed (`CorrectedSpan`), the site sum moves only at `kstar`, the cut count
moves only at `kstar`, a cut site is exactly a zero-cost site, and the resulting exchange
is bounded by one.  The shield is absent here by `not_shieldFires_of_interior`, so the two
branches do not interact. -/
theorem phiZ_dist_le_one_s1_interior (g : EltBridge.Elt)
    (hk : g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    (PhiZ (s1 g) - PhiZ g) ^ 2 ≤ 1 := by
  classical
  have hkIcc : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := by
    simp only [Finset.mem_Ioo] at hk
    simp only [Finset.mem_Icc]
    omega
  -- the shield is absent on both sides (`s1` moves neither `kstar` nor the span)
  have hs : ¬ ShieldFires g := not_shieldFires_of_interior g hk
  have hs' : ¬ ShieldFires (s1 g) := by
    have hk' : (s1 g).kstar ∈ Finset.Ioo (ATrue (s1 g)) (BTrue (s1 g) + 1) := by
      rw [ATrue_s1, BTrue_s1]; exact hk
    exact not_shieldFires_of_interior (s1 g) hk'
  -- `lRTrue` moves by the site cost at `kstar` alone
  have hlR : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ)
        + (((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)) := by
    have hmu : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)),
          ((s1 g).toPathData.mu j : ℤ))
        = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
      rw [ATrue_s1, BTrue_s1]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      unfold SiteCost.PathData.mu
      simp [EltBridge.Elt.toPathData]
    unfold lRTrue
    push_cast
    rw [hmu, siteSum_sub_eq_at_kstar_s1 g hkIcc]
    ring
  -- `cTrue` moves by the cut indicator at `kstar` alone
  have hc : (cTrue (s1 g) : ℤ)
      = (cTrue g : ℤ)
        + ((if (s1 g).toPathData.cut g.kstar then (1 : ℤ) else 0)
            - (if g.toPathData.cut g.kstar then (1 : ℤ) else 0)) := by
    rw [cTrue_eq_filter_of_not_shield _ hs', cTrue_eq_filter_of_not_shield _ hs,
      ATrue_s1, BTrue_s1]
    refine filter_card_eq_add_diff hk (fun s _ hsne => ?_)
    rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
      siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hsne]
  -- rewrite both cut indicators as zero-cost indicators, then apply the exchange bound
  have hcut : ∀ h : EltBridge.Elt,
      (if h.toPathData.cut g.kstar then (1 : ℤ) else 0)
        = (if h.toPathData.siteCost g.kstar = 0 then (1 : ℤ) else 0) := by
    intro h
    by_cases hh : h.toPathData.siteCost g.kstar = 0
    · rw [if_pos ((cut_iff_siteCost_zero h.toPathData g.kstar).mpr hh), if_pos hh]
    · rw [if_neg (fun hcc => hh ((cut_iff_siteCost_zero h.toPathData g.kstar).mp hcc)),
        if_neg hh]
  rw [hcut, hcut] at hc
  obtain ⟨h1, h2⟩ := s1_siteCost_kstar g
  have hex := exchange_sq_le_one (g.toPathData.siteCost g.kstar)
    ((s1 g).toPathData.siteCost g.kstar) h1 h2
  have key : PhiZ (s1 g) - PhiZ g
      = (((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)
          + 2 * ((if (s1 g).toPathData.siteCost g.kstar = 0 then (1 : ℤ) else 0)
              - (if g.toPathData.siteCost g.kstar = 0 then (1 : ℤ) else 0))) := by
    unfold PhiZ
    rw [hlR, hc]
    ring
  rw [key]
  exact hex


/-! ### The `s2` bound at an interior cursor -- transcription of the `s1` case -/

/-- **The `s2` bound, at an interior cursor.**  Identical shape to the `s1` case: span and
`mu` sum fixed, site sum and cut count both move only at `kstar`, and the exchange between
them is bounded by one. -/
theorem phiZ_dist_le_one_s2_interior (g : EltBridge.Elt)
    (hk : g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    (PhiZ (s2 g) - PhiZ g) ^ 2 ≤ 1 := by
  classical
  have hkIcc : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := by
    simp only [Finset.mem_Ioo] at hk
    simp only [Finset.mem_Icc]
    omega
  have hs : ¬ ShieldFires g := not_shieldFires_of_interior g hk
  have hs' : ¬ ShieldFires (s2 g) := by
    have hk' : (s2 g).kstar ∈ Finset.Ioo (ATrue (s2 g)) (BTrue (s2 g) + 1) := by
      rw [ATrue_s2, BTrue_s2]; exact hk
    exact not_shieldFires_of_interior (s2 g) hk'
  have hmu : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)),
        ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold SiteCost.PathData.mu
    simp [EltBridge.Elt.toPathData]
  have hlR : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ)
        + (((s2 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue
    push_cast
    rw [hmu, siteSum_sub_eq_at_kstar_s2 g hkIcc]
    ring
  have hc : (cTrue (s2 g) : ℤ)
      = (cTrue g : ℤ)
        + ((if (s2 g).toPathData.cut g.kstar then (1 : ℤ) else 0)
            - (if g.toPathData.cut g.kstar then (1 : ℤ) else 0)) := by
    rw [cTrue_eq_filter_of_not_shield _ hs', cTrue_eq_filter_of_not_shield _ hs,
      ATrue_s2, BTrue_s2]
    refine filter_card_eq_add_diff hk (fun s _ hsne => ?_)
    rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
      siteCost_eq_of_ne_kstar (P := (s2 g).toPathData) (Q := g.toPathData) rfl rfl s hsne]
  have hcut : ∀ h : EltBridge.Elt,
      (if h.toPathData.cut g.kstar then (1 : ℤ) else 0)
        = (if h.toPathData.siteCost g.kstar = 0 then (1 : ℤ) else 0) := by
    intro h
    by_cases hh : h.toPathData.siteCost g.kstar = 0
    · rw [if_pos ((cut_iff_siteCost_zero h.toPathData g.kstar).mpr hh), if_pos hh]
    · rw [if_neg (fun hcc => hh ((cut_iff_siteCost_zero h.toPathData g.kstar).mp hcc)),
        if_neg hh]
  rw [hcut, hcut] at hc
  obtain ⟨h1, h2⟩ := s2_siteCost_kstar g
  have hex := exchange_sq_le_one (g.toPathData.siteCost g.kstar)
    ((s2 g).toPathData.siteCost g.kstar) h1 h2
  have key : PhiZ (s2 g) - PhiZ g
      = (((s2 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)
          + 2 * ((if (s2 g).toPathData.siteCost g.kstar = 0 then (1 : ℤ) else 0)
              - (if g.toPathData.siteCost g.kstar = 0 then (1 : ℤ) else 0))) := by
    unfold PhiZ
    rw [hlR, hc]
    ring
  rw [key]
  exact hex


/-- **`s2` also raises the cost at site `0` to exactly one, in the shield case.**  `s2`
flips `delta` just as `s1` does (and additionally flips `eps`, which does not enter: the
indicator swap alone forces `alpha = beta = -1` regardless of the sign of `eps`, since
`shield_cut_pins` already pins `eps = 1` and `d 0 = 0`). -/
theorem siteCost_s2_zero_of_shield_cut (g : EltBridge.Elt) (hs : ShieldFires g)
    (hc : g.toPathData.cut 0) : (s2 g).toPathData.siteCost 0 = 1 := by
  obtain ⟨he, hd0⟩ := shield_cut_pins g hs hc
  obtain ⟨hk, hd, hneg, -⟩ := hs
  have hm1 : g.d (-1) = 0 := hneg (-1) (by norm_num)
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp [EltBridge.Elt.toPathData, EltBridge.Elt.s2, hk, hd, he, hd0, hm1]

/-- **And the `s2` shield case moves the potential by exactly `-1`**, by the same
accounting as `s1`: the cost rises from `0` to `1` and the shield (worth `2`) is lost. -/
theorem shield_case_delta_s2 (g : EltBridge.Elt) (hs : ShieldFires g)
    (hc : g.toPathData.cut 0) :
    ((s2 g).toPathData.siteCost 0 : ℤ) - (g.toPathData.siteCost 0 : ℤ)
      + 2 * ((0 : ℤ) - 1) = -1 := by
  rw [siteCost_s2_zero_of_shield_cut g hs hc,
    (cut_iff_siteCost_zero g.toPathData 0).mp hc]
  norm_num

end PhiLipschitz

#print axioms PhiLipschitz.sum_eq_add_diff_of_eq_off
#print axioms PhiLipschitz.siteSum_sub_eq_at_kstar_s1
#print axioms PhiLipschitz.siteSum_sub_eq_at_kstar_s2
#print axioms PhiLipschitz.siteSum_dist_le_one_s1
#print axioms PhiLipschitz.cut_iff_siteCost_zero
#print axioms PhiLipschitz.filter_cut_eq_filter_siteCost_zero
#print axioms PhiLipschitz.exchange_le_one
#print axioms PhiLipschitz.exchange_sq_le_one

#print axioms PhiLipschitz.shield_cut_pins
#print axioms PhiLipschitz.siteCost_s1_zero_of_shield_cut
#print axioms PhiLipschitz.shield_case_delta
#print axioms PhiLipschitz.filter_card_eq_add_diff
#print axioms PhiLipschitz.shieldFires_ATrue_zero
#print axioms PhiLipschitz.shield_site_not_interior
#print axioms PhiLipschitz.not_shieldFires_of_interior
#print axioms PhiLipschitz.cTrue_eq_filter_of_not_shield
#print axioms PhiLipschitz.phiZ_dist_le_one_s1_interior
#print axioms PhiLipschitz.phiZ_dist_le_one_s2_interior
#print axioms PhiLipschitz.siteCost_s2_zero_of_shield_cut
#print axioms PhiLipschitz.shield_case_delta_s2