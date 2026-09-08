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


/-! ### `kstar` always sits in the corrected window

The prerequisite the full (non-interior-restricted) bound needs: even though `ATrue`,
`BTrue` are built from `occTrue` (occupied edges alone, no forced edge `0`), `kstar`
never falls outside `[ATrue, BTrue + 1]`.  Three cases, each forcing one edge into
`occTrue` via a nonzero `travel` value there:

* `kstar > 0`: `travel kstar 0 = 1` puts edge `0` in `occTrue`, and
  `travel kstar (kstar-1) = 1` puts edge `kstar-1` in it too, so `BTrue >= kstar-1`.
* `kstar < 0`: symmetrically `travel kstar kstar = -1` puts edge `kstar` in `occTrue`,
  so `ATrue <= kstar`.
* `kstar = 0`: `ATrue <= 0` and `BTrue >= -1` hold by definition of the clamp, in every
  case, occupied or not. -/
theorem kstar_mem_corrected_window (g : EltBridge.Elt) :
    g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := by
  classical
  have mem_occTrue_of_ne : ∀ j : ℤ, g.d j ≠ 0 ∨ SiteCost.travel g.kstar j ≠ 0 →
      j ∈ occTrue g := by
    intro j h
    unfold occTrue
    by_cases hj : j ∈ g.supp
    · exact Finset.mem_filter.mpr ⟨hj, h⟩
    · rcases h with h | h
      · exact absurd (g.hsupp j hj).1 h
      · exact absurd (g.hsupp j hj).2 h
  simp only [Finset.mem_Icc]
  rcases lt_trichotomy g.kstar 0 with hneg | hzero | hpos
  · have hocc : g.kstar ∈ occTrue g := by
      apply mem_occTrue_of_ne
      right
      unfold SiteCost.travel
      rw [if_neg (by omega), if_pos (by omega)]
      omega
    have hATrue : ATrue g ≤ g.kstar := by
      unfold ATrue
      rw [dif_pos ⟨g.kstar, hocc⟩]
      exact le_trans (min_le_right _ _) (Finset.min'_le _ _ hocc)
    have hBTrue : (-1 : ℤ) ≤ BTrue g := by
      unfold BTrue; split_ifs <;> omega
    exact ⟨hATrue, by omega⟩
  · have hATrue : ATrue g ≤ 0 := by unfold ATrue; split_ifs <;> omega
    have hBTrue : (-1 : ℤ) ≤ BTrue g := by unfold BTrue; split_ifs <;> omega
    exact ⟨by omega, by omega⟩
  · have hocc : (g.kstar - 1) ∈ occTrue g := by
      apply mem_occTrue_of_ne
      right
      unfold SiteCost.travel
      rw [if_pos (by omega)]
      omega
    have hBTrue : g.kstar - 1 ≤ BTrue g := by
      unfold BTrue
      rw [dif_pos ⟨g.kstar - 1, hocc⟩]
      exact le_trans (Finset.le_max' _ _ hocc) (le_max_right _ _)
    have hATrue : ATrue g ≤ 0 := by unfold ATrue; split_ifs <;> omega
    exact ⟨by omega, by omega⟩

/-! ### The non-interior case at `kstar != 0`: `cTrue` does not move at all

`ShieldFires` requires `kstar = 0` outright, so at `kstar != 0` it is false on BOTH sides
of an `s1`/`s2` step regardless of `delta` (which those generators do flip, so an
iff-invariance claim in terms of `delta` alone is false -- the shield can fire on at most
one side, exactly the phenomenon `shield_case_delta` isolates; here we simply stay away
from `kstar = 0` instead of tracking that flip). -/

theorem not_shieldFires_of_kstar_ne_zero (g : EltBridge.Elt) (hk : g.kstar ≠ 0) :
    ¬ ShieldFires g := fun h => hk h.1

/-- **If `kstar != 0` and is not interior, `s1` does not move `cTrue`.**  Neither term of
`cTrue` can see `kstar`: the interior filter excludes it (not interior), and the shield
term is `0` on both sides (`kstar != 0`, and `s1` does not move `kstar`). -/
theorem cTrue_s1_eq_of_not_interior_ne_zero (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hk : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    cTrue (s1 g) = cTrue g := by
  have hs : ¬ ShieldFires g := not_shieldFires_of_kstar_ne_zero g hk0
  have hs' : ¬ ShieldFires (s1 g) := not_shieldFires_of_kstar_ne_zero (s1 g) (by rw [s1_kstar]; exact hk0)
  have hzcast : ((cTrue (s1 g) : ℤ)) = ((cTrue g : ℤ)) := by
    rw [cTrue_eq_filter_of_not_shield _ hs', cTrue_eq_filter_of_not_shield _ hs,
      ATrue_s1, BTrue_s1]
    have : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s1 g).toPathData.cut
        = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
      apply Finset.filter_congr
      intro s hsS
      rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero]
      by_cases hsk : s = g.kstar
      · exact absurd (hsk ▸ hsS) hk
      · rw [siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
    rw [this]
  exact_mod_cast hzcast

/-- **So the potential moves by at most one there too**, directly from the site cost
bound at `kstar` -- no exchange needed, since `cTrue` is fixed. -/
theorem phiZ_dist_le_one_s1_boundary_ne_zero (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hk : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1))
    (hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1)) :
    (PhiZ (s1 g) - PhiZ g) ^ 2 ≤ 1 := by
  have hmu : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ)
        + (((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu, siteSum_sub_eq_at_kstar_s1 g hkw]; ring
  have hc : cTrue (s1 g) = cTrue g := cTrue_s1_eq_of_not_interior_ne_zero g hk0 hk
  obtain ⟨h1, h2⟩ := s1_siteCost_kstar g
  have key : PhiZ (s1 g) - PhiZ g
      = ((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ) := by
    unfold PhiZ; rw [hlR, hc]; ring
  rw [key]; nlinarith


theorem cTrue_s2_eq_of_not_interior_ne_zero (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hk : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    cTrue (s2 g) = cTrue g := by
  have hs : ¬ ShieldFires g := not_shieldFires_of_kstar_ne_zero g hk0
  have hs' : ¬ ShieldFires (s2 g) :=
    not_shieldFires_of_kstar_ne_zero (s2 g) (by rw [s2_kstar]; exact hk0)
  have hzcast : ((cTrue (s2 g) : ℤ)) = ((cTrue g : ℤ)) := by
    rw [cTrue_eq_filter_of_not_shield _ hs', cTrue_eq_filter_of_not_shield _ hs,
      ATrue_s2, BTrue_s2]
    have : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s2 g).toPathData.cut
        = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
      apply Finset.filter_congr
      intro s hsS
      rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero]
      by_cases hsk : s = g.kstar
      · exact absurd (hsk ▸ hsS) hk
      · rw [siteCost_eq_of_ne_kstar (P := (s2 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
    rw [this]
  exact_mod_cast hzcast

theorem phiZ_dist_le_one_s2_boundary_ne_zero (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hk : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1))
    (hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1)) :
    (PhiZ (s2 g) - PhiZ g) ^ 2 ≤ 1 := by
  have hmu : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)), ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ)
        + (((s2 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu, siteSum_sub_eq_at_kstar_s2 g hkw]; ring
  have hc : cTrue (s2 g) = cTrue g := cTrue_s2_eq_of_not_interior_ne_zero g hk0 hk
  obtain ⟨h1, h2⟩ := s2_siteCost_kstar g
  have key : PhiZ (s2 g) - PhiZ g
      = ((s2 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ) := by
    unfold PhiZ; rw [hlR, hc]; ring
  rw [key]; nlinarith


/-! ### The mirror shield case: the shield newly fires after `s1`/`s2`

The case `shield_case_delta` does not cover: `g.delta = true` (so `ShieldFires g` is
false outright, `delta = false` being required), but `ShieldFires (s1 g)` can still
hold, since `s1` flips `delta` to `false`.  Worked out by hand first: with `kstar = 0`,
`delta = true`, `ShieldFires (s1 g)` pins (via `shield_cut_pins` applied to `s1 g`,
using that `s1` does not change `eps` or `d`) `eps = 1` and `d 0 = 0`; together with
`ShieldFires`'s own `d (-1) = 0` this gives `alpha_before = beta_before = -1` (the
indicators sit the OTHER way while `delta = true`), so `siteCost g 0 = 1`, while
`siteCost (s1 g) 0 = 0` by `cut_iff_siteCost_zero`.  So the cost DROPS by one and the
shield is GAINED (worth `2`): the potential moves by `-1 + 2 = +1`, the mirror image of
`shield_case_delta`'s `-1`. -/

/-- **`s1`'s shield-cut pins transported backward.**  Since `s1` does not change `eps`
or `d`, `shield_cut_pins` applied to `s1 g` gives the same pins on `g` directly. -/
theorem shield_cut_pins_s1_after (g : EltBridge.Elt) (hs' : ShieldFires (s1 g))
    (hc' : (s1 g).toPathData.cut 0) : g.eps = 1 ∧ g.d 0 = 0 :=
  shield_cut_pins (s1 g) hs' hc'

/-- **Before the step, with `delta = true`, the cost at site `0` is exactly one.**  The
indicators sit oppositely to the `delta = false` case: `vL = 0`, `vR = vD = 1`. -/
theorem siteCost_zero_of_shield_cut_s1_after (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hdelta : g.delta = true) (hneg : g.d (-1) = 0) (he : g.eps = 1) (hd0 : g.d 0 = 0) :
    g.toPathData.siteCost 0 = 1 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp [EltBridge.Elt.toPathData, hkz, hdelta, hneg, he, hd0]

/-- **So the mirror shield case moves the potential by exactly `+1`.**  The cost drops
from `1` to `0` and the shield (worth `2`) is gained: `-1 + 2 = 1`. -/
theorem shield_case_delta_s1_after (g : EltBridge.Elt) (hs' : ShieldFires (s1 g))
    (hc' : (s1 g).toPathData.cut 0) (hdelta : g.delta = true) :
    ((s1 g).toPathData.siteCost 0 : ℤ) - (g.toPathData.siteCost 0 : ℤ) + 2 * (1 - 0) = 1 := by
  obtain ⟨he, hd0⟩ := shield_cut_pins_s1_after g hs' hc'
  obtain ⟨hkz, -, hneg, -⟩ := hs'
  rw [s1_kstar] at hkz
  have hneg0 : g.d (-1) = 0 := hneg (-1) (by norm_num)
  rw [siteCost_zero_of_shield_cut_s1_after g hkz hdelta hneg0 he hd0,
    (cut_iff_siteCost_zero (s1 g).toPathData 0).mp hc']
  norm_num


/-! ### The `s2` mirror -- transcription -/

theorem shield_cut_pins_s2_after (g : EltBridge.Elt) (hs' : ShieldFires (s2 g))
    (hc' : (s2 g).toPathData.cut 0) : g.eps = -1 ∧ g.d 0 = 0 := by
  have h := shield_cut_pins (s2 g) hs' hc'
  have he : (s2 g).eps = -g.eps := rfl
  have hd : (s2 g).d = g.d := rfl
  rw [he, hd] at h
  exact ⟨by omega, h.2⟩

/-- With `s2`'s sign flip the pinned value is `eps = -1`, not `1` -- a genuinely
different case from `s1`'s, since `siteCost` depends on `eps` through `alphaAt`/`betaAt`.
Recomputed directly rather than reused. -/
theorem siteCost_zero_of_shield_cut_s2_after (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hdelta : g.delta = true) (hneg : g.d (-1) = 0) (he : g.eps = -1) (hd0 : g.d 0 = 0) :
    g.toPathData.siteCost 0 = 1 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp [EltBridge.Elt.toPathData, hkz, hdelta, hneg, he, hd0]

theorem shield_case_delta_s2_after (g : EltBridge.Elt) (hs' : ShieldFires (s2 g))
    (hc' : (s2 g).toPathData.cut 0) (hdelta : g.delta = true) :
    ((s2 g).toPathData.siteCost 0 : ℤ) - (g.toPathData.siteCost 0 : ℤ) + 2 * (1 - 0) = 1 := by
  obtain ⟨he, hd0⟩ := shield_cut_pins_s2_after g hs' hc'
  obtain ⟨hkz, -, hneg, -⟩ := hs'
  rw [s2_kstar] at hkz
  have hneg0 : g.d (-1) = 0 := hneg (-1) (by norm_num)
  rw [siteCost_zero_of_shield_cut_s2_after g hkz hdelta hneg0 he hd0,
    (cut_iff_siteCost_zero (s2 g).toPathData 0).mp hc']
  norm_num


/-! ### The full `kstar = 0` boundary case for `s1`

`ShieldFires` requires `delta = false` outright, and `s1` flips `delta`, so at most ONE
side of the step can ever have `ShieldFires` true -- never both, matching the four cases
already computed (`shield_case_delta`, `shield_case_delta_s1_after`) plus the case where
neither fires. -/

/-- **The interior filter is unaffected by a non-interior `kstar`, regardless of shield
status.**  Extracted from the argument already used in `cTrue_s1_eq_of_not_interior_ne_zero`,
since the boundary case at `kstar = 0` needs it independently of `ShieldFires`. -/
theorem interior_filter_s1_eq (g : EltBridge.Elt)
    (hk : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s1 g).toPathData.cut
      = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
  apply Finset.filter_congr
  intro s hsS
  rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero]
  by_cases hsk : s = g.kstar
  · exact absurd (hsk ▸ hsS) hk
  · rw [siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]

/-- **`s1`'s `kstar = 0` boundary case, unconditionally.**  Splits on `g.delta`: at most
one side can have the shield eligible (`delta = false` is required and `s1` flips it), so
each branch reduces to either the already-computed shield transition (`+-1` on the site
cost/shield pair, `shield_case_delta` / `shield_case_delta_s1_after`) or to `cTrue` not
moving at all (the direct bound, no exchange). -/
theorem phiZ_dist_le_one_s1_boundary_zero (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hk : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    (PhiZ (s1 g) - PhiZ g) ^ 2 ≤ 1 := by
  classical
  have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := kstar_mem_corrected_window g
  have hmu : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ)
        + (((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu, siteSum_sub_eq_at_kstar_s1 g hkw]; ring
  have hfilt : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s1 g).toPathData.cut
      = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut :=
    interior_filter_s1_eq g hk
  by_cases hd : g.delta = true
  · have hs0 : ¬ ShieldFires g := fun h => absurd hd (by rw [h.2.1]; simp)
    by_cases hsc : ShieldFires (s1 g) ∧ (s1 g).toPathData.cut 0
    · have e1 : cTrue (s1 g)
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card + 1 := by
        unfold cTrue; rw [ATrue_s1, BTrue_s1, if_pos hsc, hfilt]
      have e2 : cTrue g
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue
        rw [if_neg (fun h : ShieldFires g ∧ g.toPathData.cut 0 => hs0 h.1)]
        simp
      have hkey := shield_case_delta_s1_after g hsc.1 hsc.2 hd
      have hc : (cTrue (s1 g) : ℤ) = (cTrue g : ℤ) + 1 := by rw [e1, e2]; push_cast; ring
      have key : PhiZ (s1 g) - PhiZ g
          = ((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)
            + 2 * ((1 : ℤ) - 0) := by
        unfold PhiZ; rw [hlR, hc]; ring
      rw [key, hkz]; nlinarith [hkey]
    · have e1 : cTrue (s1 g)
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue
        rw [ATrue_s1, BTrue_s1, if_neg hsc, hfilt]
        simp
      have e2 : cTrue g
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue
        rw [if_neg (fun h : ShieldFires g ∧ g.toPathData.cut 0 => hs0 h.1)]
        simp
      have hc : cTrue (s1 g) = cTrue g := by rw [e1, e2]
      obtain ⟨h1, h2⟩ := s1_siteCost_kstar g
      have key : PhiZ (s1 g) - PhiZ g
          = ((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ) := by
        unfold PhiZ; rw [hlR, hc]; ring
      rw [key]; nlinarith
  · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
    have hs0' : ¬ ShieldFires (s1 g) := by
      intro h; apply absurd h.2.1; rw [s1]; simp [hd']
    by_cases hsc : ShieldFires g ∧ g.toPathData.cut 0
    · have e1 : cTrue (s1 g)
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue
        rw [ATrue_s1, BTrue_s1, if_neg (fun h : ShieldFires (s1 g) ∧ (s1 g).toPathData.cut 0 => hs0' h.1),
          hfilt]
        simp
      have e2 : cTrue g
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card + 1 := by
        unfold cTrue; rw [if_pos hsc]
      have hkey := shield_case_delta g hsc.1 hsc.2
      have hc : (cTrue (s1 g) : ℤ) = (cTrue g : ℤ) - 1 := by rw [e1, e2]; push_cast; ring
      have key : PhiZ (s1 g) - PhiZ g
          = ((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)
            + 2 * ((0 : ℤ) - 1) := by
        unfold PhiZ; rw [hlR, hc]; ring
      rw [key, hkz]; nlinarith [hkey]
    · have e1 : cTrue (s1 g)
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue
        rw [ATrue_s1, BTrue_s1, if_neg (fun h : ShieldFires (s1 g) ∧ (s1 g).toPathData.cut 0 => hs0' h.1),
          hfilt]
        simp
      have e2 : cTrue g
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue; rw [if_neg hsc]; simp
      have hc : cTrue (s1 g) = cTrue g := by rw [e1, e2]
      obtain ⟨h1, h2⟩ := s1_siteCost_kstar g
      have key : PhiZ (s1 g) - PhiZ g
          = ((s1 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ) := by
        unfold PhiZ; rw [hlR, hc]; ring
      rw [key]; nlinarith

/-! ### `s1`, assembled: the unconditional bound -/

/-- **`s1` moves `Phi` by at most one, unconditionally.**  The three cases proved above
(interior, `kstar != 0` boundary, `kstar = 0` boundary) are exhaustive by
`kstar_mem_corrected_window`. -/
theorem phiZ_dist_le_one_s1 (g : EltBridge.Elt) : (PhiZ (s1 g) - PhiZ g) ^ 2 ≤ 1 := by
  have hkw := kstar_mem_corrected_window g
  by_cases hint : g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1)
  · exact phiZ_dist_le_one_s1_interior g hint
  · by_cases hkz : g.kstar = 0
    · exact phiZ_dist_le_one_s1_boundary_zero g hkz hint
    · exact phiZ_dist_le_one_s1_boundary_ne_zero g hkz hint hkw


/-! ### The full `kstar = 0` boundary case for `s2` -- transcription, with `simp` proactive -/

theorem interior_filter_s2_eq (g : EltBridge.Elt)
    (hk : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s2 g).toPathData.cut
      = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
  apply Finset.filter_congr
  intro s hsS
  rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero]
  by_cases hsk : s = g.kstar
  · exact absurd (hsk ▸ hsS) hk
  · rw [siteCost_eq_of_ne_kstar (P := (s2 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]

theorem phiZ_dist_le_one_s2_boundary_zero (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hk : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    (PhiZ (s2 g) - PhiZ g) ^ 2 ≤ 1 := by
  classical
  have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := kstar_mem_corrected_window g
  have hmu : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)), ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ)
        + (((s2 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu, siteSum_sub_eq_at_kstar_s2 g hkw]; ring
  have hfilt : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s2 g).toPathData.cut
      = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut :=
    interior_filter_s2_eq g hk
  by_cases hd : g.delta = true
  · have hs0 : ¬ ShieldFires g := fun h => absurd hd (by rw [h.2.1]; simp)
    by_cases hsc : ShieldFires (s2 g) ∧ (s2 g).toPathData.cut 0
    · have e1 : cTrue (s2 g)
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card + 1 := by
        unfold cTrue; rw [ATrue_s2, BTrue_s2, if_pos hsc, hfilt]
      have e2 : cTrue g
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue
        rw [if_neg (fun h : ShieldFires g ∧ g.toPathData.cut 0 => hs0 h.1)]
        simp
      have hkey := shield_case_delta_s2_after g hsc.1 hsc.2 hd
      have hc : (cTrue (s2 g) : ℤ) = (cTrue g : ℤ) + 1 := by rw [e1, e2]; push_cast; ring
      have key : PhiZ (s2 g) - PhiZ g
          = ((s2 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)
            + 2 * ((1 : ℤ) - 0) := by
        unfold PhiZ; rw [hlR, hc]; ring
      rw [key, hkz]; nlinarith [hkey]
    · have e1 : cTrue (s2 g)
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue; rw [ATrue_s2, BTrue_s2, if_neg hsc, hfilt]; simp
      have e2 : cTrue g
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue
        rw [if_neg (fun h : ShieldFires g ∧ g.toPathData.cut 0 => hs0 h.1)]
        simp
      have hc : cTrue (s2 g) = cTrue g := by rw [e1, e2]
      obtain ⟨h1, h2⟩ := s2_siteCost_kstar g
      have key : PhiZ (s2 g) - PhiZ g
          = ((s2 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ) := by
        unfold PhiZ; rw [hlR, hc]; ring
      rw [key]; nlinarith
  · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
    have hs0' : ¬ ShieldFires (s2 g) := by
      intro h; apply absurd h.2.1; rw [s2]; simp [hd']
    by_cases hsc : ShieldFires g ∧ g.toPathData.cut 0
    · have e1 : cTrue (s2 g)
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue
        rw [ATrue_s2, BTrue_s2,
          if_neg (fun h : ShieldFires (s2 g) ∧ (s2 g).toPathData.cut 0 => hs0' h.1), hfilt]
        simp
      have e2 : cTrue g
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card + 1 := by
        unfold cTrue; rw [if_pos hsc]
      have hkey := shield_case_delta_s2 g hsc.1 hsc.2
      have hc : (cTrue (s2 g) : ℤ) = (cTrue g : ℤ) - 1 := by rw [e1, e2]; push_cast; ring
      have key : PhiZ (s2 g) - PhiZ g
          = ((s2 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ)
            + 2 * ((0 : ℤ) - 1) := by
        unfold PhiZ; rw [hlR, hc]; ring
      rw [key, hkz]; nlinarith [hkey]
    · have e1 : cTrue (s2 g)
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue
        rw [ATrue_s2, BTrue_s2,
          if_neg (fun h : ShieldFires (s2 g) ∧ (s2 g).toPathData.cut 0 => hs0' h.1), hfilt]
        simp
      have e2 : cTrue g
          = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
        unfold cTrue; rw [if_neg hsc]; simp
      have hc : cTrue (s2 g) = cTrue g := by rw [e1, e2]
      obtain ⟨h1, h2⟩ := s2_siteCost_kstar g
      have key : PhiZ (s2 g) - PhiZ g
          = ((s2 g).toPathData.siteCost g.kstar : ℤ) - (g.toPathData.siteCost g.kstar : ℤ) := by
        unfold PhiZ; rw [hlR, hc]; ring
      rw [key]; nlinarith

/-! ### `s2`, assembled: the unconditional bound -/

theorem phiZ_dist_le_one_s2 (g : EltBridge.Elt) : (PhiZ (s2 g) - PhiZ g) ^ 2 ≤ 1 := by
  have hkw := kstar_mem_corrected_window g
  by_cases hint : g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1)
  · exact phiZ_dist_le_one_s2_interior g hint
  · by_cases hkz : g.kstar = 0
    · exact phiZ_dist_le_one_s2_boundary_zero g hkz hint
    · exact phiZ_dist_le_one_s2_boundary_ne_zero g hkz hint hkw


/-! ### `s3`: the span moves, and by how much

Unlike `s1`/`s2`, `s3` moves `kstar` (hence can move `ATrue`/`BTrue`) and changes `d` at
one edge. Two facts already proved in `EltBridge.lean` do almost all the work:
`s3_siteCost_eq` (siteCost is EXACTLY unchanged at every site, no exceptions -- so, via
`cut_iff_siteCost_zero`, `cut` status is unchanged at every site too) and
`s3_mu_dist_le_two` (mu changes by at most 2, at the one crossed edge only). What is
missing is the movement of the CORRECTED span `ATrue`/`BTrue` (`s3_A_dist_le_one`/
`s3_B_dist_le_one` are for the OLD span, built from `occ`, not `occTrue`). -/

theorem occTrue_agree_true {g : EltBridge.Elt} (hδ : g.delta = true) (j : ℤ)
    (hj : j ≠ g.kstar) : j ∈ occTrue (s3 g) ↔ j ∈ occTrue g := by
  have hk : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hδ]
  have hd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
    rw [s3, dif_pos hδ]
  have hsupp : (s3 g).supp = insert g.kstar g.supp := by rw [s3, dif_pos hδ]
  unfold occTrue
  simp only [hsupp, Finset.mem_filter, Finset.mem_insert, hd, hk]
  rw [Function.update_of_ne hj, travel_succ_ne g.kstar j hj]
  tauto

theorem occTrue_agree_false {g : EltBridge.Elt} (hδ : g.delta = false) (j : ℤ)
    (hj : j ≠ g.kstar - 1) : j ∈ occTrue (s3 g) ↔ j ∈ occTrue g := by
  have h1 : ¬ (g.delta = true) := by rw [hδ]; simp
  have hk : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1]
  have hd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
    rw [s3, dif_neg h1]
  have hsupp : (s3 g).supp = insert (g.kstar - 1) g.supp := by rw [s3, dif_neg h1]
  unfold occTrue
  simp only [hsupp, Finset.mem_filter, Finset.mem_insert, hd, hk]
  rw [Function.update_of_ne hj, travel_pred_ne g.kstar j hj]
  tauto


/-! ### `s3`'s span movement: the case an empty `occTrue` becomes a singleton

Worked out by hand first: if `occTrue g` is empty then `travel` must vanish identically
on `g` (else it would witness a nonempty `occTrue`, via `hsupp`), forcing `kstar = 0`;
and then `d` vanishes everywhere too (the same emptiness), including at the crossed edge
`p`.  So `(s3 g).d p = g.d p -+ eps = -+ eps != 0`, and since `s3` always inserts `p` into
`supp`, `p` genuinely lands in `occTrue (s3 g)`.  Combined with `occTrue_agree`, which
pins `occTrue (s3 g) \ {p} = occTrue g \ {p} = empty`, this forces
`occTrue (s3 g) = {p}` exactly -- never empty.  So an empty `occTrue` can only ever
become a SINGLETON under `s3`, never stay empty. -/

theorem occTrue_g_empty_kstar_zero {g : EltBridge.Elt} (he : occTrue g = ∅) :
    g.kstar = 0 := by
  by_contra hk
  have : (0:ℤ) ∈ occTrue g ∨ g.kstar ∈ occTrue g := by
    rcases lt_or_gt_of_ne hk with h | h
    · right
      unfold occTrue
      refine Finset.mem_filter.mpr ⟨?_, Or.inr ?_⟩
      · by_contra hns
        exact absurd (g.hsupp g.kstar hns).2 (by
          unfold SiteCost.travel; rw [if_neg (by omega), if_pos (by omega)]; omega)
      · unfold SiteCost.travel; rw [if_neg (by omega), if_pos (by omega)]; omega
    · left
      unfold occTrue
      refine Finset.mem_filter.mpr ⟨?_, Or.inr ?_⟩
      · by_contra hns
        exact absurd (g.hsupp 0 hns).2 (by
          unfold SiteCost.travel; rw [if_pos (by omega)]; omega)
      · unfold SiteCost.travel; rw [if_pos (by omega)]; omega
  rw [he] at this
  simp at this

theorem occTrue_g_empty_d_zero {g : EltBridge.Elt} (he : occTrue g = ∅) (j : ℤ) :
    g.d j = 0 := by
  by_contra hd
  have hmem : j ∈ occTrue g := by
    unfold occTrue
    by_cases hj : j ∈ g.supp
    · exact Finset.mem_filter.mpr ⟨hj, Or.inl hd⟩
    · exact absurd (g.hsupp j hj).1 hd
  rw [he] at hmem; simp at hmem

theorem occTrue_s3_singleton_of_g_empty (g : EltBridge.Elt) (he : occTrue g = ∅) :
    occTrue (s3 g) = {(if g.delta then g.kstar else g.kstar - 1)} := by
  have hkz := occTrue_g_empty_kstar_zero he
  by_cases hδ : g.delta = true
  · have hd0 : g.d g.kstar = 0 := occTrue_g_empty_d_zero he g.kstar
    have hd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
      rw [s3, dif_pos hδ]
    have hsupp : (s3 g).supp = insert g.kstar g.supp := by rw [s3, dif_pos hδ]
    have hmem : g.kstar ∈ occTrue (s3 g) := by
      unfold occTrue
      refine Finset.mem_filter.mpr ⟨by rw [hsupp]; simp, Or.inl ?_⟩
      rw [hd, Function.update_self, hd0]
      rcases g.heps with h | h <;> rw [h] <;> norm_num
    rw [if_pos hδ]
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hmem, fun x hx => ?_⟩
    by_contra hxk
    have := (occTrue_agree_true hδ x hxk).mp hx
    rw [he] at this; simp at this
  · have hδ' : g.delta = false := by revert hδ; cases g.delta <;> simp
    have hd0 : g.d (g.kstar - 1) = 0 := occTrue_g_empty_d_zero he (g.kstar - 1)
    have hd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
      rw [s3, dif_neg hδ]
    have hsupp : (s3 g).supp = insert (g.kstar - 1) g.supp := by rw [s3, dif_neg hδ]
    have hmem : (g.kstar - 1) ∈ occTrue (s3 g) := by
      unfold occTrue
      refine Finset.mem_filter.mpr ⟨by rw [hsupp]; simp, Or.inl ?_⟩
      rw [hd, Function.update_self, hd0]
      rcases g.heps with h | h <;> rw [h] <;> norm_num
    rw [if_neg hδ]
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hmem, fun x hx => ?_⟩
    by_contra hxk
    have := (occTrue_agree_false hδ' x hxk).mp hx
    rw [he] at this; simp at this


/-! ### The reverse direction: `occTrue (s3 g)` empty forces `occTrue g` a singleton

By the agree fact alone (no fresh computation needed): if `occTrue (s3 g)` is empty then
`occTrue g \ {p} = occTrue (s3 g) \ {p} = empty`, so `occTrue g ⊆ {p}`.  If it were
ALSO empty, `occTrue_s3_singleton_of_g_empty` would force `occTrue (s3 g) = {p}`,
contradicting emptiness.  So `occTrue g` is nonempty, hence exactly `{p}`. -/

theorem occTrue_g_singleton_of_s3_empty (g : EltBridge.Elt) (he : occTrue (s3 g) = ∅) :
    occTrue g = {(if g.delta then g.kstar else g.kstar - 1)} := by
  by_cases hδ : g.delta = true
  · rw [if_pos hδ]
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · by_contra hgne
      have hge : occTrue g = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        by_cases hxk : x = g.kstar
        · exact hgne (hxk ▸ hx)
        · have := (occTrue_agree_true hδ x hxk).mpr hx
          rw [he] at this; simp at this
      have := occTrue_s3_singleton_of_g_empty g hge
      rw [if_pos hδ] at this
      rw [this] at he; simp at he
    · intro x hx
      by_contra hxk
      have := (occTrue_agree_true hδ x hxk).mpr hx
      rw [he] at this; simp at this
  · have hδ' : g.delta = false := by revert hδ; cases g.delta <;> simp
    rw [if_neg hδ]
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · by_contra hgne
      have hge : occTrue g = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        by_cases hxk : x = g.kstar - 1
        · exact hgne (hxk ▸ hx)
        · have := (occTrue_agree_false hδ' x hxk).mpr hx
          rw [he] at this; simp at this
      have := occTrue_s3_singleton_of_g_empty g hge
      rw [if_neg hδ] at this
      rw [this] at he; simp at he
    · intro x hx
      by_contra hxk
      have := (occTrue_agree_false hδ' x hxk).mpr hx
      rw [he] at this; simp at this


/-! ### `ATrue` is literally the old `A` -- no new work needed

`ATrue g := min 0 ((occTrue g).min' h)` when `occTrue g` is nonempty, else `0`.  But
`insert 0 (occTrue g)` is EXACTLY `g.occ` (that is `occ`'s own definition), and the
minimum of a nonempty set with one extra point equals the minimum of the extra point
and the set's own minimum -- so `ATrue g = (insert 0 (occTrue g)).min' _ = g.occ.min' _
= g.A`.  In the empty case both sides are `0` directly.  So `s3`'s already-proved
`EltBridge.Elt.s3_A_dist_le_one` (about the OLD `A`) transfers to `ATrue` for free. -/

theorem ATrue_eq_A (g : EltBridge.Elt) : ATrue g = g.A := by
  unfold ATrue
  split_ifs with h
  · exact (Finset.min'_insert 0 (occTrue g) h).symm
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    have hset : insert (0:ℤ) (occTrue g) = {0} := by rw [h]; rfl
    show (0:ℤ) = (insert (0:ℤ) (occTrue g)).min' g.occ_nonempty
    have hgen : ∀ (S : Finset ℤ) (hS : S.Nonempty), S = {0} → S.min' hS = 0 := by
      intro S hS hS0
      subst hS0
      exact Finset.min'_singleton 0
    exact (hgen _ g.occ_nonempty hset).symm

theorem ATrue_s3_dist_le_one (g : EltBridge.Elt) :
    ATrue (s3 g) ≤ ATrue g + 1 ∧ ATrue g ≤ ATrue (s3 g) + 1 := by
  rw [ATrue_eq_A, ATrue_eq_A]; exact EltBridge.Elt.s3_A_dist_le_one g

/-! ### `BTrue`'s movement: no shortcut, but a uniform bound criterion avoids the
occTrue-emptiness case split entirely

`BTrue g = max (-1) (M)` when `occTrue g` is nonempty (`M` its max), else `-1`.  Rather
than case-splitting on emptiness of `occTrue g`/`occTrue (s3 g)` as originally planned,
one generic criterion (`BTrue_le_of_bound`) handles all combinations uniformly: to show
`BTrue g <= Y` it suffices that `Y >= -1` and every element of `occTrue g` is `<= Y` --
true vacuously when `occTrue g` is empty, so the empty/nonempty split never needs to
surface in the caller. -/

theorem neg_one_le_BTrue (g : EltBridge.Elt) : (-1 : ℤ) ≤ BTrue g := by
  unfold BTrue; split_ifs <;> omega

theorem le_BTrue {g : EltBridge.Elt} {x : ℤ} (hx : x ∈ occTrue g) : x ≤ BTrue g := by
  unfold BTrue
  have hne : (occTrue g).Nonempty := ⟨x, hx⟩
  rw [dif_pos hne]
  exact le_trans (Finset.le_max' _ x hx) (le_max_right _ _)

theorem BTrue_le_of_bound {g : EltBridge.Elt} {Y : ℤ} (hY : (-1 : ℤ) ≤ Y)
    (h : ∀ x ∈ occTrue g, x ≤ Y) : BTrue g ≤ Y := by
  unfold BTrue
  split_ifs with hne
  · exact max_le hY (Finset.max'_le _ _ _ h)
  · exact hY

/-- The two containments an `s3` step gives `occTrue`: each set differs from the other
by at most the single crossed edge `p`.  Follows directly from `occTrue_agree_true/false`
by case-splitting on whether the element in question equals `p`. -/
theorem occTrue_s3_subset (g : EltBridge.Elt) :
    ∀ x ∈ occTrue (s3 g), x = (if g.delta then g.kstar else g.kstar - 1) ∨ x ∈ occTrue g := by
  intro x hx
  by_cases hδ : g.delta = true
  · by_cases hxk : x = g.kstar
    · exact Or.inl (by rw [if_pos hδ]; exact hxk)
    · exact Or.inr ((occTrue_agree_true hδ x hxk).mp hx)
  · have hδ' : g.delta = false := by revert hδ; cases g.delta <;> simp
    by_cases hxk : x = g.kstar - 1
    · exact Or.inl (by rw [if_neg hδ]; exact hxk)
    · exact Or.inr ((occTrue_agree_false hδ' x hxk).mp hx)

theorem occTrue_g_subset (g : EltBridge.Elt) :
    ∀ x ∈ occTrue g, x = (if g.delta then g.kstar else g.kstar - 1) ∨ x ∈ occTrue (s3 g) := by
  intro x hx
  by_cases hδ : g.delta = true
  · by_cases hxk : x = g.kstar
    · exact Or.inl (by rw [if_pos hδ]; exact hxk)
    · exact Or.inr ((occTrue_agree_true hδ x hxk).mpr hx)
  · have hδ' : g.delta = false := by revert hδ; cases g.delta <;> simp
    by_cases hxk : x = g.kstar - 1
    · exact Or.inl (by rw [if_neg hδ]; exact hxk)
    · exact Or.inr ((occTrue_agree_false hδ' x hxk).mpr hx)

/-- The crossed edge `p` sits at or below BOTH `g.kstar` and `(s3 g).kstar` -- in the
`delta = true` case `p = g.kstar = (s3 g).kstar - 1`, in the `delta = false` case
`p = g.kstar - 1 = (s3 g).kstar`, so `p` equals the smaller of the two cursor
positions exactly. -/
theorem p_le_kstar_g (g : EltBridge.Elt) :
    (if g.delta then g.kstar else g.kstar - 1) ≤ g.kstar := by
  split_ifs <;> omega

theorem p_le_kstar_s3g (g : EltBridge.Elt) :
    (if g.delta then g.kstar else g.kstar - 1) ≤ (s3 g).kstar := by
  by_cases hδ : g.delta = true
  · have hk : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hδ]
    rw [if_pos hδ]; omega
  · have h1 : ¬ (g.delta = true) := by revert hδ; cases g.delta <;> simp
    have hk : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1]
    rw [if_neg hδ]; omega

/-- **`BTrue`'s `s3` movement bound, unconditional.**  No occTrue-emptiness case split
needed: `BTrue_le_of_bound` absorbs the empty case vacuously, so the only content is
"every element of the moved set is `<= BTrue g + 1`", which follows from the subset
relation (`x = p`, bounded via `p <= kstar <= BTrue g + 1` by `kstar_mem_corrected_window`,
or `x ∈ occTrue g`, bounded via `le_BTrue`), and symmetrically. -/
theorem BTrue_s3_dist_le_one (g : EltBridge.Elt) :
    BTrue (s3 g) ≤ BTrue g + 1 ∧ BTrue g ≤ BTrue (s3 g) + 1 := by
  constructor
  · apply BTrue_le_of_bound (by have := neg_one_le_BTrue g; omega)
    intro x hx
    rcases occTrue_s3_subset g x hx with hxp | hxg
    · have hk := kstar_mem_corrected_window g
      simp only [Finset.mem_Icc] at hk
      have := p_le_kstar_g g
      omega
    · have := le_BTrue hxg; omega
  · apply BTrue_le_of_bound (by have := neg_one_le_BTrue (s3 g); omega)
    intro x hx
    rcases occTrue_g_subset g x hx with hxp | hxg
    · have hk := kstar_mem_corrected_window (s3 g)
      simp only [Finset.mem_Icc] at hk
      have := p_le_kstar_s3g g
      omega
    · have := le_BTrue hxg; omega

/-! ### `cTrue`'s `s3` movement: invariant in the two degenerate (empty-window) cases

A numeric check (`s3_jump.rs`, extended this block to report `lRTrue`/`cTrue` movement
separately, not just the combined `PhiZ` jump) found something the original plan did not
anticipate: at depth 30 (3336511 elements), `max |d(cTrue)| = 0` EXACTLY, while
`max |d(lRTrue)| = 1` carries the entire jump. If that holds in general, `cTrue` is
`s3`-INVARIANT, and `phiZ_dist_le_one_s3` reduces to bounding `lRTrue` alone -- no
exchange/cancellation argument needed for `s3`, unlike `s1`/`s2`. This is evidence, not
proof (Rule 7/8: floats and finite enumeration are not proof); the two boundary-transition
cases below ARE proved, by direct computation. The general (`occTrue g` and
`occTrue (s3 g)` both nonempty) case is NOT proved this block -- see the note after. -/

theorem minOccTrue_eq_of_singleton {g : EltBridge.Elt} {c : ℤ} (h : occTrue g = {c})
    (hne : (occTrue g).Nonempty) : (occTrue g).min' hne = c := by
  have hgen : ∀ (S : Finset ℤ) (hS : S.Nonempty), S = {c} → S.min' hS = c := by
    intro S hS hS0; subst hS0; exact Finset.min'_singleton c
  exact hgen _ hne h

theorem maxOccTrue_eq_of_singleton {g : EltBridge.Elt} {c : ℤ} (h : occTrue g = {c})
    (hne : (occTrue g).Nonempty) : (occTrue g).max' hne = c := by
  have hgen : ∀ (S : Finset ℤ) (hS : S.Nonempty), S = {c} → S.max' hS = c := by
    intro S hS hS0; subst hS0; exact Finset.max'_singleton c
  exact hgen _ hne h

theorem cTrue_eq_zero_of_occTrue_empty {g : EltBridge.Elt} (he : occTrue g = ∅) :
    cTrue g = 0 := by
  have hdz := occTrue_g_empty_d_zero he
  have hA : ATrue g = 0 := by
    unfold ATrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  have hB : BTrue g = -1 := by
    unfold BTrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  unfold cTrue
  rw [hA, hB]
  have hIoo : Finset.Ioo (0:ℤ) (-1 + 1) = ∅ := by
    decide
  rw [hIoo]
  have hns : ¬ ShieldFires g := fun h => h.2.2.2.elim (fun j hj => hj.2 (hdz j))
  rw [if_neg (fun h => hns h.1)]
  simp

theorem cTrue_s3_eq_of_g_empty (g : EltBridge.Elt) (he : occTrue g = ∅) :
    cTrue (s3 g) = cTrue g := by
  rw [cTrue_eq_zero_of_occTrue_empty he]
  have hkz := occTrue_g_empty_kstar_zero he
  have hsing := occTrue_s3_singleton_of_g_empty g he
  have hne : (occTrue (s3 g)).Nonempty := by rw [hsing]; exact Finset.singleton_nonempty _
  by_cases hδ : g.delta = true
  · have hp : (if g.delta then g.kstar else g.kstar - 1) = 0 := by rw [if_pos hδ, hkz]
    rw [hp] at hsing
    have hA : ATrue (s3 g) = 0 := by
      unfold ATrue; rw [dif_pos hne, minOccTrue_eq_of_singleton hsing hne]; norm_num
    have hB : BTrue (s3 g) = 0 := by
      unfold BTrue; rw [dif_pos hne, maxOccTrue_eq_of_singleton hsing hne]; norm_num
    have hk2 : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hδ]
    have hkne : (s3 g).kstar ≠ 0 := by omega
    unfold cTrue
    rw [hA, hB]
    have hIoo : Finset.Ioo (0:ℤ) (0 + 1) = ∅ := by
      decide
    rw [hIoo, if_neg (fun h => not_shieldFires_of_kstar_ne_zero (s3 g) hkne h.1)]
    simp
  · have hδ' : g.delta = false := by revert hδ; cases g.delta <;> simp
    have h1 : ¬ (g.delta = true) := by rw [hδ']; simp
    have hp : (if g.delta then g.kstar else g.kstar - 1) = -1 := by rw [if_neg hδ]; omega
    rw [hp] at hsing
    have hA : ATrue (s3 g) = -1 := by
      unfold ATrue; rw [dif_pos hne, minOccTrue_eq_of_singleton hsing hne]; norm_num
    have hB : BTrue (s3 g) = -1 := by
      unfold BTrue; rw [dif_pos hne, maxOccTrue_eq_of_singleton hsing hne]; norm_num
    have hk2 : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1]
    have hkne : (s3 g).kstar ≠ 0 := by omega
    unfold cTrue
    rw [hA, hB]
    have hIoo : Finset.Ioo (-1:ℤ) (-1 + 1) = ∅ := by
      decide
    rw [hIoo, if_neg (fun h => not_shieldFires_of_kstar_ne_zero (s3 g) hkne h.1)]
    simp

theorem cTrue_s3_eq_of_s3g_empty (g : EltBridge.Elt) (he : occTrue (s3 g) = ∅) :
    cTrue (s3 g) = cTrue g := by
  have h0 : cTrue (s3 g) = 0 := cTrue_eq_zero_of_occTrue_empty he
  rw [h0]
  symm
  have hkz' : (s3 g).kstar = 0 := occTrue_g_empty_kstar_zero he
  have hsing := occTrue_g_singleton_of_s3_empty g he
  have hne : (occTrue g).Nonempty := by rw [hsing]; exact Finset.singleton_nonempty _
  by_cases hδ : g.delta = true
  · have hk : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hδ]
    have hgk : g.kstar = -1 := by omega
    have hp : (if g.delta then g.kstar else g.kstar - 1) = -1 := by rw [if_pos hδ, hgk]
    rw [hp] at hsing
    have hA : ATrue g = -1 := by
      unfold ATrue; rw [dif_pos hne, minOccTrue_eq_of_singleton hsing hne]; norm_num
    have hB : BTrue g = -1 := by
      unfold BTrue; rw [dif_pos hne, maxOccTrue_eq_of_singleton hsing hne]; norm_num
    have hgkne : g.kstar ≠ 0 := by omega
    unfold cTrue
    rw [hA, hB]
    have hIoo : Finset.Ioo (-1:ℤ) (-1 + 1) = ∅ := by
      decide
    rw [hIoo, if_neg (fun h => not_shieldFires_of_kstar_ne_zero g hgkne h.1)]
    simp
  · have hδ' : g.delta = false := by revert hδ; cases g.delta <;> simp
    have h1 : ¬ (g.delta = true) := by rw [hδ']; simp
    have hk : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1]
    have hgk : g.kstar = 1 := by omega
    have hp : (if g.delta then g.kstar else g.kstar - 1) = 0 := by rw [if_neg hδ]; omega
    rw [hp] at hsing
    have hA : ATrue g = 0 := by
      unfold ATrue; rw [dif_pos hne, minOccTrue_eq_of_singleton hsing hne]; norm_num
    have hB : BTrue g = 0 := by
      unfold BTrue; rw [dif_pos hne, maxOccTrue_eq_of_singleton hsing hne]; norm_num
    have hgkne : g.kstar ≠ 0 := by omega
    unfold cTrue
    rw [hA, hB]
    have hIoo : Finset.Ioo (0:ℤ) (0 + 1) = ∅ := by
      decide
    rw [hIoo, if_neg (fun h => not_shieldFires_of_kstar_ne_zero g hgkne h.1)]
    simp

/-! `cTrue_s3_eq` (BOTH `occTrue g` and `occTrue (s3 g)` nonempty) is NOT proved here.
Attempted approach: `occTrue_s3_subset`/`occTrue_g_subset` pin the symmetric difference to
`{p}`, so the window can gain or lose at most one occupied edge; the obstruction is that
this can ALSO shift which SITE is the boundary of the interior `Ioo` range, so a site can
move from excluded-boundary to counted-interior (or vice versa) at the same step that `p`
itself enters or leaves the edge set -- two coupled effects, not one, and unlike the
empty-window cases there is no computation forcing both effects into `Ioo (0,0)`. This is
exactly the "exact cancellation, not better bookkeeping" difficulty the file header
already named. Left open; the numeric evidence above says the cancellation is real, not
that it is easy. -/

/-! ### `cTrue`'s `s3` movement in the both-nonempty case: mechanism fully diagnosed
numerically, not yet formalized

A second numeric pass (extending `s3_jump.rs` further) pinned the exact mechanism, and
refutes a hoped-for shortcut. Over the 1546464 both-nonempty pairs where a window
boundary actually shifts (confirmed separately: never both boundaries at once, `0`
violations over 3336503 pairs), the newly-interior site IS a cut site in `1540` of them
(so "the new site is never a cut" is WRONG -- retracting that hypothesis explicitly,
tried this block before the check). But in every one of those `1540` cases, the boundary
shield's firing status flips between `g` and `s3 g` to exactly compensate
(`1540 / 1540`). So the mechanism is a genuine shield/interior-count exchange,
structurally the same KIND of cancellation `exchange_sq_le_one` was built for on
`s1`/`s2` -- not a "nothing changes" argument, and NOT reducible to a simpler
"window unchanged implies ShieldFires unchanged" shortcut either: a first attempt at that
shortcut this block was caught, before being committed, as false in general -- `ShieldFires`
can hold for `g` (with `cut 0` true) while `g.kstar = 0` and the window happens not to
move, and `ShieldFires (s3 g)` is then automatically false (`kstar` can be `0` for at most
one of `g`, `s3 g`), so the two `ShieldFires` values genuinely can differ even with an
unchanged window; the overall `cTrue` equality in that sub-case must still be going
through a `cut 0` compensation, not a `ShieldFires` invariance. `cTrue_s3_eq` (any form)
is NOT proved this block. This is now a complete, verified-by-enumeration description of
the mechanism; formalizing the shield-flip exchange is the concrete next step, and it
should be built on the general exchange machinery (`exchange_le_one`/`exchange_sq_le_one`)
already in this file for `s1`/`s2`, not on a fresh invariance lemma. -/

theorem cut_s3_eq (g : EltBridge.Elt) (s : ℤ) :
    (s3 g).toPathData.cut s ↔ g.toPathData.cut s := by
  rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero, EltBridge.Elt.s3_siteCost_eq]


#print axioms PhiLipschitz.interior_filter_s1_eq
#print axioms PhiLipschitz.phiZ_dist_le_one_s1_boundary_zero
#print axioms PhiLipschitz.phiZ_dist_le_one_s1
#print axioms PhiLipschitz.interior_filter_s2_eq
#print axioms PhiLipschitz.phiZ_dist_le_one_s2_boundary_zero
#print axioms PhiLipschitz.phiZ_dist_le_one_s2
#print axioms PhiLipschitz.cTrue_s2_eq_of_not_interior_ne_zero
#print axioms PhiLipschitz.phiZ_dist_le_one_s2_boundary_ne_zero
#print axioms PhiLipschitz.occTrue_agree_true
#print axioms PhiLipschitz.occTrue_agree_false
#print axioms PhiLipschitz.occTrue_g_empty_kstar_zero
#print axioms PhiLipschitz.occTrue_g_empty_d_zero
#print axioms PhiLipschitz.occTrue_s3_singleton_of_g_empty
#print axioms PhiLipschitz.occTrue_g_singleton_of_s3_empty
#print axioms PhiLipschitz.ATrue_eq_A
#print axioms PhiLipschitz.ATrue_s3_dist_le_one

/-! ### A sharper mechanism for the both-nonempty case: `ShieldFires` pins `ATrue` to `0`

A third numeric pass (`s3_jump.rs`, printing the concrete witnesses where the
newly-interior site is a cut) found the special role of site `0` directly: in every
witness, the boundary that moves is exactly `ATrue` crossing `0` (`0 <-> -1`), on
whichever side has `kstar = 0`. That is not a coincidence: `ShieldFires` forces
`travel kstar _ = 0` everywhere (via `SiteCost.travel_of_kstar_zero`, since it requires
`kstar = 0`) and forbids any deposit at a negative edge, so every occupied edge of a
`ShieldFires` element sits at `>= 0` -- pinning `ATrue` to exactly `0`, not merely
`<= 0`. This explains why the exchange only ever involves site `0`: it is the one site
the `ShieldFires`-clamp forces to be the window's own left edge, so it is EXACTLY the
site that flips between "excluded boundary" and "counted interior" when `kstar` moves
away from `0`. `cTrue_s3_eq`'s both-nonempty case is still open, but the remaining
casework is now: (a) neither side has `kstar = 0` -- expected to reduce to "the
newly-interior site is never a cut", by the same `vD`/`vArr` mechanism that makes
`betaAt`/`alphaAt` nonzero at a nonzero `kstar`'s neighbouring site (checked by hand for
one of the four directional sub-cases, not yet for all four, not yet formalized); (b)
`kstar = 0` on one side -- the shield-to-interior transfer this lemma sets up, not yet
assembled into the full equality. -/

theorem ATrue_eq_zero_of_shieldFires {g : EltBridge.Elt} (h : ShieldFires g) :
    ATrue g = 0 := by
  obtain ⟨hk0, -, hneg, -⟩ := h
  unfold ATrue
  split_ifs with hne
  · have hmin : ∀ x ∈ occTrue g, 0 ≤ x := by
      intro x hx
      unfold occTrue at hx
      rw [Finset.mem_filter] at hx
      rcases hx.2 with hd | hf
      · by_contra hxneg
        exact hd (hneg x (by omega))
      · exact absurd hf (by rw [hk0]; simp [SiteCost.travel_of_kstar_zero])
    have h0 : 0 ≤ (occTrue g).min' hne := hmin _ (Finset.min'_mem (occTrue g) hne)
    exact min_eq_left h0
  · rfl

/-! ### Two of the four generic-case direction lemmas: never a cut at the crossed site

Concrete formulas, matching the exhaustive-enumeration finding exactly (`0` cut
violations among 1524400 both-nonempty boundary shifts with `kstar != 0` on both
sides). Two of the four directional sub-cases (`delta = true` growth, `delta = false`
growth); the two shrink-direction sub-cases and their assembly into `cTrue_s3_eq` are
not done here. -/

theorem not_cut_kstar_of_delta_true (g : EltBridge.Elt) (hd : g.delta = true)
    (hdk : g.d g.kstar = 0) : ¬ g.toPathData.cut g.kstar := by
  rintro ⟨-, hb, -⟩
  have hvR : SiteCost.PathData.vR g.toPathData g.kstar = 1 := by
    unfold SiteCost.PathData.vR SiteCost.PathData.vD
    have : g.toPathData.delta = true := hd
    simp [this]
  unfold SiteCost.PathData.betaAt at hb
  rw [hvR] at hb
  simp only [EltBridge.Elt.toPathData] at hb hdk
  rw [hdk] at hb
  rcases g.heps with h | h <;> rw [h] at hb <;> norm_num at hb

theorem not_cut_kstar_of_delta_false (g : EltBridge.Elt) (hd : g.delta = false)
    (hk0 : g.kstar ≠ 0) (hdk : g.d (g.kstar - 1) = 0) :
    ¬ g.toPathData.cut g.kstar := by
  rintro ⟨ha, -, -⟩
  have hvL : SiteCost.PathData.vL g.toPathData g.kstar = 1 := by
    unfold SiteCost.PathData.vL SiteCost.PathData.vD
    have : g.toPathData.delta = false := hd
    simp [this]
  have hvArr : SiteCost.vArr g.kstar = 0 := by unfold SiteCost.vArr; simp [hk0]
  unfold SiteCost.PathData.alphaAt at ha
  rw [hvL, hvArr] at ha
  simp only [EltBridge.Elt.toPathData] at ha hdk
  rw [hdk] at ha
  rcases g.heps with h | h <;> rw [h] at ha <;> norm_num at ha

/-! ### The two shrink-direction lemmas: all four generic-case directions now done

Worked out by hand this block, correcting the site convention once more: for a
window SHRINK, the site whose cut-status matters depends on WHICH side shrinks --
`kstar + 1` for the `delta = true` (`A`-side) shrink (uses `alphaAt`, which has the
`vArr` term, hence needs the `kstar + 1 != 0` gate -- exactly where `ShieldFires`
becomes newly eligible on the `s3 g` side), but the crossed edge `kstar - 1` ITSELF
for the `delta = false` (`B`-side) shrink (uses `betaAt`, which has NO `vArr` term at
all, so no gate is needed -- even at `kstar = 1`, where `(s3 g).kstar = 0`, `ShieldFires
(s3 g)` cannot fire regardless, because `s3` also flips `delta` to `true` there and
`ShieldFires` requires `delta = false`). This asymmetry (`alphaAt` carries `vArr`,
`betaAt` does not) is exactly why growth/shrink pair up with `alphaAt`/`betaAt`
oppositely by side: `delta = true` growth and `delta = false` shrink both use `betaAt`
(no gate); `delta = true` shrink and `delta = false` growth both use `alphaAt` (gated). -/

theorem not_cut_kstarSucc_of_delta_true (g : EltBridge.Elt) (hd : g.delta = true)
    (hk1 : g.kstar + 1 ≠ 0) (hdk : g.d g.kstar = g.eps) :
    ¬ g.toPathData.cut (g.kstar + 1) := by
  rintro ⟨ha, -, -⟩
  have hvL : SiteCost.PathData.vL g.toPathData (g.kstar + 1) = 0 := by
    unfold SiteCost.PathData.vL
    have : g.toPathData.delta = true := hd
    simp [this]
  have hvArr : SiteCost.vArr (g.kstar + 1) = 0 := by unfold SiteCost.vArr; simp [hk1]
  unfold SiteCost.PathData.alphaAt at ha
  rw [hvL, hvArr] at ha
  simp only [EltBridge.Elt.toPathData] at ha hdk
  have : g.kstar + 1 - 1 = g.kstar := by ring
  rw [this, hdk] at ha
  rcases g.heps with h | h <;> rw [h] at ha <;> norm_num at ha

theorem not_cut_kstarPred_of_delta_false (g : EltBridge.Elt) (hd : g.delta = false)
    (hdk : g.d (g.kstar - 1) = -g.eps) :
    ¬ g.toPathData.cut (g.kstar - 1) := by
  rintro ⟨-, hb, -⟩
  have hvR : SiteCost.PathData.vR g.toPathData (g.kstar - 1) = 0 := by
    unfold SiteCost.PathData.vR
    have : g.toPathData.delta = false := hd
    simp [this]
  unfold SiteCost.PathData.betaAt at hb
  rw [hvR] at hb
  simp only [EltBridge.Elt.toPathData] at hb hdk
  rw [hdk] at hb
  rcases g.heps with h | h <;> rw [h] at hb <;> norm_num at hb

/-! ### `ShieldFires g` forces the window to move -- the "neither moves" case is trivial

A numeric check (with the CORRECT `ShieldFires` predicate this time -- an earlier probe
this block used the weaker `kstar = 0 ∧ delta = false` alone and wrongly found `53715`
apparent counterexamples, all of which vanished once the `d`-conditions were checked
too) confirms `0` cases where `ShieldFires` genuinely holds on either side while the
window stays put. Proved here directly: `ShieldFires g` forces `ATrue g = 0`
(`ATrue_eq_zero_of_shieldFires`) and forces the crossed edge `g.kstar - 1 = -1` into
`occTrue (s3 g)` via `travel` alone (`SiteCost.travel` at the new `kstar = -1` is
nonzero at `j = -1` unconditionally), giving `ATrue (s3 g) ≤ -1 < 0 = ATrue g`. So
`ShieldFires g` and "the window doesn't move" cannot hold together. -/

theorem shieldFires_forces_ATrue_move (g : EltBridge.Elt) (h : ShieldFires g) :
    ATrue (s3 g) ≠ ATrue g := by
  have hk0 : g.kstar = 0 := h.1
  have hδ : g.delta = false := h.2.1
  have hAg : ATrue g = 0 := ATrue_eq_zero_of_shieldFires h
  have h1 : ¬ (g.delta = true) := by rw [hδ]; simp
  have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1]
  have hkS' : (s3 g).kstar = -1 := by omega
  have htrav : SiteCost.travel (s3 g).kstar (-1) ≠ 0 := by
    rw [hkS']; unfold SiteCost.travel; rw [if_neg (by omega), if_pos (by omega)]; omega
  have hmem : (-1 : ℤ) ∈ occTrue (s3 g) := by
    unfold occTrue
    by_cases hj : (-1 : ℤ) ∈ (s3 g).supp
    · exact Finset.mem_filter.mpr ⟨hj, Or.inr htrav⟩
    · exact absurd ((s3 g).hsupp (-1) hj).2 htrav
  have hne : (occTrue (s3 g)).Nonempty := ⟨-1, hmem⟩
  have hle : ATrue (s3 g) ≤ -1 := by
    unfold ATrue
    rw [dif_pos hne]
    exact le_trans (min_le_right _ _) (Finset.min'_le _ _ hmem)
  omega

theorem shieldFires_s3_forces_ATrue_move (g : EltBridge.Elt) (h : ShieldFires (s3 g)) :
    ATrue (s3 g) ≠ ATrue g := by
  have hk0 : (s3 g).kstar = 0 := h.1
  have hδ : (s3 g).delta = false := h.2.1
  have hAs3g : ATrue (s3 g) = 0 := ATrue_eq_zero_of_shieldFires h
  have hgd : g.delta = true := by
    by_contra hc
    have hδ' : g.delta = false := by revert hc; cases g.delta <;> simp
    have h1 : ¬ (g.delta = true) := by rw [hδ']; simp
    have : (s3 g).delta = true := by rw [s3, dif_neg h1]
    rw [this] at hδ; exact absurd hδ (by simp)
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hgd]
  have hgk : g.kstar = -1 := by omega
  have htrav : SiteCost.travel g.kstar (-1) ≠ 0 := by
    rw [hgk]; unfold SiteCost.travel; rw [if_neg (by omega), if_pos (by omega)]; omega
  have hmem : (-1 : ℤ) ∈ occTrue g := by
    unfold occTrue
    by_cases hj : (-1 : ℤ) ∈ g.supp
    · exact Finset.mem_filter.mpr ⟨hj, Or.inr htrav⟩
    · exact absurd (g.hsupp (-1) hj).2 htrav
  have hne : (occTrue g).Nonempty := ⟨-1, hmem⟩
  have hle : ATrue g ≤ -1 := by
    unfold ATrue
    rw [dif_pos hne]
    exact le_trans (min_le_right _ _) (Finset.min'_le _ _ hmem)
  omega

theorem cTrue_s3_eq_of_window_unchanged (g : EltBridge.Elt)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g) :
    cTrue (s3 g) = cTrue g := by
  have hnf1 : ¬ ShieldFires g := fun h => shieldFires_forces_ATrue_move g h hA
  have hnf2 : ¬ ShieldFires (s3 g) := fun h => shieldFires_s3_forces_ATrue_move g h hA
  unfold cTrue
  rw [hA, hB]
  have hfilter : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s3 g).toPathData.cut
      = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut :=
    Finset.filter_congr (fun x _ => by rw [cut_s3_eq])
  rw [hfilter, if_neg (fun h => hnf2 h.1), if_neg (fun h => hnf1 h.1)]

/-! ### A single point can move at most one of a Finset's min/max, never both

General fact, not specific to `occTrue`: if two nonempty `Finset ℤ`s agree off a single
point `p`, at least one of their `min'`/`max'` is shared. This is the PROOF of the
"boundaries never move simultaneously" finding logged several blocks ago as a numeric
measurement (0 violations over 3336503 pairs) -- not a re-measurement of it. -/

theorem min'_congr_of_eq {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : A = B) : A.min' hA = B.min' hB := by subst h; rfl

theorem max'_congr_of_eq {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : A = B) : A.max' hA = B.max' hB := by subst h; rfl

theorem min_or_max_unchanged {S S' : Finset ℤ} (hS : S.Nonempty) (hS' : S'.Nonempty)
    {p : ℤ} (hsymm : ∀ x : ℤ, x ≠ p → (x ∈ S ↔ x ∈ S')) :
    S.min' hS = S'.min' hS' ∨ S.max' hS = S'.max' hS' := by
  by_cases hpS : p ∈ S
  · by_cases hpS' : p ∈ S'
    · left
      have heq : S = S' := by
        ext x
        by_cases hx : x = p
        · subst hx; exact ⟨fun _ => hpS', fun _ => hpS⟩
        · exact hsymm x hx
      exact min'_congr_of_eq hS hS' heq
    · set T := S.erase p with hTdef
      have hTS' : T = S' := by
        ext x
        rw [hTdef, Finset.mem_erase]
        constructor
        · rintro ⟨hne, hx⟩; exact (hsymm x hne).mp hx
        · intro hx
          refine ⟨fun h => hpS' (h ▸ hx), ?_⟩
          exact (hsymm x (fun h => hpS' (h ▸ hx))).mpr hx
      have hSins : S = insert p T := (Finset.insert_erase hpS).symm
      have hTne : T.Nonempty := hTS' ▸ hS'
      have hpT : p ∉ T := fun h => (Finset.mem_erase.mp h).1 rfl
      have hne_min : p ≠ T.min' hTne := fun h => hpT (by rw [h]; exact T.min'_mem hTne)
      rcases lt_or_gt_of_ne hne_min with hlt | hgt
      · right
        have hmax : S.max' hS = max p (T.max' hTne) := by
          rw [max'_congr_of_eq hS (Finset.insert_nonempty p T) hSins]
          exact Finset.max'_insert p T hTne
        have hple : p ≤ T.max' hTne := le_trans hlt.le (T.min'_le_max' hTne)
        rw [hmax, max_eq_right hple, max'_congr_of_eq hTne hS' hTS']
      · left
        have hmin : S.min' hS = min p (T.min' hTne) := by
          rw [min'_congr_of_eq hS (Finset.insert_nonempty p T) hSins]
          exact Finset.min'_insert p T hTne
        rw [hmin, min_eq_right hgt.le, min'_congr_of_eq hTne hS' hTS']
  · by_cases hpS' : p ∈ S'
    · set T := S'.erase p with hTdef
      have hTS : T = S := by
        ext x
        rw [hTdef, Finset.mem_erase]
        constructor
        · rintro ⟨hne, hx⟩; exact (hsymm x hne).mpr hx
        · intro hx
          refine ⟨fun h => hpS (h ▸ hx), ?_⟩
          exact (hsymm x (fun h => hpS (h ▸ hx))).mp hx
      have hS'ins : S' = insert p T := (Finset.insert_erase hpS').symm
      have hTne : T.Nonempty := hTS ▸ hS
      have hpT : p ∉ T := fun h => (Finset.mem_erase.mp h).1 rfl
      have hne_min : p ≠ T.min' hTne := fun h => hpT (by rw [h]; exact T.min'_mem hTne)
      rcases lt_or_gt_of_ne hne_min with hlt | hgt
      · right
        have hmax : S'.max' hS' = max p (T.max' hTne) := by
          rw [max'_congr_of_eq hS' (Finset.insert_nonempty p T) hS'ins]
          exact Finset.max'_insert p T hTne
        have hple : p ≤ T.max' hTne := le_trans hlt.le (T.min'_le_max' hTne)
        rw [hmax, max_eq_right hple, max'_congr_of_eq hTne hS hTS]
      · left
        have hmin : S'.min' hS' = min p (T.min' hTne) := by
          rw [min'_congr_of_eq hS' (Finset.insert_nonempty p T) hS'ins]
          exact Finset.min'_insert p T hTne
        rw [hmin, min_eq_right hgt.le, min'_congr_of_eq hTne hS hTS]
    · left
      have heq : S = S' := by
        ext x
        by_cases hx : x = p
        · subst hx; exact ⟨fun h => absurd h hpS, fun h => absurd h hpS'⟩
        · exact hsymm x hx
      exact min'_congr_of_eq hS hS' heq

/-! ### Generic filter-card-under-one-site-shift lemmas, for assembling `cTrue_s3_eq`

Two reusable, purely combinatorial facts (not specific to `cTrue`/`occTrue` at all):
growing an `Ioo` range by one site on either end changes its filter-card by exactly
`0` or `1`, and by `0` precisely when the new site fails the predicate. These are the
arithmetic half of the `cTrue_s3_eq` assembly; the remaining half (proving WHICH
direction applies and that the shift is by exactly `+1`/`-1`, from the growth/removal
hypotheses each of the four direction lemmas needs) is not done yet -- see the note
after. -/

theorem ioo_insert_right {A B : ℤ} (h : A < B + 1) :
    Finset.Ioo A (B + 2) = insert (B + 1) (Finset.Ioo A (B + 1)) := by
  ext x; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega

theorem ioo_insert_left {A B : ℤ} (h : A < B + 1) :
    Finset.Ioo (A - 1) (B + 1) = insert A (Finset.Ioo A (B + 1)) := by
  ext x; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega

theorem card_filter_insert_right (C : ℤ → Prop) [DecidablePred C] {A B : ℤ}
    (h : A < B + 1) (hnc : ¬ C (B + 1)) :
    ((Finset.Ioo A (B + 2)).filter C).card = ((Finset.Ioo A (B + 1)).filter C).card := by
  rw [ioo_insert_right h, Finset.filter_insert, if_neg hnc]

theorem card_filter_insert_left (C : ℤ → Prop) [DecidablePred C] {A B : ℤ}
    (h : A < B + 1) (hnc : ¬ C A) :
    ((Finset.Ioo (A - 1) (B + 1)).filter C).card = ((Finset.Ioo A (B + 1)).filter C).card := by
  rw [ioo_insert_left h, Finset.filter_insert, if_neg hnc]

/-! `cTrue_s3_eq`'s last case (both `occTrue` nonempty, window moves) is STILL open
after landing these. What's missing is the LINKING step: from a direction lemma's
hypothesis (e.g. `g.delta = true`, `g.d g.kstar = 0`, the growth condition), derive the
CONCRETE fact `BTrue (s3 g) = BTrue g + 1` (not just `<= BTrue g + 1` from the
already-proved `BTrue_s3_dist_le_one`) -- i.e. that the window genuinely grows by
exactly one on that side, using `kstar_mem_corrected_window` and the membership
structure of `occTrue (s3 g) = occTrue g ∪ {p}` to pin `BTrue (s3 g) = max (-1) p`
exactly. Not done this block; the combinatorial half above is ready for it. -/

/-! ### `cTrue_s3_eq` for the "`BTrue` increases by exactly 1" case

The identification step: whenever `BTrue` genuinely increases, the crossed edge `p` IS
the new maximum (not merely bounded by it) -- because `occTrue g`/`occTrue (s3 g)` can
only differ at `p` (`occTrue_s3_subset`), so if the actual maximum of `occTrue (s3 g)`
were something OTHER than `p`, it would already have been present in `occTrue g` too,
capping `BTrue g` at that same value and contradicting the increase. -/

theorem occTrue_agree_off_p (g : EltBridge.Elt) (x : ℤ)
    (hx : x ≠ (if g.delta then g.kstar else g.kstar - 1)) :
    x ∈ occTrue g ↔ x ∈ occTrue (s3 g) := by
  constructor
  · intro h
    rcases occTrue_g_subset g x h with hxp | hxs
    · exact absurd hxp hx
    · exact hxs
  · intro h
    rcases occTrue_s3_subset g x h with hxp | hxg
    · exact absurd hxp hx
    · exact hxg

theorem crossed_eq_of_Bincrease (g : EltBridge.Elt) (h2 : (occTrue (s3 g)).Nonempty)
    (hB : BTrue (s3 g) = BTrue g + 1) :
    (if g.delta then g.kstar else g.kstar - 1) = BTrue (s3 g) := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hunfold : BTrue (s3 g) = max (-1) ((occTrue (s3 g)).max' h2) := by
    unfold BTrue; rw [dif_pos h2]
  have hge : (-1 : ℤ) ≤ BTrue g := neg_one_le_BTrue g
  have hM' : BTrue (s3 g) = (occTrue (s3 g)).max' h2 := by omega
  have hmem : (occTrue (s3 g)).max' h2 ∈ occTrue (s3 g) := Finset.max'_mem _ h2
  by_cases heqp : (occTrue (s3 g)).max' h2 = p
  · rw [← hM'] at heqp; exact heqp.symm
  · exfalso
    have hMg : (occTrue (s3 g)).max' h2 ∈ occTrue g :=
      (occTrue_s3_subset g _ hmem).resolve_left heqp
    have hle : (occTrue (s3 g)).max' h2 ≤ BTrue g := le_BTrue hMg
    rw [← hM'] at hle
    omega

/-- The crossed edge is genuinely NOT in `occTrue g` when `BTrue` increases -- else
`occTrue g` and `occTrue (s3 g)` would agree everywhere (including at `p`), forcing
`BTrue g = BTrue (s3 g)`, contradicting the increase. -/
theorem crossed_not_mem_g_of_Bincrease (g : EltBridge.Elt) (h2 : (occTrue (s3 g)).Nonempty)
    (hB : BTrue (s3 g) = BTrue g + 1) :
    (if g.delta then g.kstar else g.kstar - 1) ∉ occTrue g := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  intro hpg
  have hunfold : BTrue (s3 g) = max (-1) ((occTrue (s3 g)).max' h2) := by
    unfold BTrue; rw [dif_pos h2]
  have hge : (-1 : ℤ) ≤ BTrue g := neg_one_le_BTrue g
  have hM' : BTrue (s3 g) = (occTrue (s3 g)).max' h2 := by omega
  have hpg' : p ∈ occTrue (s3 g) := by
    rw [hpdef, crossed_eq_of_Bincrease g h2 hB, hM']; exact Finset.max'_mem _ h2
  have heq : occTrue g = occTrue (s3 g) := by
    ext x
    by_cases hx : x = p
    · subst hx; exact ⟨fun _ => hpg', fun _ => hpg⟩
    · exact occTrue_agree_off_p g x hx
  have hBeq : BTrue g = BTrue (s3 g) := by
    unfold BTrue
    rw [heq]
  omega

theorem d_crossed_eq_zero_of_Bincrease (g : EltBridge.Elt) (h2 : (occTrue (s3 g)).Nonempty)
    (hB : BTrue (s3 g) = BTrue g + 1) :
    g.d (if g.delta then g.kstar else g.kstar - 1) = 0 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hnm := crossed_not_mem_g_of_Bincrease g h2 hB
  by_contra hd
  apply hnm
  unfold occTrue
  by_cases hj : p ∈ g.supp
  · exact Finset.mem_filter.mpr ⟨hj, Or.inl hd⟩
  · exact absurd (g.hsupp p hj).1 hd

theorem not_shieldFires_of_delta_true (g : EltBridge.Elt) (hd : g.delta = true) :
    ¬ ShieldFires g := fun h => by
  have hf : g.delta = false := h.2.1
  rw [hd] at hf
  exact absurd hf (by decide)

theorem cTrue_s3_eq_of_Bincrease_delta_true (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g + 1)
    (hd : g.delta = true) (hk2 : (s3 g).kstar ≠ 0) :
    cTrue (s3 g) = cTrue g := by
  have hdk : g.d g.kstar = 0 := by
    have := d_crossed_eq_zero_of_Bincrease g h2 hB
    rwa [if_pos hd] at this
  have hnc : ¬ g.toPathData.cut g.kstar := not_cut_kstar_of_delta_true g hd hdk
  have hkeq : g.kstar = BTrue g + 1 := by
    have hc := crossed_eq_of_Bincrease g h2 hB
    rw [if_pos hd] at hc
    omega
  have hnc2 : ¬ g.toPathData.cut (BTrue g + 1) := hkeq ▸ hnc
  obtain ⟨x, hx⟩ := h1
  have hAle : ATrue g ≤ x := by
    unfold ATrue
    rw [dif_pos ⟨x, hx⟩]
    exact le_trans (min_le_right _ _) (Finset.min'_le _ _ hx)
  have hAB : ATrue g ≤ BTrue g := le_trans hAle (le_BTrue hx)
  have hfilter : ((Finset.Ioo (ATrue g) (BTrue g + 2)).filter (s3 g).toPathData.cut).card
      = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
    rw [Finset.filter_congr (fun x (_ : x ∈ Finset.Ioo (ATrue g) (BTrue g + 2)) => cut_s3_eq g x)]
    exact card_filter_insert_right g.toPathData.cut (by omega) hnc2
  have hshield1 : ¬ ShieldFires g := not_shieldFires_of_delta_true g hd
  have hshield2 : ¬ ShieldFires (s3 g) := not_shieldFires_of_kstar_ne_zero (s3 g) hk2
  unfold cTrue
  rw [hA, hB, if_neg (fun h => hshield2 h.1), if_neg (fun h => hshield1 h.1)]
  have hBB : BTrue g + 1 + 1 = BTrue g + 2 := by ring
  rw [hBB]
  omega

/-! ### `cTrue_s3_eq` for the "`ATrue` decreases by exactly 1" case -- the mirror

Same technique as the `BTrue`-increase case, mirrored: the identification chain, then
one assembled direction (`delta = false`), using the OTHER two direction lemmas
(`not_cut_kstar_of_delta_false`, needing the growth condition at site `g.kstar`, and
`card_filter_insert_left`). -/

theorem ATrue_le {g : EltBridge.Elt} {x : ℤ} (hx : x ∈ occTrue g) : ATrue g ≤ x := by
  unfold ATrue
  have hne : (occTrue g).Nonempty := ⟨x, hx⟩
  rw [dif_pos hne]
  exact le_trans (min_le_right _ _) (Finset.min'_le _ _ hx)

theorem atrue_le_zero (g : EltBridge.Elt) : ATrue g ≤ 0 := by
  unfold ATrue; split_ifs <;> omega

theorem crossed_eq_of_Adecrease (g : EltBridge.Elt) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g - 1) :
    (if g.delta then g.kstar else g.kstar - 1) = ATrue (s3 g) := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hunfold : ATrue (s3 g) = min 0 ((occTrue (s3 g)).min' h2) := by
    unfold ATrue; rw [dif_pos h2]
  have hle : ATrue g ≤ 0 := atrue_le_zero g
  have hmin : ATrue (s3 g) = (occTrue (s3 g)).min' h2 := by omega
  have hmem : (occTrue (s3 g)).min' h2 ∈ occTrue (s3 g) := Finset.min'_mem _ h2
  by_cases heqp : (occTrue (s3 g)).min' h2 = p
  · rw [← hmin] at heqp; exact heqp.symm
  · exfalso
    have hMg : (occTrue (s3 g)).min' h2 ∈ occTrue g :=
      (occTrue_s3_subset g _ hmem).resolve_left heqp
    have hge2 : ATrue g ≤ (occTrue (s3 g)).min' h2 := ATrue_le hMg
    rw [← hmin] at hge2
    omega

theorem crossed_not_mem_g_of_Adecrease (g : EltBridge.Elt) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g - 1) :
    (if g.delta then g.kstar else g.kstar - 1) ∉ occTrue g := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  intro hpg
  have hunfold : ATrue (s3 g) = min 0 ((occTrue (s3 g)).min' h2) := by
    unfold ATrue; rw [dif_pos h2]
  have hle : ATrue g ≤ 0 := atrue_le_zero g
  have hmin : ATrue (s3 g) = (occTrue (s3 g)).min' h2 := by omega
  have hpg' : p ∈ occTrue (s3 g) := by
    rw [hpdef, crossed_eq_of_Adecrease g h2 hA, hmin]; exact Finset.min'_mem _ h2
  have heq : occTrue g = occTrue (s3 g) := by
    ext x
    by_cases hx : x = p
    · subst hx; exact ⟨fun _ => hpg', fun _ => hpg⟩
    · exact occTrue_agree_off_p g x hx
  have hAeq : ATrue g = ATrue (s3 g) := by
    unfold ATrue
    rw [heq]
  omega

theorem d_crossed_eq_zero_of_Adecrease (g : EltBridge.Elt) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g - 1) :
    g.d (if g.delta then g.kstar else g.kstar - 1) = 0 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hnm := crossed_not_mem_g_of_Adecrease g h2 hA
  by_contra hd
  apply hnm
  unfold occTrue
  by_cases hj : p ∈ g.supp
  · exact Finset.mem_filter.mpr ⟨hj, Or.inl hd⟩
  · exact absurd (g.hsupp p hj).1 hd

theorem cTrue_s3_eq_of_Adecrease_delta_false (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g - 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = false) (hk1 : g.kstar ≠ 0) :
    cTrue (s3 g) = cTrue g := by
  have hdk : g.d (g.kstar - 1) = 0 := by
    have := d_crossed_eq_zero_of_Adecrease g h2 hA
    rwa [if_neg (by rw [hd]; simp)] at this
  have hnc : ¬ g.toPathData.cut g.kstar := not_cut_kstar_of_delta_false g hd hk1 hdk
  have hkeq : g.kstar = ATrue g := by
    have hc := crossed_eq_of_Adecrease g h2 hA
    rw [if_neg (by rw [hd]; simp)] at hc
    omega
  have hnc2 : ¬ g.toPathData.cut (ATrue g) := hkeq ▸ hnc
  obtain ⟨x, hx⟩ := h1
  have hBge : x ≤ BTrue g := le_BTrue hx
  have hAB : ATrue g ≤ BTrue g := le_trans (ATrue_le hx) hBge
  have hfilter : ((Finset.Ioo (ATrue g - 1) (BTrue g + 1)).filter (s3 g).toPathData.cut).card
      = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
    rw [Finset.filter_congr (fun x (_ : x ∈ Finset.Ioo (ATrue g - 1) (BTrue g + 1)) => cut_s3_eq g x)]
    exact card_filter_insert_left g.toPathData.cut (by omega) hnc2
  have hshield1 : ¬ ShieldFires g := not_shieldFires_of_kstar_ne_zero g hk1
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hd2 : (s3 g).delta = true := by rw [s3, dif_neg h1']
  have hshield2 : ¬ ShieldFires (s3 g) := not_shieldFires_of_delta_true (s3 g) hd2
  unfold cTrue
  rw [hA, hB, if_neg (fun h => hshield2 h.1), if_neg (fun h => hshield1 h.1)]
  omega

/-! ### The other two directions are impossible when `kstar != 0` on both sides

Proves what the last-but-one block only measured (`0` occurrences of `B`-growth with
`delta = false` / `A`-growth with `delta = true`): `d_crossed_eq_zero_of_Bincrease`
already gives `g.d p = 0`; the SAME emptiness (`p ∉ occTrue g`) also forces
`travel g.kstar p = 0`, and for `delta = false` that pins `g.kstar <= 0`
(`travel g.kstar (g.kstar - 1)` is nonzero exactly when `g.kstar >= 1`), hence
(`kstar != 0`) `g.kstar <= -1`, hence `p = g.kstar - 1 <= -2` -- but
`crossed_eq_of_Bincrease` says `p = BTrue (s3 g) >= -1` (`neg_one_le_BTrue`), a direct
contradiction. The `A`-decrease/`delta = true` case is the exact mirror. -/

theorem travel_crossed_eq_zero_of_Bincrease (g : EltBridge.Elt)
    (h2 : (occTrue (s3 g)).Nonempty) (hB : BTrue (s3 g) = BTrue g + 1) :
    SiteCost.travel g.kstar (if g.delta then g.kstar else g.kstar - 1) = 0 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hnm := crossed_not_mem_g_of_Bincrease g h2 hB
  by_contra ht
  apply hnm
  unfold occTrue
  by_cases hj : p ∈ g.supp
  · exact Finset.mem_filter.mpr ⟨hj, Or.inr ht⟩
  · exact absurd (g.hsupp p hj).2 ht

theorem not_Bincrease_of_delta_false (g : EltBridge.Elt) (h2 : (occTrue (s3 g)).Nonempty)
    (hB : BTrue (s3 g) = BTrue g + 1) (hd : g.delta = false) :
    False := by
  have hpeq := crossed_eq_of_Bincrease g h2 hB
  rw [if_neg (by rw [hd]; simp)] at hpeq
  have hkS : (s3 g).kstar = g.kstar - 1 := by
    have h1' : ¬ (g.delta = true) := by rw [hd]; simp
    rw [s3, dif_neg h1']
  have hwin := kstar_mem_corrected_window g
  simp only [Finset.mem_Icc] at hwin
  omega

theorem travel_crossed_eq_zero_of_Adecrease (g : EltBridge.Elt)
    (h2 : (occTrue (s3 g)).Nonempty) (hA : ATrue (s3 g) = ATrue g - 1) :
    SiteCost.travel g.kstar (if g.delta then g.kstar else g.kstar - 1) = 0 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hnm := crossed_not_mem_g_of_Adecrease g h2 hA
  by_contra ht
  apply hnm
  unfold occTrue
  by_cases hj : p ∈ g.supp
  · exact Finset.mem_filter.mpr ⟨hj, Or.inr ht⟩
  · exact absurd (g.hsupp p hj).2 ht

theorem not_Adecrease_of_delta_true (g : EltBridge.Elt) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g - 1) (hd : g.delta = true) :
    False := by
  have hpeq := crossed_eq_of_Adecrease g h2 hA
  rw [if_pos hd] at hpeq
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
  have hwin := kstar_mem_corrected_window g
  simp only [Finset.mem_Icc] at hwin
  omega


/-! ### The two remaining directions: `BTrue` decreases, `A` increases

Same technique as `Bincrease`/`Adecrease`, mirrored again: this time the crossed edge
`p` is being REMOVED from `occTrue g` (present before, gone after), so the
identification runs on `occTrue g`'s own max/min rather than `occTrue (s3 g)`'s, and
the resulting `d`-condition lands on the `s3`-UPDATED deposit being `0`, which
translates back (via `s3`'s `Function.update` formula) to `g`'s own deposit at the
crossed point being `g.eps`/`-g.eps` -- exactly the hypotheses
`not_cut_kstarSucc_of_delta_true`/`not_cut_kstarPred_of_delta_false` already need. -/

theorem crossed_eq_of_Bdecrease (g : EltBridge.Elt) (h1 : (occTrue g).Nonempty)
    (hB : BTrue (s3 g) = BTrue g - 1) :
    (if g.delta then g.kstar else g.kstar - 1) = BTrue g := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hunfold : BTrue g = max (-1) ((occTrue g).max' h1) := by unfold BTrue; rw [dif_pos h1]
  have hge2 : (-1 : ℤ) ≤ BTrue (s3 g) := neg_one_le_BTrue (s3 g)
  have hmax : BTrue g = (occTrue g).max' h1 := by omega
  have hmem : (occTrue g).max' h1 ∈ occTrue g := Finset.max'_mem _ h1
  by_cases heqp : (occTrue g).max' h1 = p
  · rw [← hmax] at heqp; exact heqp.symm
  · exfalso
    have hMg' : (occTrue g).max' h1 ∈ occTrue (s3 g) :=
      (occTrue_g_subset g _ hmem).resolve_left heqp
    have hle : (occTrue g).max' h1 ≤ BTrue (s3 g) := le_BTrue hMg'
    rw [← hmax] at hle
    omega

theorem crossed_not_mem_s3g_of_Bdecrease (g : EltBridge.Elt) (h1 : (occTrue g).Nonempty)
    (hB : BTrue (s3 g) = BTrue g - 1) :
    (if g.delta then g.kstar else g.kstar - 1) ∉ occTrue (s3 g) := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  intro hpg'
  have hunfold : BTrue g = max (-1) ((occTrue g).max' h1) := by unfold BTrue; rw [dif_pos h1]
  have hge2 : (-1 : ℤ) ≤ BTrue (s3 g) := neg_one_le_BTrue (s3 g)
  have hmax : BTrue g = (occTrue g).max' h1 := by omega
  have hpg : p ∈ occTrue g := by
    rw [hpdef, crossed_eq_of_Bdecrease g h1 hB, hmax]; exact Finset.max'_mem _ h1
  have heq : occTrue g = occTrue (s3 g) := by
    ext x
    by_cases hx : x = p
    · subst hx; exact ⟨fun _ => hpg', fun _ => hpg⟩
    · exact occTrue_agree_off_p g x hx
  have hBeq : BTrue g = BTrue (s3 g) := by unfold BTrue; rw [heq]
  omega

theorem d_new_crossed_eq_zero_of_Bdecrease (g : EltBridge.Elt) (h1 : (occTrue g).Nonempty)
    (hB : BTrue (s3 g) = BTrue g - 1) :
    (s3 g).d (if g.delta then g.kstar else g.kstar - 1) = 0 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hnm := crossed_not_mem_s3g_of_Bdecrease g h1 hB
  by_contra hd
  apply hnm
  unfold occTrue
  by_cases hj : p ∈ (s3 g).supp
  · exact Finset.mem_filter.mpr ⟨hj, Or.inl hd⟩
  · exact absurd ((s3 g).hsupp p hj).1 hd

theorem cTrue_s3_eq_of_Bdecrease_delta_false (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g - 1)
    (hd : g.delta = false) (hk1 : g.kstar ≠ 0) :
    cTrue (s3 g) = cTrue g := by
  have hkeq : g.kstar - 1 = BTrue g := by
    have hc := crossed_eq_of_Bdecrease g h1 hB
    rwa [if_neg (by rw [hd]; simp)] at hc
  have hdnew : (s3 g).d (g.kstar - 1) = 0 := by
    have := d_new_crossed_eq_zero_of_Bdecrease g h1 hB
    rwa [if_neg (by rw [hd]; simp)] at this
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
    rw [s3, dif_neg h1']
  have hdk : g.d (g.kstar - 1) = -g.eps := by
    have : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by
      rw [hupd]; simp
    rw [hdnew] at this
    omega
  have hnc : ¬ g.toPathData.cut (g.kstar - 1) := not_cut_kstarPred_of_delta_false g hd hdk
  have hnc2 : ¬ g.toPathData.cut (BTrue g) := hkeq ▸ hnc
  have hAB : ATrue g ≤ BTrue g - 1 := by
    obtain ⟨y, hy⟩ := h2
    have hy1 : ATrue (s3 g) ≤ y := ATrue_le hy
    have hy2 : y ≤ BTrue (s3 g) := le_BTrue hy
    omega
  have hfilter : ((Finset.Ioo (ATrue g) (BTrue g)).filter (s3 g).toPathData.cut).card
      = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
    have hins : Finset.Ioo (ATrue g) (BTrue g + 1)
        = insert (BTrue g) (Finset.Ioo (ATrue g) (BTrue g)) := by
      have hh := ioo_insert_right (A := ATrue g) (B := BTrue g - 1) (by omega)
      have heq1 : BTrue g - 1 + 2 = BTrue g + 1 := by ring
      have heq2 : BTrue g - 1 + 1 = BTrue g := by ring
      rw [heq1, heq2] at hh
      exact hh
    rw [hins, Finset.filter_insert, if_neg hnc2,
        Finset.filter_congr (fun x (_ : x ∈ Finset.Ioo (ATrue g) (BTrue g)) => cut_s3_eq g x)]
  have hshield1 : ¬ ShieldFires g := not_shieldFires_of_kstar_ne_zero g hk1
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hd2 : (s3 g).delta = true := by rw [s3, dif_neg h1']
  have hshield2 : ¬ ShieldFires (s3 g) := not_shieldFires_of_delta_true (s3 g) hd2
  have hnorm : BTrue g - 1 + 1 = BTrue g := by ring
  unfold cTrue
  rw [hA, hB, if_neg (fun h => hshield2 h.1), if_neg (fun h => hshield1 h.1), hnorm, hfilter]

theorem not_Bdecrease_of_delta_true (g : EltBridge.Elt) (h1 : (occTrue g).Nonempty)
    (hB : BTrue (s3 g) = BTrue g - 1) (hd : g.delta = true) :
    False := by
  have hpeq := crossed_eq_of_Bdecrease g h1 hB
  rw [if_pos hd] at hpeq
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
  have hwin := kstar_mem_corrected_window (s3 g)
  simp only [Finset.mem_Icc] at hwin
  omega

/-! ### The fourth and last direction: `ATrue` increases (`delta = true`)

Mirrors `Bdecrease` exactly (crossed edge removed, this time from the LEFT), using
`not_cut_kstarSucc_of_delta_true` and `card_filter_insert_left`. -/

theorem crossed_eq_of_Aincrease (g : EltBridge.Elt) (h1 : (occTrue g).Nonempty)
    (hA : ATrue (s3 g) = ATrue g + 1) :
    (if g.delta then g.kstar else g.kstar - 1) = ATrue g := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hunfold : ATrue g = min 0 ((occTrue g).min' h1) := by unfold ATrue; rw [dif_pos h1]
  have hle : ATrue (s3 g) ≤ 0 := atrue_le_zero (s3 g)
  have hmin : ATrue g = (occTrue g).min' h1 := by omega
  have hmem : (occTrue g).min' h1 ∈ occTrue g := Finset.min'_mem _ h1
  by_cases heqp : (occTrue g).min' h1 = p
  · rw [← hmin] at heqp; exact heqp.symm
  · exfalso
    have hMg' : (occTrue g).min' h1 ∈ occTrue (s3 g) :=
      (occTrue_g_subset g _ hmem).resolve_left heqp
    have hge2 : ATrue (s3 g) ≤ (occTrue g).min' h1 := ATrue_le hMg'
    rw [← hmin] at hge2
    omega

theorem crossed_not_mem_s3g_of_Aincrease (g : EltBridge.Elt) (h1 : (occTrue g).Nonempty)
    (hA : ATrue (s3 g) = ATrue g + 1) :
    (if g.delta then g.kstar else g.kstar - 1) ∉ occTrue (s3 g) := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  intro hpg'
  have hunfold : ATrue g = min 0 ((occTrue g).min' h1) := by unfold ATrue; rw [dif_pos h1]
  have hle : ATrue (s3 g) ≤ 0 := atrue_le_zero (s3 g)
  have hmin : ATrue g = (occTrue g).min' h1 := by omega
  have hpg : p ∈ occTrue g := by
    rw [hpdef, crossed_eq_of_Aincrease g h1 hA, hmin]; exact Finset.min'_mem _ h1
  have heq : occTrue g = occTrue (s3 g) := by
    ext x
    by_cases hx : x = p
    · subst hx; exact ⟨fun _ => hpg', fun _ => hpg⟩
    · exact occTrue_agree_off_p g x hx
  have hAeq : ATrue g = ATrue (s3 g) := by unfold ATrue; rw [heq]
  omega

theorem d_new_crossed_eq_zero_of_Aincrease (g : EltBridge.Elt) (h1 : (occTrue g).Nonempty)
    (hA : ATrue (s3 g) = ATrue g + 1) :
    (s3 g).d (if g.delta then g.kstar else g.kstar - 1) = 0 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hnm := crossed_not_mem_s3g_of_Aincrease g h1 hA
  by_contra hd
  apply hnm
  unfold occTrue
  by_cases hj : p ∈ (s3 g).supp
  · exact Finset.mem_filter.mpr ⟨hj, Or.inl hd⟩
  · exact absurd ((s3 g).hsupp p hj).1 hd

theorem cTrue_s3_eq_of_Aincrease_delta_true (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g + 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = true) (hk2 : (s3 g).kstar ≠ 0) :
    cTrue (s3 g) = cTrue g := by
  have hkeq : g.kstar = ATrue g := by
    have hc := crossed_eq_of_Aincrease g h1 hA
    rwa [if_pos hd] at hc
  have hdnew : (s3 g).d g.kstar = 0 := by
    have := d_new_crossed_eq_zero_of_Aincrease g h1 hA
    rwa [if_pos hd] at this
  have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
    rw [s3, dif_pos hd]
  have hdk : g.d g.kstar = g.eps := by
    have : (s3 g).d g.kstar = g.d g.kstar - g.eps := by rw [hupd]; simp
    rw [hdnew] at this
    omega
  have hk1' : g.kstar + 1 ≠ 0 := by
    have : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
    omega
  have hnc : ¬ g.toPathData.cut (g.kstar + 1) := not_cut_kstarSucc_of_delta_true g hd hk1' hdk
  have hnc2 : ¬ g.toPathData.cut (ATrue g + 1) := by rw [← hkeq]; exact hnc
  have hAB : ATrue g + 1 ≤ BTrue g := by
    obtain ⟨y, hy⟩ := h2
    have hy1 : ATrue (s3 g) ≤ y := ATrue_le hy
    have hy2 : y ≤ BTrue (s3 g) := le_BTrue hy
    omega
  have hfilter : ((Finset.Ioo (ATrue g + 1) (BTrue g + 1)).filter (s3 g).toPathData.cut).card
      = ((Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut).card := by
    rw [Finset.filter_congr (fun x (_ : x ∈ Finset.Ioo (ATrue g + 1) (BTrue g + 1)) => cut_s3_eq g x)]
    have hstep := card_filter_insert_left g.toPathData.cut
      (A := ATrue g + 1) (B := BTrue g) (by omega) hnc2
    have hnorm : ATrue g + 1 - 1 = ATrue g := by ring
    rw [hnorm] at hstep
    exact hstep.symm
  have hshield1 : ¬ ShieldFires g := not_shieldFires_of_delta_true g hd
  have hshield2 : ¬ ShieldFires (s3 g) := not_shieldFires_of_kstar_ne_zero (s3 g) hk2
  unfold cTrue
  rw [hA, hB, if_neg (fun h => hshield2 h.1), if_neg (fun h => hshield1 h.1)]
  omega

theorem not_Aincrease_of_delta_false (g : EltBridge.Elt) (h1 : (occTrue g).Nonempty)
    (hA : ATrue (s3 g) = ATrue g + 1) (hd : g.delta = false) :
    False := by
  have hpeq := crossed_eq_of_Aincrease g h1 hA
  rw [if_neg (by rw [hd]; simp)] at hpeq
  have hkS : (s3 g).kstar = g.kstar - 1 := by
    have h1' : ¬ (g.delta = true) := by rw [hd]; simp
    rw [s3, dif_neg h1']
  have hwin := kstar_mem_corrected_window (s3 g)
  simp only [Finset.mem_Icc] at hwin
  omega

/-! ### The `kstar = 0` special case: `ShieldFires g` holds UNCONDITIONALLY here

Key realization, found by hand before writing any Lean: in the `Adecrease`/`delta =
false` direction, the identification chain already gives `g.kstar = ATrue g`
(`crossed_eq_of_Adecrease`), so at `kstar = 0` we get `ATrue g = 0` for free -- no
separate hypothesis needed. And `ATrue g = 0` (with `kstar = 0`, forcing `travel` to
vanish everywhere, `SiteCost.travel_of_kstar_zero`) means EVERY occupied edge of `g`
sits at `>= 0` (else `occTrue g`'s minimum, and hence `ATrue g`, would be negative) --
which is exactly `ShieldFires`'s two `d`-clauses (`∀ j < 0, d j = 0` follows directly;
`∃ j >= 0, d j != 0` follows from `occTrue g` being nonempty combined with that same
bound). So `ShieldFires g` is not a separate case to split on: it is FORCED. With that,
`cTrue g` and `cTrue (s3 g)` turn out to have IDENTICAL formulas
(`(interior filter card) + [cut 0]`) after unfolding -- no case split on `cut 0`
either. This resolves the "does ShieldFires hold but cut 0 fail" worry from the task
plan: that combination is irrelevant because ShieldFires always holds and the `[cut 0]`
terms match exactly regardless of its truth value. -/

theorem shieldFires_of_kstar_zero_ATrue_zero (g : EltBridge.Elt) (hk0 : g.kstar = 0)
    (hd : g.delta = false) (hA0 : ATrue g = 0) (h1 : (occTrue g).Nonempty) :
    ShieldFires g := by
  have hnn : ∀ j : ℤ, j < 0 → g.d j = 0 := by
    intro j hj
    by_contra hdj
    have hmem : j ∈ occTrue g := by
      unfold occTrue
      by_cases hjs : j ∈ g.supp
      · exact Finset.mem_filter.mpr ⟨hjs, Or.inl hdj⟩
      · exact absurd (g.hsupp j hjs).1 hdj
    have hle : ATrue g ≤ j := ATrue_le hmem
    omega
  obtain ⟨x, hx⟩ := h1
  have hx0 : 0 ≤ x := by
    by_contra hneg
    push_neg at hneg
    unfold occTrue at hx
    rw [Finset.mem_filter] at hx
    rcases hx.2 with hd0 | ht0
    · exact hd0 (hnn x hneg)
    · apply ht0
      rw [hk0]; exact SiteCost.travel_of_kstar_zero x
  have hdx : g.d x ≠ 0 := by
    unfold occTrue at hx
    rw [Finset.mem_filter] at hx
    rcases hx.2 with hd0 | ht0
    · exact hd0
    · exfalso; apply ht0; rw [hk0]; exact SiteCost.travel_of_kstar_zero x
  exact ⟨hk0, hd, hnn, x, hx0, hdx⟩

theorem cTrue_s3_eq_of_Adecrease_delta_false_at_kstar_zero (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g - 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = false) (hk0 : g.kstar = 0) :
    cTrue (s3 g) = cTrue g := by
  have hkeq : g.kstar = ATrue g := by
    have hc := crossed_eq_of_Adecrease g h2 hA
    rw [if_neg (by rw [hd]; simp)] at hc
    omega
  have hA0 : ATrue g = 0 := by omega
  have hshield : ShieldFires g := shieldFires_of_kstar_zero_ATrue_zero g hk0 hd hA0 h1
  have hkS : (s3 g).kstar = g.kstar - 1 := by
    have h1' : ¬ (g.delta = true) := by rw [hd]; simp
    rw [s3, dif_neg h1']
  have hnshield2 : ¬ ShieldFires (s3 g) :=
    not_shieldFires_of_kstar_ne_zero (s3 g) (by omega)
  have hins : Finset.Ioo (ATrue g - 1) (BTrue g + 1)
      = insert (ATrue g) (Finset.Ioo (ATrue g) (BTrue g + 1)) := by
    have hh := ioo_insert_left (A := ATrue g) (B := BTrue g) (by
      obtain ⟨y, hy⟩ := h1
      have := ATrue_le hy
      have := le_BTrue hy
      omega)
    exact hh
  unfold cTrue
  rw [hA, hB, if_neg (fun h => hnshield2 h.1)]
  rw [Finset.filter_congr (fun x (_ : x ∈ Finset.Ioo (ATrue g - 1) (BTrue g + 1)) => cut_s3_eq g x)]
  rw [hins, Finset.filter_insert, hA0]
  by_cases hc0 : g.toPathData.cut 0
  · rw [if_pos hc0, if_pos ⟨hshield, hc0⟩]
    simp
  · rw [if_neg hc0, if_neg (fun h => hc0 h.2)]

/-! ### The mirror: `Aincrease`/`delta = true` at `(s3 g).kstar = 0` -- `ShieldFires (s3 g)` forced -/

theorem cTrue_s3_eq_of_Aincrease_delta_true_at_kstar_zero (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g + 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = true) (hk0 : (s3 g).kstar = 0) :
    cTrue (s3 g) = cTrue g := by
  classical
  have hkeq : g.kstar = ATrue g := by
    have hc := crossed_eq_of_Aincrease g h1 hA
    rwa [if_pos hd] at hc
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
  have hAeq0 : ATrue (s3 g) = 0 := by omega
  have hA0 : ATrue g + 1 = 0 := by omega
  have hd2 : (s3 g).delta = false := by rw [s3, dif_pos hd]
  have hshield2 : ShieldFires (s3 g) :=
    shieldFires_of_kstar_zero_ATrue_zero (s3 g) hk0 hd2 hAeq0 h2
  have hnshield1 : ¬ ShieldFires g := not_shieldFires_of_kstar_ne_zero g (by omega)
  have hins : Finset.Ioo (ATrue g) (BTrue g + 1)
      = insert (ATrue g + 1) (Finset.Ioo (ATrue g + 1) (BTrue g + 1)) := by
    have hh := ioo_insert_left (A := ATrue g + 1) (B := BTrue g) (by
      obtain ⟨y, hy⟩ := h2
      have := ATrue_le hy
      have := le_BTrue hy
      omega)
    have hA1 : ATrue g + 1 - 1 = ATrue g := by ring
    rwa [hA1] at hh
  unfold cTrue
  rw [hA, hB]
  have hz0 : (if ShieldFires g ∧ g.toPathData.cut 0 then (1:ℕ) else 0) = 0 :=
    if_neg (fun h => hnshield1 h.1)
  rw [hz0]
  rw [Finset.filter_congr (fun x (_ : x ∈ Finset.Ioo (ATrue g + 1) (BTrue g + 1)) => cut_s3_eq g x)]
  rw [hins, Finset.filter_insert, hA0]
  by_cases hc0 : g.toPathData.cut 0
  · have hc0' : (s3 g).toPathData.cut 0 := (cut_s3_eq g 0).mpr hc0
    have hz1 : (if ShieldFires (s3 g) ∧ (s3 g).toPathData.cut 0 then (1:ℕ) else 0) = 1 :=
      if_pos ⟨hshield2, hc0'⟩
    have hnotmem : (0:ℤ) ∉ (Finset.Ioo (0:ℤ) (BTrue g + 1)).filter g.toPathData.cut := by
      simp [Finset.mem_Ioo]
    rw [hz1, if_pos hc0, Finset.card_insert_of_notMem hnotmem]
  · have hc0' : ¬ (s3 g).toPathData.cut 0 := fun h => hc0 ((cut_s3_eq g 0).mp h)
    have hz2 : (if ShieldFires (s3 g) ∧ (s3 g).toPathData.cut 0 then (1:ℕ) else 0) = 0 :=
      if_neg (fun h => hc0' h.2)
    rw [hz2, if_neg hc0]

/-! ### Two more impossibilities: `Bincrease`/`delta=true` at `(s3 g).kstar = 0`, and
`Bdecrease`/`delta=false` at `g.kstar = 0`

Found while assembling the full `cTrue_s3_eq`: the `B`-side direction lemmas are
general in `kstar` on their OWN delta-matching side (already fixed to use
`not_shieldFires_of_delta_true` there), but the OTHER side's shield exclusion still
needs that side's `kstar != 0` -- and a numeric check found this really can fail, at
exactly the mirror site of the two `A`-side special cases. Both close the same way as
`not_Bdecrease_of_delta_true`/`not_Aincrease_of_delta_false`: `neg_one_le_BTrue`
applied to whichever side the `kstar = 0` forces to a too-negative `BTrue`. -/

theorem not_Bincrease_at_s3g_kstar_zero (g : EltBridge.Elt)
    (h2 : (occTrue (s3 g)).Nonempty) (hB : BTrue (s3 g) = BTrue g + 1)
    (hd : g.delta = true) (hk2 : (s3 g).kstar = 0) : False := by
  have hpeq := crossed_eq_of_Bincrease g h2 hB
  rw [if_pos hd] at hpeq
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
  have hge : (-1 : ℤ) ≤ BTrue g := neg_one_le_BTrue g
  omega

theorem not_Bdecrease_at_g_kstar_zero (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (hB : BTrue (s3 g) = BTrue g - 1)
    (hd : g.delta = false) (hk1 : g.kstar = 0) : False := by
  have hpeq := crossed_eq_of_Bdecrease g h1 hB
  rw [if_neg (by rw [hd]; simp)] at hpeq
  have hge : (-1 : ℤ) ≤ BTrue (s3 g) := neg_one_le_BTrue (s3 g)
  omega

/-! ### `cTrue_s3_eq`: the full, unconditional theorem

Assembles all cases: `occTrue g`/`occTrue (s3 g)` empty (via `cTrue_s3_eq_of_g_empty`/
`_of_s3g_empty`), both nonempty with the window unchanged
(`cTrue_s3_eq_of_window_unchanged`), both nonempty with `kstar != 0` on both sides
(`cTrue_s3_eq_of_kstar_ne_zero`), and both nonempty with `kstar = 0` on exactly one
side (the two `_at_kstar_zero` theorems, dispatched by `delta` -- at `kstar = 0`, only
one direction is geometrically possible for a given `delta`, matching the pattern
already confirmed for the generic case). -/

theorem cTrue_s3_eq (g : EltBridge.Elt) : cTrue (s3 g) = cTrue g := by
  by_cases h1 : (occTrue g).Nonempty
  · by_cases h2 : (occTrue (s3 g)).Nonempty
    · have hdispRaw := min_or_max_unchanged h1 h2 (occTrue_agree_off_p g)
      have hdisp : ATrue (s3 g) = ATrue g ∨ BTrue (s3 g) = BTrue g := by
        rcases hdispRaw with hmin | hmax
        · left; unfold ATrue; rw [dif_pos h1, dif_pos h2, hmin]
        · right; unfold BTrue; rw [dif_pos h1, dif_pos h2, hmax]
      by_cases hAeq : ATrue (s3 g) = ATrue g
      · by_cases hBeq : BTrue (s3 g) = BTrue g
        · exact cTrue_s3_eq_of_window_unchanged g hAeq hBeq
        · obtain ⟨hBd1, hBd2⟩ := BTrue_s3_dist_le_one g
          rcases (by omega : BTrue (s3 g) = BTrue g + 1 ∨ BTrue (s3 g) = BTrue g - 1)
            with hBp | hBm
          · -- BTrue increases: delta must be true (else impossible); the special
            -- site is (s3 g).kstar, so gate on THAT being zero or not.
            by_cases hd : g.delta = true
            · by_cases hk2 : (s3 g).kstar = 0
              · exact (not_Bincrease_at_s3g_kstar_zero g h2 hBp hd hk2).elim
              · exact cTrue_s3_eq_of_Bincrease_delta_true g h1 h2 hAeq hBp hd hk2
            · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
              exact (not_Bincrease_of_delta_false g h2 hBp hd').elim
          · -- BTrue decreases: delta must be false; the special site is g.kstar.
            by_cases hd : g.delta = false
            · by_cases hk1 : g.kstar = 0
              · exact (not_Bdecrease_at_g_kstar_zero g h1 hBm hd hk1).elim
              · exact cTrue_s3_eq_of_Bdecrease_delta_false g h1 h2 hAeq hBm hd hk1
            · have hd' : g.delta = true := by revert hd; cases g.delta <;> simp
              exact (not_Bdecrease_of_delta_true g h1 hBm hd').elim
      · have hBeq : BTrue (s3 g) = BTrue g := hdisp.resolve_left hAeq
        obtain ⟨hAd1, hAd2⟩ := ATrue_s3_dist_le_one g
        rcases (by omega : ATrue (s3 g) = ATrue g + 1 ∨ ATrue (s3 g) = ATrue g - 1)
          with hAp | hAm
        · -- ATrue increases: delta must be true; special site is (s3 g).kstar.
          by_cases hd : g.delta = true
          · by_cases hk2 : (s3 g).kstar = 0
            · exact cTrue_s3_eq_of_Aincrease_delta_true_at_kstar_zero g h1 h2 hAp hBeq hd hk2
            · exact cTrue_s3_eq_of_Aincrease_delta_true g h1 h2 hAp hBeq hd hk2
          · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
            exact (not_Aincrease_of_delta_false g h1 hAp hd').elim
        · -- ATrue decreases: delta must be false; special site is g.kstar.
          by_cases hd : g.delta = false
          · by_cases hk1 : g.kstar = 0
            · exact cTrue_s3_eq_of_Adecrease_delta_false_at_kstar_zero g h1 h2 hAm hBeq hd hk1
            · exact cTrue_s3_eq_of_Adecrease_delta_false g h1 h2 hAm hBeq hd hk1
          · have hd' : g.delta = true := by revert hd; cases g.delta <;> simp
            exact (not_Adecrease_of_delta_true g h2 hAm hd').elim
    · rw [Finset.not_nonempty_iff_eq_empty] at h2
      exact cTrue_s3_eq_of_s3g_empty g h2
  · rw [Finset.not_nonempty_iff_eq_empty] at h1
    exact cTrue_s3_eq_of_g_empty g h1

/-! ### Toward `lRTrue`'s `s3` movement: `d` vanishes strictly outside the corrected window

General fact, needed to bound the single new SITE term that enters `lRTrue`'s `siteCost`
sum when the window grows: if `occTrue g`'s witnesses are all `<= BTrue g` (true by
`BTrue`'s own definition, `max (-1) (occTrue g).max'`), then any edge strictly beyond
`BTrue g` is not in `occTrue g`, hence (via the standard membership characterisation)
has vanishing deposit. Mirrors for `ATrue` on the low side. -/

theorem d_eq_zero_of_gt_BTrue (g : EltBridge.Elt) {j : ℤ} (hj : BTrue g < j) :
    g.d j = 0 := by
  by_cases hj0 : (occTrue g).Nonempty
  · have hjmax : ¬ j ≤ (occTrue g).max' hj0 := by
      have : (occTrue g).max' hj0 ≤ BTrue g := by
        unfold BTrue; rw [dif_pos hj0]; exact le_max_right _ _
      omega
    have hjocc : j ∉ occTrue g := fun h => hjmax (Finset.le_max' _ j h)
    by_contra hd
    apply hjocc
    unfold occTrue
    by_cases hjs : j ∈ g.supp
    · exact Finset.mem_filter.mpr ⟨hjs, Or.inl hd⟩
    · exact absurd (g.hsupp j hjs).1 hd
  · rw [Finset.not_nonempty_iff_eq_empty] at hj0
    exact occTrue_g_empty_d_zero hj0 j

theorem d_eq_zero_of_lt_ATrue (g : EltBridge.Elt) {j : ℤ} (hj : j < ATrue g) :
    g.d j = 0 := by
  by_cases hj0 : (occTrue g).Nonempty
  · have hjmin : ¬ (occTrue g).min' hj0 ≤ j := by
      have : ATrue g ≤ (occTrue g).min' hj0 := by
        unfold ATrue; rw [dif_pos hj0]; exact min_le_right _ _
      omega
    have hjocc : j ∉ occTrue g := fun h => hjmin (Finset.min'_le _ j h)
    by_contra hd
    apply hjocc
    unfold occTrue
    by_cases hjs : j ∈ g.supp
    · exact Finset.mem_filter.mpr ⟨hjs, Or.inl hd⟩
    · exact absurd (g.hsupp j hjs).1 hd
  · rw [Finset.not_nonempty_iff_eq_empty] at hj0
    exact occTrue_g_empty_d_zero hj0 j

/-! ### `lRTrue`'s `s3` movement: the `Bincrease`/`delta = true` direction, exactly `+1`

Worked out by hand first (matching the numeric finding that `lRTrue` carries the whole
`PhiZ` jump exactly): the `mu`-sum gains the crossed edge `p = g.kstar` itself (mu's
window is `Icc(A,B)`, plain, unlike `cTrue`'s `Ioo`), with an EXACT value `1` there
(computed directly from `d`/`travel` at `p`, not merely bounded by `s3_mu_dist_le_two`);
the `siteCost`-sum gains site `p + 1`, whose cost is EXACTLY `0` (`alphaAt`/`betaAt`
both vanish there, using `d_eq_zero_of_gt_BTrue` for the `betaAt` half and the
`vArr`/`vL` structure plus `p + 1 != 0` -- forced since `BTrue g = p - 1 >= -1` gives
`p >= 0`, hence `p + 1 >= 1` -- for `alphaAt`). So `lRTrue (s3 g) = lRTrue g + 1`
exactly, not just `<= +1`. -/

theorem mu_s3g_at_crossed_eq_one_of_Bincrease (g : EltBridge.Elt)
    (h2 : (occTrue (s3 g)).Nonempty) (hB : BTrue (s3 g) = BTrue g + 1)
    (hd : g.delta = true) : (s3 g).toPathData.mu g.kstar = 1 := by
  have hdz : g.d g.kstar = 0 := by
    have := d_crossed_eq_zero_of_Bincrease g h2 hB; rwa [if_pos hd] at this
  have htz : SiteCost.travel g.kstar g.kstar = 0 := by
    have := travel_crossed_eq_zero_of_Bincrease g h2 hB; rwa [if_pos hd] at this
  have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
    rw [s3, dif_pos hd]
  have hdnew : (s3 g).d g.kstar = -g.eps := by
    rw [hupd, Function.update_self, hdz]; ring
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
  have htrnew : SiteCost.travel (s3 g).kstar g.kstar = 1 := by
    rw [hkS, EltBridge.Elt.travel_succ_at, htz]
    ring
  unfold SiteCost.PathData.mu
  simp only [EltBridge.Elt.toPathData]
  rw [hdnew, htrnew]
  have hcond : ¬ ((-g.eps : ℤ) = 0 ∧ (1:ℤ) = 0) := fun h => by norm_num at h
  rw [if_neg hcond]
  rcases g.heps with h | h <;> rw [h] <;> decide

theorem siteCost_new_eq_zero_of_Bincrease (g : EltBridge.Elt)
    (h2 : (occTrue (s3 g)).Nonempty) (hB : BTrue (s3 g) = BTrue g + 1)
    (hd : g.delta = true) : g.toPathData.siteCost (g.kstar + 1) = 0 := by
  have hdz : g.d g.kstar = 0 := by
    have := d_crossed_eq_zero_of_Bincrease g h2 hB; rwa [if_pos hd] at this
  have hge : (-1 : ℤ) ≤ BTrue g := neg_one_le_BTrue g
  have hkeq : g.kstar = BTrue g + 1 := by
    have hc := crossed_eq_of_Bincrease g h2 hB
    rw [if_pos hd] at hc
    omega
  have hp0 : (0:ℤ) ≤ g.kstar := by omega
  have hda : g.d (g.kstar + 1) = 0 := d_eq_zero_of_gt_BTrue g (by omega)
  have halpha : g.toPathData.alphaAt (g.kstar + 1) = 0 := by
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
    simp only [EltBridge.Elt.toPathData]
    have hnorm : g.kstar + 1 - 1 = g.kstar := by ring
    rw [hnorm, hdz]
    have hvArr : SiteCost.vArr (g.kstar + 1) = 0 := by unfold SiteCost.vArr; simp; omega
    rw [hvArr]
    have : g.toPathData.delta = true := hd
    simp [this]
  have hbeta : g.toPathData.betaAt (g.kstar + 1) = 0 := by
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
    simp only [EltBridge.Elt.toPathData]
    rw [hda]
    have hne : g.kstar + 1 ≠ g.kstar := by omega
    simp [hne]
  unfold SiteCost.PathData.siteCost
  rw [halpha, hbeta]
  rfl

theorem lRTrue_s3_eq_of_Bincrease_delta_true (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g + 1)
    (hd : g.delta = true) : lRTrue (s3 g) = lRTrue g + 1 := by
  have hmu1 := mu_s3g_at_crossed_eq_one_of_Bincrease g h2 hB hd
  have hsc0 := siteCost_new_eq_zero_of_Bincrease g h2 hB hd
  have hkeq : g.kstar = BTrue g + 1 := by
    have hc := crossed_eq_of_Bincrease g h2 hB
    rw [if_pos hd] at hc
    omega
  have hAB : ATrue g ≤ BTrue g := by
    obtain ⟨x, hx⟩ := h1
    exact le_trans (ATrue_le hx) (le_BTrue hx)
  have hmuins : Finset.Icc (ATrue g) (BTrue g + 1)
      = insert (BTrue g + 1) (Finset.Icc (ATrue g) (BTrue g)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hmucongr : (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (s3 g).toPathData.mu j)
      = (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j) :=
    Finset.sum_congr rfl (fun x hx => s3_mu_agree g x (by
      simp only [Finset.mem_Icc] at hx
      rw [if_pos hd]; omega))
  have hmusum : (∑ j ∈ Finset.Icc (ATrue g) (BTrue g + 1), (s3 g).toPathData.mu j)
      = (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j) + 1 := by
    rw [hmuins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
        hmucongr, ← hkeq, hmu1]
    omega
  have hsiteins : Finset.Icc (ATrue g) (BTrue g + 2)
      = insert (BTrue g + 2) (Finset.Icc (ATrue g) (BTrue g + 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hkeqB : g.kstar + 1 = BTrue g + 2 := by omega
  have hsitecongr : (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), (s3 g).toPathData.siteCost s)
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), g.toPathData.siteCost s) :=
    Finset.sum_congr rfl (fun x _ => EltBridge.Elt.s3_siteCost_eq g x)
  have hsitesum : (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 2), (s3 g).toPathData.siteCost s)
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), g.toPathData.siteCost s) := by
    rw [hsiteins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
        ← hkeqB]
    have hnew : (s3 g).toPathData.siteCost (g.kstar + 1) = 0 := by
      rw [EltBridge.Elt.s3_siteCost_eq]; exact hsc0
    rw [hnew, hsitecongr]
    omega
  unfold lRTrue
  rw [hA, hB]
  have hBB : BTrue g + 1 + 1 = BTrue g + 2 := by ring
  rw [hBB, hmusum, hsitesum]
  omega

/-! ### `lRTrue`'s `s3` movement: the `Bdecrease`/`delta = false` direction, exactly `-1`

Mirror of the `Bincrease` computation, removing rather than adding. The `mu`-sum loses
the crossed edge `p = g.kstar - 1` itself (`mu_g p = 1` exactly: `d_g p = -eps`,
magnitude `1`, forces `mu = max(1, travel) = 1` regardless of `travel`'s value there).
The `siteCost`-sum loses site `p + 1 = g.kstar`: `betaAt` vanishes there because
`g.kstar` itself sits STRICTLY BEYOND `BTrue g` (`BTrue g = p < p + 1 = g.kstar`), so
`d_eq_zero_of_gt_BTrue` applies directly; `alphaAt` vanishes given `g.kstar != 0`
(needed here for the same reason `cTrue`'s `Bdecrease` proof needed it -- unlike
`Bincrease`, this specific site's `alphaAt` DOES carry a `vArr` term). -/

theorem mu_g_at_crossed_eq_one_of_Bdecrease (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (hB : BTrue (s3 g) = BTrue g - 1)
    (hd : g.delta = false) : g.toPathData.mu (g.kstar - 1) = 1 := by
  have hdnew : (s3 g).d (g.kstar - 1) = 0 := by
    have := d_new_crossed_eq_zero_of_Bdecrease g h1 hB; rwa [if_neg (by rw [hd]; simp)] at this
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
    rw [s3, dif_neg h1']
  have hdz : g.d (g.kstar - 1) = -g.eps := by
    have : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by rw [hupd]; simp
    rw [hdnew] at this
    omega
  unfold SiteCost.PathData.mu
  simp only [EltBridge.Elt.toPathData]
  rw [hdz]
  have hne : ¬ ((-g.eps : ℤ) = 0 ∧ SiteCost.travel g.kstar (g.kstar - 1) = 0) := by
    rintro ⟨he, -⟩
    rcases g.heps with h | h <;> rw [h] at he <;> norm_num at he
  rw [if_neg hne]
  have htc := SiteCost.travel_cases g.kstar (g.kstar - 1)
  rcases g.heps with h | h <;> rw [h] <;> rcases htc with ht | ht | ht <;> rw [ht] <;> decide

theorem siteCost_removed_eq_zero_of_Bdecrease (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (hB : BTrue (s3 g) = BTrue g - 1)
    (hd : g.delta = false) (hk1 : g.kstar ≠ 0) : g.toPathData.siteCost g.kstar = 0 := by
  have hkeq : g.kstar - 1 = BTrue g := by
    have hc := crossed_eq_of_Bdecrease g h1 hB
    rwa [if_neg (by rw [hd]; simp)] at hc
  have hdz : g.d (g.kstar - 1) = -g.eps := by
    have hdnew : (s3 g).d (g.kstar - 1) = 0 := by
      have := d_new_crossed_eq_zero_of_Bdecrease g h1 hB; rwa [if_neg (by rw [hd]; simp)] at this
    have h1' : ¬ (g.delta = true) := by rw [hd]; simp
    have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
      rw [s3, dif_neg h1']
    have : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by rw [hupd]; simp
    rw [hdnew] at this
    omega
  have hdk0 : g.d g.kstar = 0 := d_eq_zero_of_gt_BTrue g (by omega)
  have halpha : g.toPathData.alphaAt g.kstar = 0 := by
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
    simp only [EltBridge.Elt.toPathData]
    have hnorm : g.kstar - 1 = g.kstar - 1 := rfl
    rw [hdz]
    have hvArr : SiteCost.vArr g.kstar = 0 := by unfold SiteCost.vArr; simp; exact hk1
    rw [hvArr, if_neg (by rw [hd]; simp)]
    simp
  have hbeta : g.toPathData.betaAt g.kstar = 0 := by
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
    simp only [EltBridge.Elt.toPathData]
    rw [hdk0, if_neg (by rw [hd]; simp)]
    simp
  unfold SiteCost.PathData.siteCost
  rw [halpha, hbeta]
  rfl

theorem lRTrue_s3_eq_of_Bdecrease_delta_false (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g - 1)
    (hd : g.delta = false) (hk1 : g.kstar ≠ 0) : lRTrue (s3 g) + 1 = lRTrue g := by
  have hmu1 := mu_g_at_crossed_eq_one_of_Bdecrease g h1 hB hd
  have hsc0 := siteCost_removed_eq_zero_of_Bdecrease g h1 hB hd hk1
  have hkeq : g.kstar - 1 = BTrue g := by
    have hc := crossed_eq_of_Bdecrease g h1 hB
    rwa [if_neg (by rw [hd]; simp)] at hc
  have hAB : ATrue g ≤ BTrue g - 1 := by
    obtain ⟨y, hy⟩ := h2
    have hy1 : ATrue (s3 g) ≤ y := ATrue_le hy
    have hy2 : y ≤ BTrue (s3 g) := le_BTrue hy
    omega
  have hmu1' : g.toPathData.mu (BTrue g) = 1 := by rw [← hkeq]; exact hmu1
  have hmuins : Finset.Icc (ATrue g) (BTrue g)
      = insert (BTrue g) (Finset.Icc (ATrue g) (BTrue g - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hmucongr : (∑ j ∈ Finset.Icc (ATrue g) (BTrue g - 1), g.toPathData.mu j)
      = (∑ j ∈ Finset.Icc (ATrue g) (BTrue g - 1), (s3 g).toPathData.mu j) :=
    Finset.sum_congr rfl (fun x hx => (s3_mu_agree g x (by
      simp only [Finset.mem_Icc] at hx
      rw [if_neg (by rw [hd]; simp)]; omega)).symm)
  have hmusum : (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j)
      = (∑ j ∈ Finset.Icc (ATrue g) (BTrue g - 1), (s3 g).toPathData.mu j) + 1 := by
    rw [hmuins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
        hmu1', hmucongr]
    omega
  have hsiteins : Finset.Icc (ATrue g) (BTrue g + 1)
      = insert (BTrue g + 1) (Finset.Icc (ATrue g) (BTrue g)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hkeqB : BTrue g + 1 = g.kstar := by omega
  have hsitecongr : (∑ s ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.siteCost s)
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g), (s3 g).toPathData.siteCost s) :=
    Finset.sum_congr rfl (fun x _ => (EltBridge.Elt.s3_siteCost_eq g x).symm)
  have hsitesum : (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), g.toPathData.siteCost s)
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g), (s3 g).toPathData.siteCost s) := by
    rw [hsiteins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
        hkeqB, hsc0, hsitecongr]
    omega
  unfold lRTrue
  rw [hA, hB]
  have hBB : BTrue g - 1 + 1 = BTrue g := by ring
  rw [hBB]
  omega

/-! ### `lRTrue`'s `s3` movement: the `Aincrease`/`delta = true` direction, exactly `-1`

Mirror of `Bdecrease`, on the left. Both `mu`'s and `siteCost`'s sums use `ATrue` as
their (bare) lower bound, so this direction loses the SAME index `p = g.kstar` from
BOTH sums -- unlike the `B`-side directions, which lose different-but-adjacent indices
from `mu` and `siteCost`. `mu_g(p) = 1` (forced by `d_g(p) = eps`, magnitude `1`,
regardless of `travel`). `siteCost_g(p) = 0` given `g.kstar != 0`: `betaAt(p) = 0`
directly from the removal condition `d_g(p) = eps` cancelling `eps * vR(p) = eps`;
`alphaAt(p) = -[p = 0]` (using `d_eq_zero_of_lt_ATrue` at `p - 1 < ATrue g = p`),
vanishing exactly when `p != 0`. -/

theorem mu_g_at_crossed_eq_one_of_Aincrease (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (hA : ATrue (s3 g) = ATrue g + 1)
    (hd : g.delta = true) : g.toPathData.mu g.kstar = 1 := by
  have hdnew : (s3 g).d g.kstar = 0 := by
    have := d_new_crossed_eq_zero_of_Aincrease g h1 hA; rwa [if_pos hd] at this
  have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
    rw [s3, dif_pos hd]
  have hdz : g.d g.kstar = g.eps := by
    have : (s3 g).d g.kstar = g.d g.kstar - g.eps := by rw [hupd]; simp
    rw [hdnew] at this
    omega
  unfold SiteCost.PathData.mu
  simp only [EltBridge.Elt.toPathData]
  rw [hdz]
  have hne : ¬ ((g.eps : ℤ) = 0 ∧ SiteCost.travel g.kstar g.kstar = 0) := by
    rintro ⟨he, -⟩
    rcases g.heps with h | h <;> rw [h] at he <;> norm_num at he
  rw [if_neg hne]
  have htc := SiteCost.travel_cases g.kstar g.kstar
  rcases g.heps with h | h <;> rw [h] <;> rcases htc with ht | ht | ht <;> rw [ht] <;> decide

theorem siteCost_removed_eq_zero_of_Aincrease (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (hA : ATrue (s3 g) = ATrue g + 1)
    (hd : g.delta = true) (hk1 : g.kstar ≠ 0) : g.toPathData.siteCost g.kstar = 0 := by
  have hkeq : g.kstar = ATrue g := by
    have hc := crossed_eq_of_Aincrease g h1 hA; rwa [if_pos hd] at hc
  have hdz : g.d g.kstar = g.eps := by
    have hdnew : (s3 g).d g.kstar = 0 := by
      have := d_new_crossed_eq_zero_of_Aincrease g h1 hA; rwa [if_pos hd] at this
    have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
      rw [s3, dif_pos hd]
    have : (s3 g).d g.kstar = g.d g.kstar - g.eps := by rw [hupd]; simp
    rw [hdnew] at this
    omega
  have hda : g.d (g.kstar - 1) = 0 := d_eq_zero_of_lt_ATrue g (by omega)
  have hbeta : g.toPathData.betaAt g.kstar = 0 := by
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
    simp only [EltBridge.Elt.toPathData]
    rw [hdz, if_pos hd]
    simp
  have halpha : g.toPathData.alphaAt g.kstar = 0 := by
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
    simp only [EltBridge.Elt.toPathData]
    rw [hda]
    have hvArr : SiteCost.vArr g.kstar = 0 := by unfold SiteCost.vArr; simp; exact hk1
    rw [hvArr, if_pos hd]
    simp
  unfold SiteCost.PathData.siteCost
  rw [halpha, hbeta]
  rfl

theorem lRTrue_s3_eq_of_Aincrease_delta_true (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g + 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = true) (hk1 : g.kstar ≠ 0) : lRTrue (s3 g) + 1 = lRTrue g := by
  have hmu1 := mu_g_at_crossed_eq_one_of_Aincrease g h1 hA hd
  have hsc0 := siteCost_removed_eq_zero_of_Aincrease g h1 hA hd hk1
  have hkeq : g.kstar = ATrue g := by
    have hc := crossed_eq_of_Aincrease g h1 hA; rwa [if_pos hd] at hc
  have hAB : ATrue g ≤ BTrue g - 1 := by
    obtain ⟨y, hy⟩ := h1
    have hy1 : ATrue g ≤ y := ATrue_le hy
    have hy2 : y ≤ BTrue g := le_BTrue hy
    have hAB0 : ATrue g ≤ BTrue g := le_trans hy1 hy2
    obtain ⟨z, hz⟩ := h2
    have hz1 : ATrue (s3 g) ≤ z := ATrue_le hz
    have hz2 : z ≤ BTrue (s3 g) := le_BTrue hz
    omega
  have hmu1' : g.toPathData.mu (ATrue g) = 1 := by rw [← hkeq]; exact hmu1
  have hsc0' : g.toPathData.siteCost (ATrue g) = 0 := by rw [← hkeq]; exact hsc0
  have hmuins : Finset.Icc (ATrue g) (BTrue g)
      = insert (ATrue g) (Finset.Icc (ATrue g + 1) (BTrue g)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hmucongr : (∑ j ∈ Finset.Icc (ATrue g + 1) (BTrue g), g.toPathData.mu j)
      = (∑ j ∈ Finset.Icc (ATrue g + 1) (BTrue g), (s3 g).toPathData.mu j) :=
    Finset.sum_congr rfl (fun x hx => (s3_mu_agree g x (by
      simp only [Finset.mem_Icc] at hx
      rw [if_pos hd]; omega)).symm)
  have hmusum : (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j)
      = (∑ j ∈ Finset.Icc (ATrue g + 1) (BTrue g), (s3 g).toPathData.mu j) + 1 := by
    rw [hmuins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
        hmu1', hmucongr]
    omega
  have hsiteins : Finset.Icc (ATrue g) (BTrue g + 1)
      = insert (ATrue g) (Finset.Icc (ATrue g + 1) (BTrue g + 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hsitecongr : (∑ s ∈ Finset.Icc (ATrue g + 1) (BTrue g + 1), g.toPathData.siteCost s)
      = (∑ s ∈ Finset.Icc (ATrue g + 1) (BTrue g + 1), (s3 g).toPathData.siteCost s) :=
    Finset.sum_congr rfl (fun x _ => (EltBridge.Elt.s3_siteCost_eq g x).symm)
  have hsitesum : (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), g.toPathData.siteCost s)
      = (∑ s ∈ Finset.Icc (ATrue g + 1) (BTrue g + 1), (s3 g).toPathData.siteCost s) := by
    rw [hsiteins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
        hsc0', hsitecongr]
    omega
  unfold lRTrue
  rw [hA, hB]
  omega

/-! ### `lRTrue`'s `s3` movement: the `Adecrease`/`delta = false` direction, exactly `+1`

Mirror of `Aincrease`, in the addition direction (mirrors `Bincrease` on the `A` side):
both sums gain the SAME index `p = (s3 g).kstar = g.kstar - 1`. `mu_{s3g}(p) = 1`
(`d_{s3g}(p) = eps`, magnitude `1`, forced regardless of `travel`). `siteCost_g(p) = 0`
given `(s3 g).kstar != 0`: `betaAt(p) = d_g(p) = 0` directly (the growth condition);
`alphaAt(p) = -[p = 0]` (`d_eq_zero_of_lt_ATrue` at `p - 1 < ATrue g`), vanishing
exactly when `p != 0`. -/

theorem mu_s3g_at_crossed_eq_one_of_Adecrease (g : EltBridge.Elt)
    (h2 : (occTrue (s3 g)).Nonempty) (hA : ATrue (s3 g) = ATrue g - 1)
    (hd : g.delta = false) : (s3 g).toPathData.mu (g.kstar - 1) = 1 := by
  have hdz : g.d (g.kstar - 1) = 0 := by
    have := d_crossed_eq_zero_of_Adecrease g h2 hA; rwa [if_neg (by rw [hd]; simp)] at this
  have htz : SiteCost.travel g.kstar (g.kstar - 1) = 0 := by
    have := travel_crossed_eq_zero_of_Adecrease g h2 hA; rwa [if_neg (by rw [hd]; simp)] at this
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
    rw [s3, dif_neg h1']
  have hdnew : (s3 g).d (g.kstar - 1) = g.eps := by
    rw [hupd, Function.update_self, hdz]; ring
  have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
  have htrnew : SiteCost.travel (s3 g).kstar (g.kstar - 1) = -1 := by
    rw [hkS]
    have := EltBridge.Elt.travel_pred_at g.kstar
    omega
  unfold SiteCost.PathData.mu
  simp only [EltBridge.Elt.toPathData]
  rw [hdnew, htrnew]
  have hcond : ¬ ((g.eps : ℤ) = 0 ∧ (-1:ℤ) = 0) := fun h => by norm_num at h
  rw [if_neg hcond]
  rcases g.heps with h | h <;> rw [h] <;> decide

theorem siteCost_new_eq_zero_of_Adecrease (g : EltBridge.Elt)
    (h2 : (occTrue (s3 g)).Nonempty) (hA : ATrue (s3 g) = ATrue g - 1)
    (hd : g.delta = false) (hk2 : (s3 g).kstar ≠ 0) :
    g.toPathData.siteCost (g.kstar - 1) = 0 := by
  have hdz : g.d (g.kstar - 1) = 0 := by
    have := d_crossed_eq_zero_of_Adecrease g h2 hA; rwa [if_neg (by rw [hd]; simp)] at this
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
  have hda : g.d (g.kstar - 2) = 0 := by
    have hlt : g.kstar - 2 < ATrue g := by
      have hc := crossed_eq_of_Adecrease g h2 hA
      rw [if_neg (by rw [hd]; simp)] at hc
      omega
    exact d_eq_zero_of_lt_ATrue g hlt
  have halpha : g.toPathData.alphaAt (g.kstar - 1) = 0 := by
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
    simp only [EltBridge.Elt.toPathData]
    have hnorm : g.kstar - 1 - 1 = g.kstar - 2 := by ring
    rw [hnorm, hda]
    have hvArr : SiteCost.vArr (g.kstar - 1) = 0 := by
      unfold SiteCost.vArr; simp
      intro hcontra
      apply hk2; rw [hkS]; omega
    rw [hvArr, if_neg (by rw [hd]; simp)]
    simp
  have hbeta : g.toPathData.betaAt (g.kstar - 1) = 0 := by
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
    simp only [EltBridge.Elt.toPathData]
    rw [hdz, if_neg (by rw [hd]; simp)]
    simp
  unfold SiteCost.PathData.siteCost
  rw [halpha, hbeta]
  rfl

theorem lRTrue_s3_eq_of_Adecrease_delta_false (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g - 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = false) (hk2 : (s3 g).kstar ≠ 0) :
    lRTrue (s3 g) = lRTrue g + 1 := by
  have hmu1 := mu_s3g_at_crossed_eq_one_of_Adecrease g h2 hA hd
  have hsc0 := siteCost_new_eq_zero_of_Adecrease g h2 hA hd hk2
  have hkeq : g.kstar - 1 = ATrue (s3 g) := by
    have hc := crossed_eq_of_Adecrease g h2 hA
    rwa [if_neg (by rw [hd]; simp)] at hc
  have hAB : ATrue (s3 g) ≤ BTrue g := by
    obtain ⟨z, hz⟩ := h2
    have hz1 : ATrue (s3 g) ≤ z := ATrue_le hz
    have hz2 : z ≤ BTrue (s3 g) := le_BTrue hz
    omega
  have hmuins : Finset.Icc (ATrue (s3 g)) (BTrue g)
      = insert (ATrue (s3 g)) (Finset.Icc (ATrue g) (BTrue g)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hmucongr : (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (s3 g).toPathData.mu j)
      = (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j) :=
    Finset.sum_congr rfl (fun x hx => s3_mu_agree g x (by
      simp only [Finset.mem_Icc] at hx
      rw [if_neg (by rw [hd]; simp)]; omega))
  have hmu1' : (s3 g).toPathData.mu (ATrue (s3 g)) = 1 := by rw [← hkeq]; exact hmu1
  have hmusum : (∑ j ∈ Finset.Icc (ATrue (s3 g)) (BTrue g), (s3 g).toPathData.mu j)
      = (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j) + 1 := by
    rw [hmuins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hmu1', hmucongr]
    omega
  have hsiteins : Finset.Icc (ATrue (s3 g)) (BTrue g + 1)
      = insert (ATrue (s3 g)) (Finset.Icc (ATrue g) (BTrue g + 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hsc0' : (s3 g).toPathData.siteCost (ATrue (s3 g)) = 0 := by
    rw [← hkeq, EltBridge.Elt.s3_siteCost_eq]; exact hsc0
  have hsitecongr : (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), (s3 g).toPathData.siteCost s)
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), g.toPathData.siteCost s) :=
    Finset.sum_congr rfl (fun x _ => EltBridge.Elt.s3_siteCost_eq g x)
  have hsitesum : (∑ s ∈ Finset.Icc (ATrue (s3 g)) (BTrue g + 1), (s3 g).toPathData.siteCost s)
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), g.toPathData.siteCost s) := by
    rw [hsiteins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hsc0', hsitecongr]
    omega
  unfold lRTrue
  rw [hB]
  omega

/-! ### `lRTrue`'s `s3` movement: the `occTrue g` empty case, exactly `+1`

`d` vanishes everywhere and `kstar = 0` here, so `vD s = [s = kstar]` is computed as a
plain numeral fact BEFORE it is combined with anything `delta`-dependent, avoiding the
dependent-`if`-rewrite pitfall (rewriting `kstar` directly inside a nested `if` whose
own `Decidable` instance depends on it breaks the motive check). `siteCost s = 0` for
every `s != 0`. Reuses the already-proved `mu` computations from the generic
`Bincrease`/`Adecrease` directions, whose hypotheses this empty-window transition
happens to satisfy exactly. -/

theorem vD_eq_zero_of_occTrue_empty (g : EltBridge.Elt) (he : occTrue g = ∅) {s : ℤ}
    (hs : s ≠ 0) : g.toPathData.vD s = 0 := by
  have hk0 := occTrue_g_empty_kstar_zero he
  unfold SiteCost.PathData.vD
  simp only [EltBridge.Elt.toPathData]
  split_ifs with h
  · omega
  · rfl

theorem siteCost_eq_zero_of_occTrue_empty_ne_zero (g : EltBridge.Elt)
    (he : occTrue g = ∅) {s : ℤ} (hs : s ≠ 0) : g.toPathData.siteCost s = 0 := by
  have hdz := occTrue_g_empty_d_zero he
  have hvD := vD_eq_zero_of_occTrue_empty g he hs
  have hvL : g.toPathData.vL s = 0 := by unfold SiteCost.PathData.vL; rw [hvD]; simp
  have hvR : g.toPathData.vR s = 0 := by unfold SiteCost.PathData.vR; rw [hvD]; simp
  have hdeq : g.toPathData.d = g.d := rfl
  have halpha : g.toPathData.alphaAt s = 0 := by
    unfold SiteCost.PathData.alphaAt
    rw [hdeq, hdz (s - 1), hvL]
    have hvArr : SiteCost.vArr s = 0 := by unfold SiteCost.vArr; simp; exact hs
    rw [hvArr]; simp
  have hbeta : g.toPathData.betaAt s = 0 := by
    unfold SiteCost.PathData.betaAt
    rw [hdeq, hdz s, hvR]; simp
  unfold SiteCost.PathData.siteCost
  rw [halpha, hbeta]
  rfl

theorem lRTrue_eq_siteCost_zero_of_occTrue_g_empty (g : EltBridge.Elt)
    (he : occTrue g = ∅) : lRTrue g = g.toPathData.siteCost 0 := by
  have hA : ATrue g = 0 := by
    unfold ATrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  have hB : BTrue g = -1 := by
    unfold BTrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  unfold lRTrue
  rw [hA, hB]
  have hmuempty : Finset.Icc (0:ℤ) (-1) = ∅ := by decide
  rw [hmuempty]
  norm_num

theorem lRTrue_s3_eq_of_occTrue_g_empty_delta_true (g : EltBridge.Elt)
    (he : occTrue g = ∅) (hd : g.delta = true) :
    lRTrue (s3 g) = lRTrue g + 1 := by
  have hk0 := occTrue_g_empty_kstar_zero he
  have hlr := lRTrue_eq_siteCost_zero_of_occTrue_g_empty g he
  have hAg : ATrue g = 0 := by
    unfold ATrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  have hBg : BTrue g = -1 := by
    unfold BTrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  have hsing := occTrue_s3_singleton_of_g_empty g he
  rw [if_pos hd, hk0] at hsing
  have hne : (occTrue (s3 g)).Nonempty := by rw [hsing]; exact Finset.singleton_nonempty _
  have hA : ATrue (s3 g) = 0 := by
    unfold ATrue; rw [dif_pos hne, minOccTrue_eq_of_singleton hsing hne]; norm_num
  have hB : BTrue (s3 g) = 0 := by
    unfold BTrue; rw [dif_pos hne, maxOccTrue_eq_of_singleton hsing hne]; norm_num
  have hBeq : BTrue (s3 g) = BTrue g + 1 := by rw [hB, hBg]; ring
  have hmu1 := mu_s3g_at_crossed_eq_one_of_Bincrease g hne hBeq hd
  rw [hk0] at hmu1
  have hsc1 : g.toPathData.siteCost 1 = 0 :=
    siteCost_eq_zero_of_occTrue_empty_ne_zero g he (by omega)
  have hsc1' : (s3 g).toPathData.siteCost 1 = 0 := by
    rw [EltBridge.Elt.s3_siteCost_eq]; exact hsc1
  have hsc0' : (s3 g).toPathData.siteCost 0 = g.toPathData.siteCost 0 :=
    EltBridge.Elt.s3_siteCost_eq g 0
  have step1 : lRTrue (s3 g)
      = (s3 g).toPathData.mu 0 + ((s3 g).toPathData.siteCost 0 + (s3 g).toPathData.siteCost 1) := by
    unfold lRTrue
    rw [hA, hB]
    have hmuone : Finset.Icc (0:ℤ) 0 = ({(0:ℤ)} : Finset ℤ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    have hsiteins : Finset.Icc (0:ℤ) (0 + 1) = insert (1:ℤ) (Finset.Icc (0:ℤ) 0) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hmuone, Finset.sum_singleton, hsiteins,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hmuone,
        Finset.sum_singleton]
    ring
  rw [step1, hmu1, hsc1', hsc0', hlr]
  ring

theorem lRTrue_s3_eq_of_occTrue_g_empty_delta_false (g : EltBridge.Elt)
    (he : occTrue g = ∅) (hd : g.delta = false) :
    lRTrue (s3 g) = lRTrue g + 1 := by
  have hk0 := occTrue_g_empty_kstar_zero he
  have hlr := lRTrue_eq_siteCost_zero_of_occTrue_g_empty g he
  have hAg : ATrue g = 0 := by
    unfold ATrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  have hBg : BTrue g = -1 := by
    unfold BTrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hsing := occTrue_s3_singleton_of_g_empty g he
  rw [if_neg h1', hk0] at hsing
  have hne : (occTrue (s3 g)).Nonempty := by rw [hsing]; exact Finset.singleton_nonempty _
  have hA : ATrue (s3 g) = -1 := by
    unfold ATrue; rw [dif_pos hne, minOccTrue_eq_of_singleton hsing hne]; norm_num
  have hB : BTrue (s3 g) = -1 := by
    unfold BTrue; rw [dif_pos hne, maxOccTrue_eq_of_singleton hsing hne]; norm_num
  have hAeq : ATrue (s3 g) = ATrue g - 1 := by rw [hA, hAg]; ring
  have hmu1 := mu_s3g_at_crossed_eq_one_of_Adecrease g hne hAeq hd
  have hkeqm1 : g.kstar - 1 = -1 := by omega
  rw [hkeqm1] at hmu1
  have hsc1 : g.toPathData.siteCost (-1) = 0 :=
    siteCost_eq_zero_of_occTrue_empty_ne_zero g he (by omega)
  have hsc1' : (s3 g).toPathData.siteCost (-1) = 0 := by
    rw [EltBridge.Elt.s3_siteCost_eq]; exact hsc1
  have hsc0' : (s3 g).toPathData.siteCost 0 = g.toPathData.siteCost 0 :=
    EltBridge.Elt.s3_siteCost_eq g 0
  have step1 : lRTrue (s3 g)
      = (s3 g).toPathData.mu (-1) + ((s3 g).toPathData.siteCost (-1) + (s3 g).toPathData.siteCost 0) := by
    unfold lRTrue
    rw [hA, hB]
    have hmuone : Finset.Icc (-1:ℤ) (-1) = ({(-1:ℤ)} : Finset ℤ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    have hsiteins : Finset.Icc (-1:ℤ) (-1 + 1) = insert (-1:ℤ) (Finset.Icc (0:ℤ) (-1 + 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsiteone : Finset.Icc (0:ℤ) (-1 + 1) = ({(0:ℤ)} : Finset ℤ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [hmuone, Finset.sum_singleton, hsiteins,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hsiteone,
        Finset.sum_singleton]
  rw [step1, hmu1, hsc1', hsc0', hlr]
  omega

theorem lRTrue_s3_eq_of_occTrue_g_empty (g : EltBridge.Elt) (he : occTrue g = ∅) :
    lRTrue (s3 g) = lRTrue g + 1 := by
  by_cases hd : g.delta = true
  · exact lRTrue_s3_eq_of_occTrue_g_empty_delta_true g he hd
  · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
    exact lRTrue_s3_eq_of_occTrue_g_empty_delta_false g he hd'

/-! ### `lRTrue`'s `s3` movement: the `occTrue (s3 g)` empty case, exactly `-1`

Mirror of the `occTrue g` empty case, in the removal direction: `lRTrue_eq_siteCost_
zero_of_occTrue_g_empty` and `siteCost_eq_zero_of_occTrue_empty_ne_zero` are already
generic in their `Elt` argument, so applying them to `s3 g` (rather than `g`) reuses
them directly for the now-empty side. The occupied side (`g`, singleton `{p}`) is
exactly an `Aincrease` (`delta = true`) or `Bdecrease` (`delta = false`) REMOVAL
transition, so `mu_g_at_crossed_eq_one_of_Aincrease`/`_of_Bdecrease` and
`siteCost_removed_eq_zero_of_Aincrease`/`_of_Bdecrease` (already proved for the
generic directions) apply directly too, with `g.kstar` playing the role of the
crossed site (confirmed `!= 0` since `g.kstar` equals `-1` or `1` at this transition,
never `0`, matching the earlier `Bdecrease`/`Aincrease` "never at kstar=0" findings). -/

theorem lRTrue_s3_eq_of_occTrue_s3g_empty_delta_true (g : EltBridge.Elt)
    (he : occTrue (s3 g) = ∅) (hd : g.delta = true) :
    lRTrue (s3 g) = lRTrue g - 1 := by
  have hk0 := occTrue_g_empty_kstar_zero he
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
  have hkm1 : g.kstar = -1 := by omega
  have hlrS := lRTrue_eq_siteCost_zero_of_occTrue_g_empty (s3 g) he
  have hsc0eq : (s3 g).toPathData.siteCost 0 = g.toPathData.siteCost 0 :=
    EltBridge.Elt.s3_siteCost_eq g 0
  have hsing := occTrue_g_singleton_of_s3_empty g he
  rw [if_pos hd] at hsing
  have hne : (occTrue g).Nonempty := by rw [hsing]; exact Finset.singleton_nonempty _
  have hA : ATrue g = -1 := by
    unfold ATrue; rw [dif_pos hne, minOccTrue_eq_of_singleton hsing hne, hkm1]; omega
  have hB : BTrue g = -1 := by
    unfold BTrue; rw [dif_pos hne, maxOccTrue_eq_of_singleton hsing hne, hkm1]; omega
  have hAs3 : ATrue (s3 g) = 0 := by
    unfold ATrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  have hAeq : ATrue (s3 g) = ATrue g + 1 := by rw [hA, hAs3]; omega
  have hmu1 := mu_g_at_crossed_eq_one_of_Aincrease g hne hAeq hd
  rw [hkm1] at hmu1
  have hsc0 : g.toPathData.siteCost g.kstar = 0 :=
    siteCost_removed_eq_zero_of_Aincrease g hne hAeq hd (by omega)
  rw [hkm1] at hsc0
  have step1 : lRTrue g = g.toPathData.mu (-1) + (g.toPathData.siteCost (-1) + g.toPathData.siteCost 0) := by
    unfold lRTrue
    rw [hA, hB]
    have hmuone : Finset.Icc (-1:ℤ) (-1) = ({(-1:ℤ)} : Finset ℤ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    have hsiteins : Finset.Icc (-1:ℤ) (-1 + 1) = insert (-1:ℤ) (Finset.Icc (0:ℤ) (-1 + 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsiteone : Finset.Icc (0:ℤ) (-1 + 1) = ({(0:ℤ)} : Finset ℤ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [hmuone, Finset.sum_singleton, hsiteins,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hsiteone,
        Finset.sum_singleton]
  rw [step1, hmu1, hsc0, hlrS, hsc0eq]
  omega

theorem lRTrue_s3_eq_of_occTrue_s3g_empty_delta_false (g : EltBridge.Elt)
    (he : occTrue (s3 g) = ∅) (hd : g.delta = false) :
    lRTrue (s3 g) = lRTrue g - 1 := by
  have hk0 := occTrue_g_empty_kstar_zero he
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
  have hk1 : g.kstar = 1 := by omega
  have hlrS := lRTrue_eq_siteCost_zero_of_occTrue_g_empty (s3 g) he
  have hsc0eq : (s3 g).toPathData.siteCost 0 = g.toPathData.siteCost 0 :=
    EltBridge.Elt.s3_siteCost_eq g 0
  have hsing := occTrue_g_singleton_of_s3_empty g he
  rw [if_neg h1'] at hsing
  have hne : (occTrue g).Nonempty := by rw [hsing]; exact Finset.singleton_nonempty _
  have hA : ATrue g = 0 := by
    unfold ATrue; rw [dif_pos hne, minOccTrue_eq_of_singleton hsing hne, hk1]; omega
  have hB : BTrue g = 0 := by
    unfold BTrue; rw [dif_pos hne, maxOccTrue_eq_of_singleton hsing hne, hk1]; omega
  have hBs3 : BTrue (s3 g) = -1 := by
    unfold BTrue; rw [dif_neg (by rw [he]; exact Finset.not_nonempty_empty)]
  have hBeq : BTrue (s3 g) = BTrue g - 1 := by rw [hB, hBs3]; omega
  have hmu1 := mu_g_at_crossed_eq_one_of_Bdecrease g hne hBeq hd
  have hkm1 : g.kstar - 1 = 0 := by omega
  rw [hkm1] at hmu1
  have hsc0 : g.toPathData.siteCost g.kstar = 0 :=
    siteCost_removed_eq_zero_of_Bdecrease g hne hBeq hd (by omega)
  rw [hk1] at hsc0
  have step1 : lRTrue g = g.toPathData.mu 0 + (g.toPathData.siteCost 0 + g.toPathData.siteCost 1) := by
    unfold lRTrue
    rw [hA, hB]
    have hmuone : Finset.Icc (0:ℤ) 0 = ({(0:ℤ)} : Finset ℤ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    have hsiteins : Finset.Icc (0:ℤ) (0 + 1) = insert (1:ℤ) (Finset.Icc (0:ℤ) 0) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hmuone, Finset.sum_singleton, hsiteins,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hmuone,
        Finset.sum_singleton]
    ring
  rw [step1, hmu1, hsc0, hlrS, hsc0eq]
  omega

theorem lRTrue_s3_eq_of_occTrue_s3g_empty (g : EltBridge.Elt) (he : occTrue (s3 g) = ∅) :
    lRTrue (s3 g) = lRTrue g - 1 := by
  by_cases hd : g.delta = true
  · exact lRTrue_s3_eq_of_occTrue_s3g_empty_delta_true g he hd
  · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
    exact lRTrue_s3_eq_of_occTrue_s3g_empty_delta_false g he hd'


theorem mu_dist_one_of_occupied_true (g : EltBridge.Elt) (hd : g.delta = true)
    (hd0 : g.d g.kstar ≠ 0) :
    ((s3 g).toPathData.mu g.kstar : ℤ) = g.toPathData.mu g.kstar + 1 ∨
      (g.toPathData.mu g.kstar : ℤ) = (s3 g).toPathData.mu g.kstar + 1 := by
  have hpar := g.hpar g.kstar
  have htc := SiteCost.travel_cases g.kstar g.kstar
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
  have hd1 : (s3 g).d g.kstar = g.d g.kstar - g.eps := by
    have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
      rw [s3, dif_pos hd]
    rw [hupd]; simp
  have ht1 : SiteCost.travel (s3 g).kstar g.kstar = SiteCost.travel g.kstar g.kstar + 1 := by
    rw [hkS, EltBridge.Elt.travel_succ_at]
  have heps := g.heps
  unfold SiteCost.PathData.mu
  simp only [EltBridge.Elt.toPathData]
  split_ifs with hvac1 hvac2 hvac2 <;>
    rcases htc with ht | ht | ht <;> rcases heps with he | he <;> omega

theorem mu_dist_one_of_occupied_false (g : EltBridge.Elt) (hd : g.delta = false)
    (hd0 : g.d (g.kstar - 1) ≠ 0) :
    ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1 ∨
      (g.toPathData.mu (g.kstar - 1) : ℤ) = (s3 g).toPathData.mu (g.kstar - 1) + 1 := by
  have hpar := g.hpar (g.kstar - 1)
  have htc := SiteCost.travel_cases g.kstar (g.kstar - 1)
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
  have hd1 : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by
    have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
      rw [s3, dif_neg h1']
    rw [hupd]; simp
  have ht1 : SiteCost.travel (s3 g).kstar (g.kstar - 1) = SiteCost.travel g.kstar (g.kstar - 1) - 1 := by
    rw [hkS, EltBridge.Elt.travel_pred_at]
  have heps := g.heps
  unfold SiteCost.PathData.mu
  simp only [EltBridge.Elt.toPathData]
  split_ifs with hvac1 hvac2 hvac2 <;>
    rcases htc with ht | ht | ht <;> rcases heps with he | he <;> omega

theorem mu_dist_one_of_occupied (g : EltBridge.Elt)
    (hd0 : g.d (if g.delta then g.kstar else g.kstar - 1) ≠ 0) :
    ((s3 g).toPathData.mu (if g.delta then g.kstar else g.kstar - 1) : ℤ)
        = g.toPathData.mu (if g.delta then g.kstar else g.kstar - 1) + 1 ∨
      (g.toPathData.mu (if g.delta then g.kstar else g.kstar - 1) : ℤ)
        = (s3 g).toPathData.mu (if g.delta then g.kstar else g.kstar - 1) + 1 := by
  by_cases hd : g.delta = true
  · rw [if_pos hd] at hd0 ⊢
    exact mu_dist_one_of_occupied_true g hd hd0
  · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
    rw [if_neg hd] at hd0 ⊢
    exact mu_dist_one_of_occupied_false g hd' hd0

/-! ### `mu`'s exact `+-1` shift, fully unconditionally (the vacuum case too)

A numeric check found `mu_dist_one_of_occupied`'s hypothesis (`d != 0` at the crossed
edge) genuinely fails in `181072` of the `1790039` window-unchanged transitions --
the crossed edge can be a true VACUUM (`d = 0`, and by `hpar`'s parity constraint this
forces `travel = 0` too, since `travel in {-1,0,1}` and only `0` is even) before the
step. In that case `mu_g(p) = 2` (the vacuum clause) UNCONDITIONALLY, and after the
step `d` becomes `+-eps` (magnitude `1`) while `travel` becomes `+-1` (magnitude `1`,
`travel_succ_at`/`travel_pred_at` applied to `travel_g = 0`), so `mu_{s3g}(p) =
max(1,1) = 1` -- ALWAYS exactly `2 -> 1`, no `eps`/`delta` case split even needed.
Combined with `mu_dist_one_of_occupied`, `mu` moves by exactly `+-1` under `s3` at
EVERY crossed edge, unconditionally -- no hypothesis on `d` at all. -/

theorem mu_dist_one_unconditional (g : EltBridge.Elt) :
    ((s3 g).toPathData.mu (if g.delta then g.kstar else g.kstar - 1) : ℤ)
        = g.toPathData.mu (if g.delta then g.kstar else g.kstar - 1) + 1 ∨
      (g.toPathData.mu (if g.delta then g.kstar else g.kstar - 1) : ℤ)
        = (s3 g).toPathData.mu (if g.delta then g.kstar else g.kstar - 1) + 1 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  by_cases hd0 : g.d p ≠ 0
  · rw [hpdef]
    exact mu_dist_one_of_occupied g hd0
  · push_neg at hd0
    by_cases hd : g.delta = true
    · have hpv : p = g.kstar := by rw [hpdef, if_pos hd]
      rw [hpv] at hd0
      have hpar := g.hpar g.kstar
      have htc0 := SiteCost.travel_cases g.kstar g.kstar
      have htz : SiteCost.travel g.kstar g.kstar = 0 := by omega
      have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
      have hd1 : (s3 g).d g.kstar = g.d g.kstar - g.eps := by
        have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
          rw [s3, dif_pos hd]
        rw [hupd]; simp
      have ht1 : SiteCost.travel (s3 g).kstar g.kstar = SiteCost.travel g.kstar g.kstar + 1 := by
        rw [hkS, EltBridge.Elt.travel_succ_at]
      have heps := g.heps
      rw [hpdef, if_pos hd]
      unfold SiteCost.PathData.mu
      simp only [EltBridge.Elt.toPathData]
      split_ifs with hvac1 hvac2 hvac2 <;> rcases heps with he | he <;> omega
    · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
      have hpv : p = g.kstar - 1 := by rw [hpdef, if_neg hd]
      rw [hpv] at hd0
      have hpar := g.hpar (g.kstar - 1)
      have htc0 := SiteCost.travel_cases g.kstar (g.kstar - 1)
      have htz : SiteCost.travel g.kstar (g.kstar - 1) = 0 := by omega
      have h1' : ¬ (g.delta = true) := by rw [hd']; simp
      have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
      have hd1 : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by
        have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
          rw [s3, dif_neg h1']
        rw [hupd]; simp
      have ht1 : SiteCost.travel (s3 g).kstar (g.kstar - 1) = SiteCost.travel g.kstar (g.kstar - 1) - 1 := by
        rw [hkS, EltBridge.Elt.travel_pred_at]
      have heps := g.heps
      rw [hpdef, if_neg hd]
      unfold SiteCost.PathData.mu
      simp only [EltBridge.Elt.toPathData]
      split_ifs with hvac1 hvac2 hvac2 <;> rcases heps with he | he <;> omega

/-! ### `lRTrue`'s `s3` movement: the window-unchanged case, assembled

The crossed edge `p` lies in the (closed) `mu`-window `[ATrue g, BTrue g]` whenever the
window is unchanged: `kstar_mem_corrected_window` applied to BOTH `g` and `s3 g`,
combined with `hA`/`hB`, pins `p` on both sides at once (the `+1` slack in each
individual bound cancels against the OTHER side's bound). With `p` inside the window,
`sum_eq_add_diff_of_eq_off` (using `s3_mu_agree` elsewhere) reduces the `mu`-sum's
difference to exactly the `p`-term difference, closed by the now-unconditional
`mu_dist_one_unconditional`. `siteCost` needs no argument at all here (`s3_siteCost_eq`
is unconditional, and the window is unchanged so it's the same sum). -/

theorem crossed_mem_mu_window_of_window_unchanged (g : EltBridge.Elt)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g) :
    (if g.delta then g.kstar else g.kstar - 1) ∈
      Finset.Icc (ATrue g) (BTrue g) := by
  have hwg := kstar_mem_corrected_window g
  have hws := kstar_mem_corrected_window (s3 g)
  simp only [Finset.mem_Icc] at hwg hws
  by_cases hd : g.delta = true
  · have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
    rw [if_pos hd]
    simp only [Finset.mem_Icc]
    omega
  · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
    have h1' : ¬ (g.delta = true) := by rw [hd']; simp
    have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
    rw [if_neg hd]
    simp only [Finset.mem_Icc]
    omega

theorem lRTrue_s3_dist_one_of_window_unchanged (g : EltBridge.Elt)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g) :
    (lRTrue (s3 g) : ℤ) = lRTrue g + 1 ∨ (lRTrue g : ℤ) = lRTrue (s3 g) + 1 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hpmem := crossed_mem_mu_window_of_window_unchanged g hA hB
  rw [← hpdef] at hpmem
  have hmusum : (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), ((s3 g).toPathData.mu j : ℤ))
      = (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ))
          + (((s3 g).toPathData.mu p : ℤ) - (g.toPathData.mu p : ℤ)) :=
    sum_eq_add_diff_of_eq_off hpmem (fun x _ hx => by
      have hx' : x ≠ (if g.delta then g.kstar else g.kstar - 1) := by rwa [hpdef] at hx
      have := s3_mu_agree g x hx'
      exact_mod_cast this)
  have hsitesum : (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), ((s3 g).toPathData.siteCost s : ℤ))
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), (g.toPathData.siteCost s : ℤ)) :=
    Finset.sum_congr rfl (fun x _ => by exact_mod_cast EltBridge.Elt.s3_siteCost_eq g x)
  have hlr : (lRTrue (s3 g) : ℤ) = (lRTrue g : ℤ)
      + (((s3 g).toPathData.mu p : ℤ) - (g.toPathData.mu p : ℤ)) := by
    unfold lRTrue
    rw [hA, hB]
    push_cast
    rw [hmusum, hsitesum]
    ring
  rcases mu_dist_one_unconditional g with h | h
  · rw [← hpdef] at h; left; rw [hlr, h]; ring
  · rw [← hpdef] at h; right; rw [hlr] at *; omega


theorem not_Aincrease_at_g_kstar_zero (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (hA : ATrue (s3 g) = ATrue g + 1)
    (hd : g.delta = true) (hk0 : g.kstar = 0) : False := by
  have hc := crossed_eq_of_Aincrease g h1 hA
  rw [if_pos hd] at hc
  have hkeq : g.kstar = ATrue g := hc
  have hdnew : (s3 g).d g.kstar = 0 := by
    have := d_new_crossed_eq_zero_of_Aincrease g h1 hA
    rwa [if_pos hd] at this
  have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
    rw [s3, dif_pos hd]
  have hdk : g.d g.kstar = g.eps := by
    have : (s3 g).d g.kstar = g.d g.kstar - g.eps := by rw [hupd]; simp
    rw [hdnew] at this; omega
  have hpar := g.hpar g.kstar
  have htz : SiteCost.travel g.kstar g.kstar = 0 := by
    rw [hk0]; exact SiteCost.travel_of_kstar_zero 0
  have heps := g.heps
  rw [hdk, htz] at hpar
  rcases heps with he | he <;> omega

theorem not_Adecrease_at_s3g_kstar_zero (g : EltBridge.Elt)
    (h2 : (occTrue (s3 g)).Nonempty) (hA : ATrue (s3 g) = ATrue g - 1)
    (hd : g.delta = false) (hk0 : (s3 g).kstar = 0) : False := by
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hc := crossed_eq_of_Adecrease g h2 hA
  rw [if_neg h1'] at hc
  have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
  have hdz : g.d (g.kstar - 1) = 0 := by
    have := d_crossed_eq_zero_of_Adecrease g h2 hA
    rwa [if_neg h1'] at this
  have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
    rw [s3, dif_neg h1']
  have hdk : (s3 g).d (g.kstar - 1) = g.eps := by
    have : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by rw [hupd]; simp
    rw [hdz] at this; omega
  have hdk' : (s3 g).d (s3 g).kstar = g.eps := by rw [hkS]; exact hdk
  have hpar := (s3 g).hpar (s3 g).kstar
  have htz : SiteCost.travel (s3 g).kstar (s3 g).kstar = 0 := by
    rw [hk0]; exact SiteCost.travel_of_kstar_zero 0
  have heps := g.heps
  rw [hdk', htz] at hpar
  rcases heps with he | he <;> omega

theorem lRTrue_s3_eq_of_Aincrease_delta_true' (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g + 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = true) : lRTrue (s3 g) + 1 = lRTrue g :=
  lRTrue_s3_eq_of_Aincrease_delta_true g h1 h2 hA hB hd
    (fun hk0 => not_Aincrease_at_g_kstar_zero g h1 hA hd hk0)

theorem lRTrue_s3_eq_of_Adecrease_delta_false' (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g - 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = false) : lRTrue (s3 g) = lRTrue g + 1 :=
  lRTrue_s3_eq_of_Adecrease_delta_false g h1 h2 hA hB hd
    (fun hk0 => not_Adecrease_at_s3g_kstar_zero g h2 hA hd hk0)


theorem lRTrue_s3_eq_of_Bdecrease_delta_false' (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g - 1)
    (hd : g.delta = false) : lRTrue (s3 g) + 1 = lRTrue g :=
  lRTrue_s3_eq_of_Bdecrease_delta_false g h1 h2 hA hB hd
    (fun hk1 => not_Bdecrease_at_g_kstar_zero g h1 hB hd hk1)


theorem lRTrue_s3_dist_one (g : EltBridge.Elt) :
    (lRTrue (s3 g) : ℤ) = lRTrue g + 1 ∨ (lRTrue g : ℤ) = lRTrue (s3 g) + 1 := by
  by_cases h1 : (occTrue g).Nonempty
  · by_cases h2 : (occTrue (s3 g)).Nonempty
    · have hdispRaw := min_or_max_unchanged h1 h2 (occTrue_agree_off_p g)
      have hdisp : ATrue (s3 g) = ATrue g ∨ BTrue (s3 g) = BTrue g := by
        rcases hdispRaw with hmin | hmax
        · left; unfold ATrue; rw [dif_pos h1, dif_pos h2, hmin]
        · right; unfold BTrue; rw [dif_pos h1, dif_pos h2, hmax]
      by_cases hAeq : ATrue (s3 g) = ATrue g
      · by_cases hBeq : BTrue (s3 g) = BTrue g
        · exact lRTrue_s3_dist_one_of_window_unchanged g hAeq hBeq
        · obtain ⟨hBd1, hBd2⟩ := BTrue_s3_dist_le_one g
          rcases (by omega : BTrue (s3 g) = BTrue g + 1 ∨ BTrue (s3 g) = BTrue g - 1)
            with hBp | hBm
          · by_cases hd : g.delta = true
            · have := lRTrue_s3_eq_of_Bincrease_delta_true g h1 h2 hAeq hBp hd
              left; exact_mod_cast this
            · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
              exact (not_Bincrease_of_delta_false g h2 hBp hd').elim
          · by_cases hd : g.delta = false
            · have := lRTrue_s3_eq_of_Bdecrease_delta_false' g h1 h2 hAeq hBm hd
              right; exact_mod_cast this.symm
            · have hd' : g.delta = true := by revert hd; cases g.delta <;> simp
              exact (not_Bdecrease_of_delta_true g h1 hBm hd').elim
      · have hBeq : BTrue (s3 g) = BTrue g := hdisp.resolve_left hAeq
        obtain ⟨hAd1, hAd2⟩ := ATrue_s3_dist_le_one g
        rcases (by omega : ATrue (s3 g) = ATrue g + 1 ∨ ATrue (s3 g) = ATrue g - 1)
          with hAp | hAm
        · by_cases hd : g.delta = true
          · have := lRTrue_s3_eq_of_Aincrease_delta_true' g h1 h2 hAp hBeq hd
            right; exact_mod_cast this.symm
          · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
            exact (not_Aincrease_of_delta_false g h1 hAp hd').elim
        · by_cases hd : g.delta = false
          · have := lRTrue_s3_eq_of_Adecrease_delta_false' g h1 h2 hAm hBeq hd
            left; exact_mod_cast this
          · have hd' : g.delta = true := by revert hd; cases g.delta <;> simp
            exact (not_Adecrease_of_delta_true g h2 hAm hd').elim
    · rw [Finset.not_nonempty_iff_eq_empty] at h2
      have hnat := lRTrue_s3_eq_of_occTrue_s3g_empty g h2
      obtain ⟨x, hx⟩ := h1
      have hxA : ATrue g ≤ x := ATrue_le hx
      have hxB : x ≤ BTrue g := le_BTrue hx
      have hxIcc : x ∈ Finset.Icc (ATrue g) (BTrue g) := Finset.mem_Icc.mpr ⟨hxA, hxB⟩
      have hmux1 : 1 ≤ g.toPathData.mu x := by
        unfold SiteCost.PathData.mu
        simp only [EltBridge.Elt.toPathData]
        split_ifs with h
        · omega
        · push_neg at h
          rcases eq_or_ne (g.d x) 0 with hz | hz
          · have hf := h hz
            have := Int.natAbs_pos.mpr hf
            omega
          · have := Int.natAbs_pos.mpr hz
            omega
      have hsumge : g.toPathData.mu x ≤ ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) hxIcc
      have hpos : 1 ≤ lRTrue g := by
        unfold lRTrue
        omega
      right
      have : (lRTrue (s3 g) : ℤ) = lRTrue g - 1 := by exact_mod_cast hnat
      omega
  · rw [Finset.not_nonempty_iff_eq_empty] at h1
    have := lRTrue_s3_eq_of_occTrue_g_empty g h1
    left; exact_mod_cast this


theorem phiZ_dist_le_one_s3 (g : EltBridge.Elt) : (PhiZ (s3 g) - PhiZ g) ^ 2 ≤ 1 := by
  have hc : cTrue (s3 g) = cTrue g := cTrue_s3_eq g
  have hl := lRTrue_s3_dist_one g
  unfold PhiZ
  rw [hc]
  rcases hl with h | h
  · rw [h]; ring_nf; omega
  · rw [show (lRTrue g : ℤ) = lRTrue (s3 g) + 1 from h]; ring_nf; omega


theorem toPathData_mu_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) (j : ℤ) :
    g.toPathData.mu j = h.toPathData.mu j := by
  unfold SiteCost.PathData.mu
  simp only [EltBridge.Elt.toPathData]
  rw [H.1, H.2.2.2]

theorem toPathData_siteCost_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) (s : ℤ) :
    g.toPathData.siteCost s = h.toPathData.siteCost s := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD
  simp only [EltBridge.Elt.toPathData, H.1, H.2.1, H.2.2.1, H.2.2.2]
  rfl

theorem toPathData_cut_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) (s : ℤ) :
    g.toPathData.cut s ↔ h.toPathData.cut s := by
  unfold SiteCost.PathData.cut SiteCost.PathData.alphaAt SiteCost.PathData.betaAt  
    SiteCost.PathData.PhiAt SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD
    SiteCost.PathData.f
  simp only [EltBridge.Elt.toPathData, H.1, H.2.1, H.2.2.1, H.2.2.2]
  tauto

theorem occTrue_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) :
    occTrue g = occTrue h := by
  ext j
  unfold occTrue
  constructor
  · intro hj
    have hpred := (Finset.mem_filter.mp hj).2
    have hpred' : h.d j ≠ 0 ∨ SiteCost.travel h.kstar j ≠ 0 := by
      rw [← H.2.2.2, ← H.1]; exact hpred
    have hmem : j ∈ h.supp := by
      by_contra hc
      have := (h.hsupp j hc)
      rcases hpred' with hp | hp
      · exact hp this.1
      · exact hp this.2
    exact Finset.mem_filter.mpr ⟨hmem, hpred'⟩
  · intro hj
    have hpred := (Finset.mem_filter.mp hj).2
    have hpred' : g.d j ≠ 0 ∨ SiteCost.travel g.kstar j ≠ 0 := by
      rw [H.2.2.2, H.1]; exact hpred
    have hmem : j ∈ g.supp := by
      by_contra hc
      have := (g.hsupp j hc)
      rcases hpred' with hp | hp
      · exact hp this.1
      · exact hp this.2
    exact Finset.mem_filter.mpr ⟨hmem, hpred'⟩

theorem ATrue_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) :
    ATrue g = ATrue h := by
  unfold ATrue
  rw [occTrue_congr H]

theorem BTrue_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) :
    BTrue g = BTrue h := by
  unfold BTrue
  rw [occTrue_congr H]

theorem lRTrue_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) :
    lRTrue g = lRTrue h := by
  unfold lRTrue
  rw [ATrue_congr H, BTrue_congr H]
  congr 1
  · exact Finset.sum_congr rfl (fun x _ => toPathData_mu_congr H x)
  · exact Finset.sum_congr rfl (fun x _ => toPathData_siteCost_congr H x)

theorem ShieldFires_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) :
    ShieldFires g ↔ ShieldFires h := by
  unfold ShieldFires
  rw [H.1, H.2.2.1]
  constructor
  · rintro ⟨hk, hd, hl, hr⟩
    exact ⟨hk, hd, fun j hj => by rw [← H.2.2.2]; exact hl j hj,
      by obtain ⟨j, hj1, hj2⟩ := hr; exact ⟨j, hj1, by rw [← H.2.2.2]; exact hj2⟩⟩
  · rintro ⟨hk, hd, hl, hr⟩
    exact ⟨hk, hd, fun j hj => by rw [H.2.2.2]; exact hl j hj,
      by obtain ⟨j, hj1, hj2⟩ := hr; exact ⟨j, hj1, by rw [H.2.2.2]; exact hj2⟩⟩

theorem cTrue_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) :
    cTrue g = cTrue h := by
  unfold cTrue
  rw [ATrue_congr H, BTrue_congr H]
  congr 1
  · have hset : (Finset.Ioo (ATrue h) (BTrue h + 1)).filter g.toPathData.cut
        = (Finset.Ioo (ATrue h) (BTrue h + 1)).filter h.toPathData.cut :=
      Finset.filter_congr (fun x _ => toPathData_cut_congr H x)
    rw [hset]
  · by_cases hc : ShieldFires g ∧ g.toPathData.cut 0
    · rw [if_pos hc]
      have hc' : ShieldFires h ∧ h.toPathData.cut 0 :=
        ⟨(ShieldFires_congr H).mp hc.1, (toPathData_cut_congr H 0).mp hc.2⟩
      rw [if_pos hc']
    · rw [if_neg hc]
      have hc' : ¬ (ShieldFires h ∧ h.toPathData.cut 0) := by
        rintro ⟨h1, h2⟩
        exact hc ⟨(ShieldFires_congr H).mpr h1, (toPathData_cut_congr H 0).mpr h2⟩
      rw [if_neg hc']

theorem PhiZ_congr {g h : EltBridge.Elt} (H : EltBridge.Elt.SameElt g h) :
    PhiZ g = PhiZ h := by
  unfold PhiZ
  rw [lRTrue_congr H, cTrue_congr H]


theorem phiZ_dist_le_one_of_Gen {a b : EltBridge.Elt} (H : EltBridge.Elt.Gen a b) :
    (PhiZ b - PhiZ a) ^ 2 ≤ 1 := by
  rcases H with h1 | h2 | h3
  · rw [PhiZ_congr h1]; exact phiZ_dist_le_one_s1 a
  · rw [PhiZ_congr h2]; exact phiZ_dist_le_one_s2 a
  · rw [PhiZ_congr h3]; exact phiZ_dist_le_one_s3 a


theorem PhiZ_one : PhiZ EltBridge.Elt.one = 0 := by
  unfold PhiZ
  rw [lRTrue_one, cTrue_one]
  norm_num

theorem reaches_phiZ_abs_le {n : ℕ} {g : EltBridge.Elt} (hn : EltBridge.Elt.Reaches n g) :
    |PhiZ g| ≤ (n : ℤ) := by
  induction hn with
  | refl hsame =>
    rw [PhiZ_congr hsame, PhiZ_one]
    simp
  | @step n a b hstep hgen ih =>
    have hdist := phiZ_dist_le_one_of_Gen hgen
    have habs : -1 ≤ PhiZ b - PhiZ a ∧ PhiZ b - PhiZ a ≤ 1 := by
      constructor <;> nlinarith [sq_abs (PhiZ b - PhiZ a), abs_nonneg (PhiZ b - PhiZ a)]
    have hia := abs_le.mp ih
    rw [abs_le]
    push_cast
    omega

theorem wordLength_ge_phiZ_abs {g : EltBridge.Elt} (h : EltBridge.Elt.Reachable g) :
    (EltBridge.Elt.wordLength g : ℤ) ≥ |PhiZ g| :=
  reaches_phiZ_abs_le (EltBridge.Elt.reaches_wordLength h)


theorem wordLength_ge_lRTrue_add_two_cTrue {g : EltBridge.Elt} (h : EltBridge.Elt.Reachable g) :
    (EltBridge.Elt.wordLength g : ℤ) ≥ (lRTrue g : ℤ) + 2 * (cTrue g : ℤ) := by
  have hge := wordLength_ge_phiZ_abs h
  have hnn : (0 : ℤ) ≤ PhiZ g := by unfold PhiZ; positivity
  rw [abs_of_nonneg hnn] at hge
  unfold PhiZ at hge
  omega


theorem occTrue_empty_of_lRTrue_eq_zero {g : EltBridge.Elt} (h0 : lRTrue g = 0) :
    occTrue g = ∅ := by
  by_contra hne
  have hne' : (occTrue g).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨x, hx⟩ := hne'
  have hxA : ATrue g ≤ x := ATrue_le hx
  have hxB : x ≤ BTrue g := le_BTrue hx
  have hxIcc : x ∈ Finset.Icc (ATrue g) (BTrue g) := Finset.mem_Icc.mpr ⟨hxA, hxB⟩
  have hmux1 : 1 ≤ g.toPathData.mu x := by
    unfold SiteCost.PathData.mu
    simp only [EltBridge.Elt.toPathData]
    split_ifs with h
    · omega
    · push_neg at h
      rcases eq_or_ne (g.d x) 0 with hz | hz
      · have hf := h hz
        have := Int.natAbs_pos.mpr hf
        omega
      · have := Int.natAbs_pos.mpr hz
        omega
  have hsumge : g.toPathData.mu x ≤ ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le _) hxIcc
  unfold lRTrue at h0
  omega

theorem siteCost_zero_trivial (g : EltBridge.Elt) (hk : g.kstar = 0)
    (hd : ∀ j, g.d j = 0) (hδ : g.delta = false) (heps : g.eps = 1) :
    g.toPathData.siteCost 0 = 0 := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp only [EltBridge.Elt.toPathData, hd, hk, heps, hδ]
  norm_num

theorem siteCost_zero_trivial_pos (g : EltBridge.Elt) (hk : g.kstar = 0)
    (hd : ∀ j, g.d j = 0) (hne : ¬ (g.delta = false ∧ g.eps = 1)) :
    0 < g.toPathData.siteCost 0 := by
  have heps := g.heps
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp only [EltBridge.Elt.toPathData, hd, hk]
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ
  · simp only [hδ]
    rcases heps with he | he <;> simp [he]
  · simp only [hδ]
    rcases heps with he | he
    · exact absurd ⟨hδ, he⟩ hne
    · simp [he]

theorem trivial_lRTrue_eq_siteCost0 {g : EltBridge.Elt} (hk : g.kstar = 0)
    (hd : ∀ j, g.d j = 0) : lRTrue g = g.toPathData.siteCost 0 := by
  have hoc : occTrue g = ∅ := by
    unfold occTrue
    rw [Finset.filter_eq_empty_iff]
    intro j _
    rw [hd j, hk, SiteCost.travel_of_kstar_zero]
    simp
  have hA : ATrue g = 0 := by unfold ATrue; rw [dif_neg (by rw [hoc]; simp)]
  have hB : BTrue g = -1 := by unfold BTrue; rw [dif_neg (by rw [hoc]; simp)]
  unfold lRTrue
  rw [hA, hB]
  simp

theorem phiZ_eq_zero_imp_sameElt_one {g : EltBridge.Elt} (h0 : PhiZ g = 0) :
    EltBridge.Elt.SameElt g EltBridge.Elt.one := by
  have hlc : lRTrue g = 0 ∧ cTrue g = 0 := by
    unfold PhiZ at h0
    constructor <;> omega
  have hoc := occTrue_empty_of_lRTrue_eq_zero hlc.1
  have hk : g.kstar = 0 := occTrue_g_empty_kstar_zero hoc
  have hd : ∀ j, g.d j = 0 := occTrue_g_empty_d_zero hoc
  have hlrs : lRTrue g = g.toPathData.siteCost 0 := trivial_lRTrue_eq_siteCost0 hk hd
  have hsc0 : g.toPathData.siteCost 0 = 0 := by omega
  have hcase : g.delta = false ∧ g.eps = 1 := by
    by_contra hne
    have := siteCost_zero_trivial_pos g hk hd hne
    omega
  refine ⟨hk, hcase.2, hcase.1, ?_⟩
  funext j
  rw [hd j]
  rfl


theorem trivial_siteCost0_val (g : EltBridge.Elt) (hk : g.kstar = 0)
    (hd : ∀ j, g.d j = 0) :
    g.toPathData.siteCost 0
      = if g.delta = false ∧ g.eps = 1 then 0 else if g.delta = true then 1 else 2 := by
  have heps := g.heps
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  simp only [EltBridge.Elt.toPathData, hd, hk]
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ
  · simp only [hδ, if_true, if_false]
    rcases heps with he | he <;> simp [he]
  · simp only [hδ]
    rcases heps with he | he <;> simp [he]

theorem trivial_PhiZ_val (g : EltBridge.Elt) (hk : g.kstar = 0) (hd : ∀ j, g.d j = 0) :
    PhiZ g = if g.delta = false ∧ g.eps = 1 then 0 else if g.delta = true then 1 else 2 := by
  have hlrs := trivial_lRTrue_eq_siteCost0 hk hd
  have hcz : cTrue g = 0 := by
    unfold cTrue
    have hoc : occTrue g = ∅ := by
      unfold occTrue
      rw [Finset.filter_eq_empty_iff]
      intro j _
      rw [hd j, hk, SiteCost.travel_of_kstar_zero]
      simp
    have hA : ATrue g = 0 := by unfold ATrue; rw [dif_neg (by rw [hoc]; simp)]
    have hB : BTrue g = -1 := by unfold BTrue; rw [dif_neg (by rw [hoc]; simp)]
    rw [hA, hB]
    have hshield : ¬ ShieldFires g := by
      rintro ⟨-, -, -, ⟨j, hj1, hj2⟩⟩
      exact hj2 (hd j)
    rw [if_neg (fun h => hshield h.1)]
    norm_num
  unfold PhiZ
  rw [hlrs, hcz, trivial_siteCost0_val g hk hd]
  split_ifs <;> ring

theorem trivial_descent (g : EltBridge.Elt) (hk : g.kstar = 0) (hd : ∀ j, g.d j = 0)
    (hne : ¬ (g.delta = false ∧ g.eps = 1)) :
    PhiZ (EltBridge.Elt.s1 g) < PhiZ g ∨ PhiZ (EltBridge.Elt.s2 g) < PhiZ g := by
  have hkg := trivial_PhiZ_val g hk hd
  have hk1 : (EltBridge.Elt.s1 g).kstar = 0 := by rw [EltBridge.Elt.s1_kstar]; exact hk
  have hd1 : ∀ j, (EltBridge.Elt.s1 g).d j = 0 := by rw [EltBridge.Elt.s1_d]; exact hd
  have hk2 : (EltBridge.Elt.s2 g).kstar = 0 := by
    show g.kstar = 0; exact hk
  have hd2 : ∀ j, (EltBridge.Elt.s2 g).d j = 0 := by
    show ∀ j, g.d j = 0; exact hd
  have hval1 := trivial_PhiZ_val (EltBridge.Elt.s1 g) hk1 hd1
  have hval2 := trivial_PhiZ_val (EltBridge.Elt.s2 g) hk2 hd2
  have hδ1 : (EltBridge.Elt.s1 g).delta = !g.delta := rfl
  have hδ2 : (EltBridge.Elt.s2 g).delta = !g.delta := rfl
  have heps2 : (EltBridge.Elt.s2 g).eps = -g.eps := rfl
  have heps1 : (EltBridge.Elt.s1 g).eps = g.eps := rfl
  have heps := g.heps
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ
  · -- delta = true
    rcases heps with he | he
    · left
      rw [hval1, hδ1, hδ, heps1, he]
      rw [hkg, hδ, he]
      simp
    · right
      rw [hval2, hδ2, hδ, heps2, he]
      rw [hkg, hδ, he]
      simp
  · -- delta = false, so eps must be -1 (else hne contradicted)
    have he : g.eps = -1 := by
      rcases heps with h | h
      · exact absurd ⟨hδ, h⟩ hne
      · exact h
    left
    rw [hval1, hδ1, hδ, heps1, he]
    rw [hkg, hδ, he]
    simp


theorem phiZ_s3_eq_lRTrue_dist (g : EltBridge.Elt) :
    PhiZ (s3 g) - PhiZ g = (lRTrue (s3 g) : ℤ) - lRTrue g := by
  have hc : cTrue (s3 g) = cTrue g := cTrue_s3_eq g
  unfold PhiZ
  rw [hc]; ring

theorem descent_of_Bdecrease (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g - 1)
    (hd : g.delta = false) : PhiZ (s3 g) < PhiZ g := by
  have hl : (lRTrue (s3 g) : ℤ) + 1 = lRTrue g := by
    exact_mod_cast lRTrue_s3_eq_of_Bdecrease_delta_false' g h1 h2 hA hB hd
  have heq := phiZ_s3_eq_lRTrue_dist g
  omega

theorem descent_of_Aincrease (g : EltBridge.Elt)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g + 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = true) : PhiZ (s3 g) < PhiZ g := by
  have hl : (lRTrue (s3 g) : ℤ) + 1 = lRTrue g := by
    exact_mod_cast lRTrue_s3_eq_of_Aincrease_delta_true' g h1 h2 hA hB hd
  have heq := phiZ_s3_eq_lRTrue_dist g
  omega

theorem descent_of_g_empty (g : EltBridge.Elt) (he : occTrue g = ∅) :
    PhiZ g < PhiZ (s3 g) := by
  have hl : (lRTrue (s3 g) : ℤ) = lRTrue g + 1 := by
    exact_mod_cast lRTrue_s3_eq_of_occTrue_g_empty g he
  have heq := phiZ_s3_eq_lRTrue_dist g
  omega

theorem descent_of_s3g_empty (g : EltBridge.Elt) (he : occTrue (s3 g) = ∅) :
    PhiZ (s3 g) < PhiZ g := by
  have h1 : (occTrue g).Nonempty := by
    rw [← Finset.not_nonempty_iff_eq_empty] at he
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    exact he (occTrue_s3_singleton_of_g_empty g hc ▸ Finset.singleton_nonempty _)
  have hnat := lRTrue_s3_eq_of_occTrue_s3g_empty g he
  obtain ⟨x, hx⟩ := h1
  have hxA : ATrue g ≤ x := ATrue_le hx
  have hxB : x ≤ BTrue g := le_BTrue hx
  have hxIcc : x ∈ Finset.Icc (ATrue g) (BTrue g) := Finset.mem_Icc.mpr ⟨hxA, hxB⟩
  have hmux1 : 1 ≤ g.toPathData.mu x := by
    unfold SiteCost.PathData.mu
    simp only [EltBridge.Elt.toPathData]
    split_ifs with h
    · omega
    · push_neg at h
      rcases eq_or_ne (g.d x) 0 with hz | hz
      · have hf := h hz
        have := Int.natAbs_pos.mpr hf
        omega
      · have := Int.natAbs_pos.mpr hz
        omega
  have hsumge : g.toPathData.mu x ≤ ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), g.toPathData.mu j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le _) hxIcc
  have hpos : 1 ≤ lRTrue g := by unfold lRTrue; omega
  have hl : (lRTrue (s3 g) : ℤ) = lRTrue g - 1 := by exact_mod_cast hnat
  have heq := phiZ_s3_eq_lRTrue_dist g
  omega


theorem alphaAt_sub_betaAt_kstar (g : EltBridge.Elt) :
    g.toPathData.alphaAt g.kstar - g.toPathData.betaAt g.kstar
      = g.d (g.kstar - 1) - g.d g.kstar - SiteCost.vArr g.kstar + g.eps := by
  unfold SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD
  simp only [EltBridge.Elt.toPathData]
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ <;> simp [hδ] <;> ring

theorem travel_kstar_pred_sub_kstar (g : EltBridge.Elt) :
    SiteCost.travel g.kstar (g.kstar - 1) - SiteCost.travel g.kstar g.kstar
      = if g.kstar = 0 then 0 else 1 := by
  unfold SiteCost.travel
  split_ifs <;> omega

theorem alphaAt_betaAt_kstar_parity (g : EltBridge.Elt) :
    (g.toPathData.alphaAt g.kstar - g.toPathData.betaAt g.kstar) % 2 = 0 := by
  have hd := alphaAt_sub_betaAt_kstar g
  have hp1 := g.hpar (g.kstar - 1)
  have hp2 := g.hpar g.kstar
  have ht := travel_kstar_pred_sub_kstar g
  have heps := g.heps
  have hvarr : SiteCost.vArr g.kstar = if g.kstar = 0 then 1 else 0 := by
    unfold SiteCost.vArr
    rfl
  split_ifs at ht hvarr with hk0 <;> rw [hvarr] at hd <;> omega


theorem alphaAt_s1_kstar (g : EltBridge.Elt) :
    (s1 g).toPathData.alphaAt g.kstar
      = g.toPathData.alphaAt g.kstar + (if g.delta = true then g.eps else -g.eps) := by
  have hpd1 : (s1 g).delta = !g.delta := rfl
  have hpe1 : (s1 g).eps = g.eps := rfl
  unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
  simp only [EltBridge.Elt.toPathData, hpd1, hpe1]
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ <;> simp [hδ] <;> ring

theorem betaAt_s1_kstar (g : EltBridge.Elt) :
    (s1 g).toPathData.betaAt g.kstar
      = g.toPathData.betaAt g.kstar + (if g.delta = true then g.eps else -g.eps) := by
  have hpd1 : (s1 g).delta = !g.delta := rfl
  have hpe1 : (s1 g).eps = g.eps := rfl
  unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
  simp only [EltBridge.Elt.toPathData, hpd1, hpe1]
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ <;> simp [hδ] <;> ring

theorem alphaAt_s2_kstar (g : EltBridge.Elt) :
    (s2 g).toPathData.alphaAt g.kstar = g.toPathData.alphaAt g.kstar - g.eps := by
  have hpd1 : (s2 g).delta = !g.delta := rfl
  have hpe1 : (s2 g).eps = -g.eps := rfl
  unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
  simp only [EltBridge.Elt.toPathData, hpd1, hpe1]
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ <;> simp [hδ] <;> ring

theorem betaAt_s2_kstar (g : EltBridge.Elt) :
    (s2 g).toPathData.betaAt g.kstar = g.toPathData.betaAt g.kstar + g.eps := by
  have hpd1 : (s2 g).delta = !g.delta := rfl
  have hpe1 : (s2 g).eps = -g.eps := rfl
  unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
  simp only [EltBridge.Elt.toPathData, hpd1, hpe1]
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ <;> simp [hδ] <;> ring


theorem reaches_exact_of_trivial (g : EltBridge.Elt) (hk : g.kstar = 0)
    (hd : ∀ j, g.d j = 0) :
    EltBridge.Elt.Reaches (if g.delta = false ∧ g.eps = 1 then 0
        else if g.delta = true then 1 else 2) g := by
  have hd' : g.d = fun _ => 0 := funext hd
  rcases g.heps with he | he
  · by_cases hδ : g.delta = true
    · rw [if_neg (fun h => absurd hδ (by simp [h.1])), if_pos hδ]
      exact EltBridge.Elt.Reaches.congr (EltBridge.Elt.Reaches.one.s1)
        ⟨by simp [EltBridge.Elt.one, EltBridge.Elt.s1, hk],
         by simp [EltBridge.Elt.one, EltBridge.Elt.s1, he],
         by simp [EltBridge.Elt.one, EltBridge.Elt.s1, hδ],
         by simp [EltBridge.Elt.one, EltBridge.Elt.s1, hd']⟩
    · simp only [Bool.not_eq_true] at hδ
      rw [if_pos ⟨hδ, he⟩]
      exact EltBridge.Elt.Reaches.congr EltBridge.Elt.Reaches.one
        ⟨by simp [EltBridge.Elt.one, hk], by simp [EltBridge.Elt.one, he],
         by simp [EltBridge.Elt.one, hδ], by simp [EltBridge.Elt.one, hd']⟩
  · by_cases hδ : g.delta = true
    · rw [if_neg (fun h => absurd hδ (by simp [h.1])), if_pos hδ]
      exact EltBridge.Elt.Reaches.congr (EltBridge.Elt.Reaches.one.s2)
        ⟨by simp [EltBridge.Elt.one, EltBridge.Elt.s2, hk],
         by simp [EltBridge.Elt.one, EltBridge.Elt.s2, he],
         by simp [EltBridge.Elt.one, EltBridge.Elt.s2, hδ],
         by simp [EltBridge.Elt.one, EltBridge.Elt.s2, hd']⟩
    · simp only [Bool.not_eq_true] at hδ
      rw [if_neg (by simp [hδ, he]), if_neg (by simp [hδ])]
      exact EltBridge.Elt.Reaches.congr (EltBridge.Elt.Reaches.one.s2.s1)
        ⟨by simp [EltBridge.Elt.one, EltBridge.Elt.s1, EltBridge.Elt.s2, hk],
         by simp [EltBridge.Elt.one, EltBridge.Elt.s1, EltBridge.Elt.s2, he],
         by simp [EltBridge.Elt.one, EltBridge.Elt.s1, EltBridge.Elt.s2, hδ],
         by simp [EltBridge.Elt.one, EltBridge.Elt.s1, EltBridge.Elt.s2, hd']⟩

theorem wordLength_eq_phiZ_of_trivial (g : EltBridge.Elt) (hk : g.kstar = 0)
    (hd : ∀ j, g.d j = 0) : (EltBridge.Elt.wordLength g : ℤ) = PhiZ g := by
  have hval := trivial_PhiZ_val g hk hd
  have hreach := reaches_exact_of_trivial g hk hd
  have hle : EltBridge.Elt.wordLength g
      ≤ (if g.delta = false ∧ g.eps = 1 then 0 else if g.delta = true then 1 else 2) :=
    EltBridge.Elt.wordLength_le hreach
  have hreachable : EltBridge.Elt.Reachable g := ⟨_, hreach⟩
  have hge := wordLength_ge_lRTrue_add_two_cTrue hreachable
  unfold PhiZ at hge hval ⊢
  split_ifs at hval hle <;> omega



theorem alphaAt_kstar_eq_of_left_boundary (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hleft : g.kstar = ATrue g) :
    g.toPathData.alphaAt g.kstar = if g.delta = true then 0 else g.eps := by
  have hlt : g.kstar - 1 < ATrue g := by rw [hleft]; omega
  have hd0 : g.d (g.kstar - 1) = 0 := d_eq_zero_of_lt_ATrue g hlt
  unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD SiteCost.vArr
  simp only [EltBridge.Elt.toPathData]
  rw [hd0]
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ <;> simp [hδ, hk0]

theorem betaAt_kstar_eq_of_right_boundary (g : EltBridge.Elt) (hright : g.kstar = BTrue g + 1) :
    g.toPathData.betaAt g.kstar = if g.delta = true then -g.eps else 0 := by
  have hd0 := d_eq_zero_of_gt_BTrue g (j := g.kstar) (by rw [hright]; omega)
  unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
  simp only [EltBridge.Elt.toPathData]
  rw [hd0]
  rcases Bool.eq_false_or_eq_true g.delta with hδ | hδ <;> simp [hδ]







theorem siteCost_descent_left_delta_false (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hd : g.delta = false) (hleft : g.kstar = ATrue g) :
    (s1 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar ∨
      (s2 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar := by
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  unfold SiteCost.PathData.siteCost
  have hpin := alphaAt_kstar_eq_of_left_boundary g hk0 hleft
  have hpar := alphaAt_betaAt_kstar_parity g
  rw [hpin] at hpar
  rcases heps with he | he <;>
    simp [hd, he] at hpin hpar <;>
    simp [hd, he, hpin] at ha1 ha2 hb1 hb2 <;>
    · have hbne : g.toPathData.betaAt g.kstar ≠ 0 := by omega
      rw [ha1, hb1, ha2, hb2, hpin]
      omega

theorem siteCost_descent_right_delta_true (g : EltBridge.Elt)
    (hd : g.delta = true) (hright : g.kstar = BTrue g + 1) :
    (s1 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar ∨
      (s2 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar := by
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  unfold SiteCost.PathData.siteCost
  have hpin := betaAt_kstar_eq_of_right_boundary g hright
  have hpar := alphaAt_betaAt_kstar_parity g
  rw [hpin] at hpar
  rcases heps with he | he <;>
    simp [hd, he] at hpin hpar <;>
    simp [hd, he, hpin] at ha1 ha2 hb1 hb2 <;>
    · have hane : g.toPathData.alphaAt g.kstar ≠ 0 := by omega
      rw [ha1, hb1, ha2, hb2, hpin]
      omega

theorem siteCost_descent_left_delta_true (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hd : g.delta = true) (hleft : g.kstar = ATrue g)
    (hsign : g.toPathData.betaAt g.kstar * g.eps < 0) :
    (s1 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar ∨
      (s2 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar := by
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  unfold SiteCost.PathData.siteCost
  have hpin := alphaAt_kstar_eq_of_left_boundary g hk0 hleft
  have hpar := alphaAt_betaAt_kstar_parity g
  rw [hpin] at hpar
  rcases heps with he | he <;>
    simp [hd, he] at hpin hsign hpar <;>
    simp [hd, he, hpin] at ha1 ha2 hb1 hb2 <;>
    (left; rw [ha1, hb1, hpin]; omega)

theorem siteCost_descent_right_delta_false (g : EltBridge.Elt)
    (hd : g.delta = false) (hright : g.kstar = BTrue g + 1)
    (hsign : g.toPathData.alphaAt g.kstar * g.eps > 0) :
    (s1 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar ∨
      (s2 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar := by
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  unfold SiteCost.PathData.siteCost
  have hpin := betaAt_kstar_eq_of_right_boundary g hright
  have hpar := alphaAt_betaAt_kstar_parity g
  rw [hpin] at hpar
  rcases heps with he | he <;>
    simp [hd, he] at hpin hsign hpar <;>
    simp [hd, he, hpin] at ha1 ha2 hb1 hb2 <;>
    (left; rw [ha1, hb1, hpin]; omega)


theorem descent_of_Bincrease_via_s1_or_s2 (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g + 1)
    (hd : g.delta = true) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g := by
  have hkeq : g.kstar = BTrue g + 1 := by
    have hc := crossed_eq_of_Bincrease g h2 hB
    rw [if_pos hd, hB] at hc
    omega
  have hnotint : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1) := by simp [hkeq]
  have hAB : ATrue g ≤ BTrue g := by
    obtain ⟨x, hx⟩ := h1
    exact le_trans (ATrue_le hx) (le_BTrue hx)
  have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := by
    rw [hkeq]; simp only [Finset.mem_Icc]; omega
  have hc1 : cTrue (s1 g) = cTrue g := cTrue_s1_eq_of_not_interior_ne_zero g hk0 hnotint
  have hc2 : cTrue (s2 g) = cTrue g := cTrue_s2_eq_of_not_interior_ne_zero g hk0 hnotint
  have hmu1 : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hmu2 : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)), ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR1 : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ) + (((s1 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu1, siteSum_sub_eq_at_kstar_s1 g hkw]; ring
  have hlR2 : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ) + (((s2 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu2, siteSum_sub_eq_at_kstar_s2 g hkw]; ring
  rcases siteCost_descent_right_delta_true g hd hkeq with hs1 | hs2
  · left; unfold PhiZ; rw [hlR1, hc1]; push_cast; omega
  · right; unfold PhiZ; rw [hlR2, hc2]; push_cast; omega


theorem descent_of_Adecrease_via_s1_or_s2 (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g - 1) (hB : BTrue (s3 g) = BTrue g)
    (hd : g.delta = false) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g := by
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hkeq : g.kstar = ATrue g := by
    have hc := crossed_eq_of_Adecrease g h2 hA
    rw [if_neg h1', hA] at hc
    omega
  have hnotint : g.kstar ∉ Finset.Ioo (ATrue g) (BTrue g + 1) := by simp [hkeq]
  have hAB : ATrue g ≤ BTrue g := by
    obtain ⟨x, hx⟩ := h1
    exact le_trans (ATrue_le hx) (le_BTrue hx)
  have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := by
    rw [hkeq]; simp only [Finset.mem_Icc]; omega
  have hc1 : cTrue (s1 g) = cTrue g := cTrue_s1_eq_of_not_interior_ne_zero g hk0 hnotint
  have hc2 : cTrue (s2 g) = cTrue g := cTrue_s2_eq_of_not_interior_ne_zero g hk0 hnotint
  have hmu1 : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hmu2 : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)), ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR1 : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ) + (((s1 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu1, siteSum_sub_eq_at_kstar_s1 g hkw]; ring
  have hlR2 : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ) + (((s2 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu2, siteSum_sub_eq_at_kstar_s2 g hkw]; ring
  rcases siteCost_descent_left_delta_false g hk0 hd hkeq with hs1 | hs2
  · left; unfold PhiZ; rw [hlR1, hc1]; push_cast; omega
  · right; unfold PhiZ; rw [hlR2, hc2]; push_cast; omega


/-- **The descent lemma, EXCEPT for the window-unchanged-with-mu-ascent case.**
Assembles: the trivial class (via `trivial_descent`), `occTrue (s3 g) = ∅` (via
`descent_of_s3g_empty`, a direct `s3`-descent), the two direct-descent window-move
directions (`Bdecrease`, `Aincrease`, both direct `s3`-descents), and the two genuine
growth directions where `s3` itself ascends (`Bincrease`, `Adecrease`, closed via
`descent_of_Bincrease_via_s1_or_s2`/`descent_of_Adecrease_via_s1_or_s2`). The one case
NOT covered: `occTrue g` and `occTrue (s3 g)` both nonempty, window UNCHANGED under `s3`,
and `s3`'s own movement is an ascent (the `mu`-ascent disjunct of
`mu_dist_one_unconditional`) -- this needs the interior-kstar machinery
(`phiZ_dist_le_one_s1/s2_interior`), not yet connected to a genuine descent argument. -/
theorem exists_descent_of_not_window_unchanged_ascent (g : EltBridge.Elt)
    (hne : ¬ EltBridge.Elt.SameElt g EltBridge.Elt.one) (hk0 : g.kstar ≠ 0)
    (hnotcase : ¬ (∃ h1 : (occTrue g).Nonempty, ∃ h2 : (occTrue (s3 g)).Nonempty,
        ATrue (s3 g) = ATrue g ∧ BTrue (s3 g) = BTrue g ∧
        (lRTrue (s3 g) : ℤ) = lRTrue g + 1)) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g ∨ PhiZ (s3 g) < PhiZ g := by
  by_cases h1 : (occTrue g).Nonempty
  · by_cases h2 : (occTrue (s3 g)).Nonempty
    · have hdispRaw := min_or_max_unchanged h1 h2 (occTrue_agree_off_p g)
      have hdisp : ATrue (s3 g) = ATrue g ∨ BTrue (s3 g) = BTrue g := by
        rcases hdispRaw with hmin | hmax
        · left; unfold ATrue; rw [dif_pos h1, dif_pos h2, hmin]
        · right; unfold BTrue; rw [dif_pos h1, dif_pos h2, hmax]
      by_cases hAeq : ATrue (s3 g) = ATrue g
      · by_cases hBeq : BTrue (s3 g) = BTrue g
        · -- window unchanged: use lRTrue_s3_dist_one_of_window_unchanged
          rcases lRTrue_s3_dist_one_of_window_unchanged g hAeq hBeq with hl | hl
          · exact absurd ⟨h1, h2, hAeq, hBeq, hl⟩ hnotcase
          · right; right
            have heq := phiZ_s3_eq_lRTrue_dist g
            omega
        · obtain ⟨hBd1, hBd2⟩ := BTrue_s3_dist_le_one g
          rcases (by omega : BTrue (s3 g) = BTrue g + 1 ∨ BTrue (s3 g) = BTrue g - 1)
            with hBp | hBm
          · by_cases hd : g.delta = true
            · rcases descent_of_Bincrease_via_s1_or_s2 g hk0 h1 h2 hAeq hBp hd with hh | hh
              · left; exact hh
              · right; left; exact hh
            · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
              exact (not_Bincrease_of_delta_false g h2 hBp hd').elim
          · by_cases hd : g.delta = false
            · right; right; exact descent_of_Bdecrease g h1 h2 hAeq hBm hd
            · have hd' : g.delta = true := by revert hd; cases g.delta <;> simp
              exact (not_Bdecrease_of_delta_true g h1 hBm hd').elim
      · have hBeq : BTrue (s3 g) = BTrue g := hdisp.resolve_left hAeq
        obtain ⟨hAd1, hAd2⟩ := ATrue_s3_dist_le_one g
        rcases (by omega : ATrue (s3 g) = ATrue g + 1 ∨ ATrue (s3 g) = ATrue g - 1)
          with hAp | hAm
        · by_cases hd : g.delta = true
          · right; right; exact descent_of_Aincrease g h1 h2 hAp hBeq hd
          · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
            exact (not_Aincrease_of_delta_false g h1 hAp hd').elim
        · by_cases hd : g.delta = false
          · rcases descent_of_Adecrease_via_s1_or_s2 g hk0 h1 h2 hAm hBeq hd with hh | hh
            · left; exact hh
            · right; left; exact hh
          · have hd' : g.delta = true := by revert hd; cases g.delta <;> simp
            exact (not_Adecrease_of_delta_true g h2 hAm hd').elim
    · rw [Finset.not_nonempty_iff_eq_empty] at h2
      right; right; exact descent_of_s3g_empty g h2
  · exfalso
    rw [Finset.not_nonempty_iff_eq_empty] at h1
    exact hk0 (occTrue_g_empty_kstar_zero h1)


theorem d_ne_zero_of_mu_ascent (g : EltBridge.Elt)
    (hasc : ((s3 g).toPathData.mu (if g.delta then g.kstar else g.kstar - 1) : ℤ)
        = g.toPathData.mu (if g.delta then g.kstar else g.kstar - 1) + 1) :
    g.d (if g.delta then g.kstar else g.kstar - 1) ≠ 0 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  intro hd0
  by_cases hd : g.delta = true
  · have hpv : p = g.kstar := by rw [hpdef, if_pos hd]
    rw [hpv] at hd0
    have hpar := g.hpar g.kstar
    have htc0 := SiteCost.travel_cases g.kstar g.kstar
    have htz : SiteCost.travel g.kstar g.kstar = 0 := by omega
    have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
    have hd1 : (s3 g).d g.kstar = g.d g.kstar - g.eps := by
      have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
        rw [s3, dif_pos hd]
      rw [hupd]; simp
    have ht1 : SiteCost.travel (s3 g).kstar g.kstar = SiteCost.travel g.kstar g.kstar + 1 := by
      rw [hkS, EltBridge.Elt.travel_succ_at]
    have heps := g.heps
    have hmug : g.toPathData.mu g.kstar = 2 := by
      unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData, hd0, htz]
    have hmus3 : (s3 g).toPathData.mu g.kstar = 1 := by
      unfold SiteCost.PathData.mu
      simp only [EltBridge.Elt.toPathData]
      rw [hd1, hd0, ht1, htz]
      rcases heps with he | he <;> simp [he]
    rw [hpv, hmug, hmus3] at hasc
    norm_num at hasc
  · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
    have hpv : p = g.kstar - 1 := by rw [hpdef, if_neg (by rw [hd']; simp)]
    rw [hpv] at hd0
    have hpar := g.hpar (g.kstar - 1)
    have htc0 := SiteCost.travel_cases g.kstar (g.kstar - 1)
    have htz : SiteCost.travel g.kstar (g.kstar - 1) = 0 := by
      have h1' : ¬ (g.delta = true) := by rw [hd']; simp
      have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
      have hself : SiteCost.travel (g.kstar - 1) (g.kstar - 1) = 0 ∨
          SiteCost.travel (g.kstar - 1) (g.kstar - 1) ≠ 0 := em _
      omega
    have h1' : ¬ (g.delta = true) := by rw [hd']; simp
    have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
    have hd1 : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by
      have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
        rw [s3, dif_neg h1']
      rw [hupd]; simp
    have ht1 : SiteCost.travel (s3 g).kstar (g.kstar - 1) = SiteCost.travel g.kstar (g.kstar - 1) - 1 := by
      rw [hkS, EltBridge.Elt.travel_pred_at]
    have heps := g.heps
    have hmug : g.toPathData.mu (g.kstar - 1) = 2 := by
      unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData, hd0, htz]
    have hmus3 : (s3 g).toPathData.mu (g.kstar - 1) = 1 := by
      unfold SiteCost.PathData.mu
      simp only [EltBridge.Elt.toPathData]
      rw [hd1, hd0, ht1, htz]
      rcases heps with he | he <;> simp [he]
    rw [hpv, hmug, hmus3] at hasc
    norm_num at hasc


theorem betaAt_ne_pm_one_of_ascent_true (g : EltBridge.Elt) (hd : g.delta = true)
    (hasc : ((s3 g).toPathData.mu g.kstar : ℤ) = g.toPathData.mu g.kstar + 1) :
    g.toPathData.betaAt g.kstar ≠ 1 ∧ g.toPathData.betaAt g.kstar ≠ -1 := by
  have hpar := g.hpar g.kstar
  have htc := SiteCost.travel_cases g.kstar g.kstar
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
  have hd1 : (s3 g).d g.kstar = g.d g.kstar - g.eps := by
    have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
      rw [s3, dif_pos hd]
    rw [hupd]; simp
  have ht1 : SiteCost.travel (s3 g).kstar g.kstar = SiteCost.travel g.kstar g.kstar + 1 := by
    rw [hkS, EltBridge.Elt.travel_succ_at]
  have heps := g.heps
  have hbeta : g.toPathData.betaAt g.kstar = g.d g.kstar - g.eps := by
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
    simp [EltBridge.Elt.toPathData, hd]
  unfold SiteCost.PathData.mu at hasc
  simp only [EltBridge.Elt.toPathData] at hasc
  rw [hbeta]
  split_ifs at hasc with hvac1 hvac2 hvac2 <;>
    rcases htc with ht | ht | ht <;> rcases heps with he | he <;> omega


theorem betaAt_sign_of_ascent_true (g : EltBridge.Elt) (hd : g.delta = true)
    (hasc : ((s3 g).toPathData.mu g.kstar : ℤ) = g.toPathData.mu g.kstar + 1) :
    g.toPathData.betaAt g.kstar * g.eps ≤ 0 := by
  have hpar := g.hpar g.kstar
  have htc := SiteCost.travel_cases g.kstar g.kstar
  have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
  have hd1 : (s3 g).d g.kstar = g.d g.kstar - g.eps := by
    have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
      rw [s3, dif_pos hd]
    rw [hupd]; simp
  have ht1 : SiteCost.travel (s3 g).kstar g.kstar = SiteCost.travel g.kstar g.kstar + 1 := by
    rw [hkS, EltBridge.Elt.travel_succ_at]
  have heps := g.heps
  have hbeta : g.toPathData.betaAt g.kstar = g.d g.kstar - g.eps := by
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
    simp [EltBridge.Elt.toPathData, hd]
  unfold SiteCost.PathData.mu at hasc
  simp only [EltBridge.Elt.toPathData] at hasc
  rw [hbeta]
  split_ifs at hasc with hvac1 hvac2 hvac2 <;>
    rcases htc with ht | ht | ht <;> rcases heps with he | he <;> simp only [he] at * <;> omega


theorem siteCost_descent_of_ascent_true (g : EltBridge.Elt) (hd : g.delta = true)
    (hasc : ((s3 g).toPathData.mu g.kstar : ℤ) = g.toPathData.mu g.kstar + 1)
    (hM : 0 < g.toPathData.siteCost g.kstar) :
    (s1 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar ∨
      (s2 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar := by
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  have hpar := alphaAt_betaAt_kstar_parity g
  have hne1 := betaAt_ne_pm_one_of_ascent_true g hd hasc
  have hsign := betaAt_sign_of_ascent_true g hd hasc
  clear hasc
  unfold SiteCost.PathData.siteCost at hM ⊢
  rcases heps with he | he <;>
    simp [hd, he] at ha1 hb1 ha2 hb2 hpar hne1 hsign hM <;>
    rcases lt_trichotomy (g.toPathData.alphaAt g.kstar) 0 with ha | ha | ha <;>
    first | (left; omega) | (right; omega)


theorem cut_kstar_false_of_ascent_true (g : EltBridge.Elt) (hd : g.delta = true)
    (hasc : ((s3 g).toPathData.mu g.kstar : ℤ) = g.toPathData.mu g.kstar + 1)
    (hM : 0 < g.toPathData.siteCost g.kstar) :
    ¬ g.toPathData.cut g.kstar ∧ ¬ (s1 g).toPathData.cut g.kstar ∧
      ¬ (s2 g).toPathData.cut g.kstar := by
  have hne1 := betaAt_ne_pm_one_of_ascent_true g hd hasc
  have hsign := betaAt_sign_of_ascent_true g hd hasc
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  refine ⟨?_, ?_, ?_⟩ <;>
    · intro hcut
      rw [cut_iff_siteCost_zero] at hcut
      unfold SiteCost.PathData.siteCost at hcut hM
      first
        | (rcases heps with he | he <;> simp [hd, he] at ha1 hb1 hM hne1 hsign hcut <;> omega)
        | omega

theorem descent_of_ascent_true (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0) (hd : g.delta = true)
    (hasc : ((s3 g).toPathData.mu g.kstar : ℤ) = g.toPathData.mu g.kstar + 1)
    (hM : 0 < g.toPathData.siteCost g.kstar) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g := by
  have hcuts := cut_kstar_false_of_ascent_true g hd hasc hM
  have hs1 : ¬ ShieldFires g := not_shieldFires_of_kstar_ne_zero g hk0
  have hs1' : ¬ ShieldFires (s1 g) := not_shieldFires_of_kstar_ne_zero (s1 g) (by rw [s1_kstar]; exact hk0)
  have hs2' : ¬ ShieldFires (s2 g) := not_shieldFires_of_kstar_ne_zero (s2 g) (by rw [s2_kstar]; exact hk0)
  have hc1 : cTrue (s1 g) = cTrue g := by
    have hzcast : ((cTrue (s1 g) : ℤ)) = ((cTrue g : ℤ)) := by
      rw [cTrue_eq_filter_of_not_shield _ hs1', cTrue_eq_filter_of_not_shield _ hs1,
        ATrue_s1, BTrue_s1]
      have : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s1 g).toPathData.cut
          = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
        apply Finset.filter_congr
        intro s hsS
        by_cases hsk : s = g.kstar
        · subst hsk; simp [hcuts.1, hcuts.2.1]
        · rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
            siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
      rw [this]
    exact_mod_cast hzcast
  have hc2 : cTrue (s2 g) = cTrue g := by
    have hzcast : ((cTrue (s2 g) : ℤ)) = ((cTrue g : ℤ)) := by
      rw [cTrue_eq_filter_of_not_shield _ hs2', cTrue_eq_filter_of_not_shield _ hs1,
        ATrue_s2, BTrue_s2]
      have : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s2 g).toPathData.cut
          = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
        apply Finset.filter_congr
        intro s hsS
        by_cases hsk : s = g.kstar
        · subst hsk; simp [hcuts.1, hcuts.2.2]
        · rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
            siteCost_eq_of_ne_kstar (P := (s2 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
      rw [this]
    exact_mod_cast hzcast
  have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := kstar_mem_corrected_window g
  have hmu1 : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hmu2 : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)), ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR1 : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ) + (((s1 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu1, siteSum_sub_eq_at_kstar_s1 g hkw]; ring
  have hlR2 : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ) + (((s2 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu2, siteSum_sub_eq_at_kstar_s2 g hkw]; ring
  rcases siteCost_descent_of_ascent_true g hd hasc hM with hd1 | hd2
  · left; unfold PhiZ; rw [hlR1, hc1]; push_cast; omega
  · right; unfold PhiZ; rw [hlR2, hc2]; push_cast; omega


theorem travel_pred_ne_neg_one (k : ℤ) : SiteCost.travel k (k - 1) ≠ -1 := by
  unfold SiteCost.travel; split_ifs <;> omega

theorem alphaAt_ne_pm_one_of_ascent_false (g : EltBridge.Elt) (hd : g.delta = false)
    (hk0 : g.kstar ≠ 0)
    (hasc : ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1) :
    g.toPathData.alphaAt g.kstar ≠ 1 ∧ g.toPathData.alphaAt g.kstar ≠ -1 := by
  have hpar := g.hpar (g.kstar - 1)
  have htc := SiteCost.travel_cases g.kstar (g.kstar - 1)
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
  have hd1 : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by
    have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
      rw [s3, dif_neg h1']
    rw [hupd]; simp
  have ht1 : SiteCost.travel (s3 g).kstar (g.kstar - 1) = SiteCost.travel g.kstar (g.kstar - 1) - 1 := by
    rw [hkS, EltBridge.Elt.travel_pred_at]
  have heps := g.heps
  have halpha : g.toPathData.alphaAt g.kstar = g.d (g.kstar - 1) + g.eps := by
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD SiteCost.vArr
    simp [EltBridge.Elt.toPathData, hd, hk0]
  have htne := travel_pred_ne_neg_one g.kstar
  have hkey : g.d (g.kstar - 1) + g.eps ≠ 1 ∧ g.d (g.kstar - 1) + g.eps ≠ -1 := by
    unfold SiteCost.PathData.mu at hasc
    simp only [EltBridge.Elt.toPathData] at hasc
    split_ifs at hasc with hvac1 hvac2 hvac2 <;>
      rcases htc with ht | ht | ht <;> rcases heps with he | he <;> omega
  rw [halpha]; exact hkey

theorem alphaAt_sign_of_ascent_false (g : EltBridge.Elt) (hd : g.delta = false)
    (hk0 : g.kstar ≠ 0)
    (hasc : ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1) :
    g.toPathData.alphaAt g.kstar * g.eps ≥ 0 := by
  have hpar := g.hpar (g.kstar - 1)
  have htc := SiteCost.travel_cases g.kstar (g.kstar - 1)
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
  have hd1 : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by
    have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
      rw [s3, dif_neg h1']
    rw [hupd]; simp
  have ht1 : SiteCost.travel (s3 g).kstar (g.kstar - 1) = SiteCost.travel g.kstar (g.kstar - 1) - 1 := by
    rw [hkS, EltBridge.Elt.travel_pred_at]
  have heps := g.heps
  have halpha : g.toPathData.alphaAt g.kstar = g.d (g.kstar - 1) + g.eps := by
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD SiteCost.vArr
    simp [EltBridge.Elt.toPathData, hd, hk0]
  have htne := travel_pred_ne_neg_one g.kstar
  unfold SiteCost.PathData.mu at hasc
  simp only [EltBridge.Elt.toPathData] at hasc
  rw [halpha]
  split_ifs at hasc with hvac1 hvac2 hvac2 <;>
    rcases htc with ht | ht | ht <;> rcases heps with he | he <;> simp only [he] at * <;> omega

theorem siteCost_descent_of_ascent_false (g : EltBridge.Elt) (hd : g.delta = false)
    (hk0 : g.kstar ≠ 0)
    (hasc : ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1)
    (hM : 0 < g.toPathData.siteCost g.kstar) :
    (s1 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar ∨
      (s2 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar := by
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  have hpar := alphaAt_betaAt_kstar_parity g
  have hne1 := alphaAt_ne_pm_one_of_ascent_false g hd hk0 hasc
  have hsign := alphaAt_sign_of_ascent_false g hd hk0 hasc
  clear hasc
  unfold SiteCost.PathData.siteCost at hM ⊢
  rcases heps with he | he <;>
    simp [hd, he] at ha1 hb1 ha2 hb2 hpar hne1 hsign hM <;>
    rcases lt_trichotomy (g.toPathData.betaAt g.kstar) 0 with hb | hb | hb <;>
    first | (left; omega) | (right; omega)



theorem cut_kstar_false_of_ascent_false (g : EltBridge.Elt) (hd : g.delta = false)
    (hk0 : g.kstar ≠ 0)
    (hasc : ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1)
    (hM : 0 < g.toPathData.siteCost g.kstar) :
    ¬ g.toPathData.cut g.kstar ∧ ¬ (s1 g).toPathData.cut g.kstar ∧
      ¬ (s2 g).toPathData.cut g.kstar := by
  have hne1 := alphaAt_ne_pm_one_of_ascent_false g hd hk0 hasc
  have hsign := alphaAt_sign_of_ascent_false g hd hk0 hasc
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  refine ⟨?_, ?_, ?_⟩ <;>
    · intro hcut
      rw [cut_iff_siteCost_zero] at hcut
      unfold SiteCost.PathData.siteCost at hcut hM
      first
        | (rcases heps with he | he <;> simp [hd, he] at ha1 hb1 hM hne1 hsign hcut <;> omega)
        | omega

theorem descent_of_ascent_false (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0) (hd : g.delta = false)
    (hasc : ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1)
    (hM : 0 < g.toPathData.siteCost g.kstar) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g := by
  have hcuts := cut_kstar_false_of_ascent_false g hd hk0 hasc hM
  have hs1 : ¬ ShieldFires g := not_shieldFires_of_kstar_ne_zero g hk0
  have hs1' : ¬ ShieldFires (s1 g) := not_shieldFires_of_kstar_ne_zero (s1 g) (by rw [s1_kstar]; exact hk0)
  have hs2' : ¬ ShieldFires (s2 g) := not_shieldFires_of_kstar_ne_zero (s2 g) (by rw [s2_kstar]; exact hk0)
  have hc1 : cTrue (s1 g) = cTrue g := by
    have hzcast : ((cTrue (s1 g) : ℤ)) = ((cTrue g : ℤ)) := by
      rw [cTrue_eq_filter_of_not_shield _ hs1', cTrue_eq_filter_of_not_shield _ hs1,
        ATrue_s1, BTrue_s1]
      have : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s1 g).toPathData.cut
          = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
        apply Finset.filter_congr
        intro s hsS
        by_cases hsk : s = g.kstar
        · subst hsk; simp [hcuts.1, hcuts.2.1]
        · rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
            siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
      rw [this]
    exact_mod_cast hzcast
  have hc2 : cTrue (s2 g) = cTrue g := by
    have hzcast : ((cTrue (s2 g) : ℤ)) = ((cTrue g : ℤ)) := by
      rw [cTrue_eq_filter_of_not_shield _ hs2', cTrue_eq_filter_of_not_shield _ hs1,
        ATrue_s2, BTrue_s2]
      have : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s2 g).toPathData.cut
          = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
        apply Finset.filter_congr
        intro s hsS
        by_cases hsk : s = g.kstar
        · subst hsk; simp [hcuts.1, hcuts.2.2]
        · rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
            siteCost_eq_of_ne_kstar (P := (s2 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
      rw [this]
    exact_mod_cast hzcast
  have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := kstar_mem_corrected_window g
  have hmu1 : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hmu2 : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)), ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR1 : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ) + (((s1 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu1, siteSum_sub_eq_at_kstar_s1 g hkw]; ring
  have hlR2 : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ) + (((s2 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu2, siteSum_sub_eq_at_kstar_s2 g hkw]; ring
  rcases siteCost_descent_of_ascent_false g hd hk0 hasc hM with hd1 | hd2
  · left; unfold PhiZ; rw [hlR1, hc1]; push_cast; omega
  · right; unfold PhiZ; rw [hlR2, hc2]; push_cast; omega


theorem mu_ascent_of_lRTrue_ascent_window_unchanged (g : EltBridge.Elt)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g)
    (hasc : (lRTrue (s3 g) : ℤ) = lRTrue g + 1) :
    ((s3 g).toPathData.mu (if g.delta then g.kstar else g.kstar - 1) : ℤ)
      = g.toPathData.mu (if g.delta then g.kstar else g.kstar - 1) + 1 := by
  set p := (if g.delta then g.kstar else g.kstar - 1) with hpdef
  have hpmem := crossed_mem_mu_window_of_window_unchanged g hA hB
  rw [← hpdef] at hpmem
  have hmusum : (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), ((s3 g).toPathData.mu j : ℤ))
      = (∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ))
          + (((s3 g).toPathData.mu p : ℤ) - (g.toPathData.mu p : ℤ)) :=
    sum_eq_add_diff_of_eq_off hpmem (fun x _ hx => by
      have hx' : x ≠ (if g.delta then g.kstar else g.kstar - 1) := by rwa [hpdef] at hx
      have := s3_mu_agree g x hx'
      exact_mod_cast this)
  have hsitesum : (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), ((s3 g).toPathData.siteCost s : ℤ))
      = (∑ s ∈ Finset.Icc (ATrue g) (BTrue g + 1), (g.toPathData.siteCost s : ℤ)) :=
    Finset.sum_congr rfl (fun x _ => by exact_mod_cast EltBridge.Elt.s3_siteCost_eq g x)
  have hlr : (lRTrue (s3 g) : ℤ) = (lRTrue g : ℤ)
      + (((s3 g).toPathData.mu p : ℤ) - (g.toPathData.mu p : ℤ)) := by
    unfold lRTrue
    rw [hA, hB]
    push_cast
    rw [hmusum, hsitesum]
    ring
  omega


theorem exists_descent_of_hM (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hne : ¬ EltBridge.Elt.SameElt g EltBridge.Elt.one)
    (hMcase : ∀ h1 : (occTrue g).Nonempty, ∀ h2 : (occTrue (s3 g)).Nonempty,
        ATrue (s3 g) = ATrue g → BTrue (s3 g) = BTrue g →
        (lRTrue (s3 g) : ℤ) = lRTrue g + 1 → 0 < g.toPathData.siteCost g.kstar) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g ∨ PhiZ (s3 g) < PhiZ g := by
  by_cases hcase : ∃ h1 : (occTrue g).Nonempty, ∃ h2 : (occTrue (s3 g)).Nonempty,
      ATrue (s3 g) = ATrue g ∧ BTrue (s3 g) = BTrue g ∧
      (lRTrue (s3 g) : ℤ) = lRTrue g + 1
  · obtain ⟨h1, h2, hA, hB, hlr⟩ := hcase
    have hasc := mu_ascent_of_lRTrue_ascent_window_unchanged g hA hB hlr
    have hM : 0 < g.toPathData.siteCost g.kstar := hMcase h1 h2 hA hB hlr
    by_cases hd : g.delta = true
    · rw [if_pos hd] at hasc
      rcases descent_of_ascent_true g hk0 hd hasc hM with hh | hh
      · left; exact hh
      · right; left; exact hh
    · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
      rw [if_neg (by rw [hd']; simp)] at hasc
      rcases descent_of_ascent_false g hk0 hd' hasc hM with hh | hh
      · left; exact hh
      · right; left; exact hh
  · push_neg at hcase
    exact exists_descent_of_not_window_unchanged_ascent g hne hk0
      (fun ⟨h1, h2, hA, hB, hlr⟩ => absurd hlr (by
        intro hlr'; exact absurd (hcase h1 h2 hA hB) (by simp [hlr'])))


theorem ATrue_mem_occTrue_of_ne_zero {g : EltBridge.Elt} (h1 : (occTrue g).Nonempty)
    (hne : ATrue g ≠ 0) : ATrue g ∈ occTrue g := by
  unfold ATrue at hne ⊢
  rw [dif_pos h1] at hne ⊢
  have hmin : min 0 ((occTrue g).min' h1) = (occTrue g).min' h1 := by
    by_cases h : (occTrue g).min' h1 < 0
    · omega
    · exfalso; apply hne; omega
  rw [hmin]
  exact Finset.min'_mem _ h1

theorem BTrue_mem_occTrue_of_ne_neg_one {g : EltBridge.Elt} (h1 : (occTrue g).Nonempty)
    (hne : BTrue g ≠ -1) : BTrue g ∈ occTrue g := by
  unfold BTrue at hne ⊢
  rw [dif_pos h1] at hne ⊢
  have hmax : max (-1) ((occTrue g).max' h1) = (occTrue g).max' h1 := by
    by_cases h : (-1 : ℤ) < (occTrue g).max' h1
    · omega
    · exfalso; apply hne; omega
  rw [hmax]
  exact Finset.max'_mem _ h1


theorem travel_self_ne_one (k : ℤ) : SiteCost.travel k k ≠ 1 := by
  unfold SiteCost.travel; split_ifs <;> omega

theorem kstar_interior_of_siteCost_zero_ascent (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (h1 : (occTrue g).Nonempty) (h2 : (occTrue (s3 g)).Nonempty)
    (hA : ATrue (s3 g) = ATrue g) (hB : BTrue (s3 g) = BTrue g)
    (hM0 : g.toPathData.siteCost g.kstar = 0) :
    ATrue g < g.kstar ∧ g.kstar < BTrue g + 1 := by
  have halphabeta : g.toPathData.alphaAt g.kstar = 0 ∧ g.toPathData.betaAt g.kstar = 0 := by
    unfold SiteCost.PathData.siteCost at hM0
    constructor <;> omega
  by_cases hd : g.delta = true
  · have hbeta : g.toPathData.betaAt g.kstar = g.d g.kstar - g.eps := by
      unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
      simp [EltBridge.Elt.toPathData, hd]
    have halpha : g.toPathData.alphaAt g.kstar = g.d (g.kstar - 1) - SiteCost.vArr g.kstar := by
      unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
      simp [EltBridge.Elt.toPathData, hd]
    have hvarr : SiteCost.vArr g.kstar = 0 := by unfold SiteCost.vArr; simp [hk0]
    rw [hvarr] at halpha
    have hdk : g.d g.kstar = g.eps := by rw [hbeta] at halphabeta; omega
    have hdk1 : g.d (g.kstar - 1) = 0 := by rw [halpha] at halphabeta; omega
    refine ⟨?_, ?_⟩
    · have hmemocc : g.kstar ∈ occTrue g := by
        unfold occTrue
        by_cases hsup : g.kstar ∈ g.supp
        · exact Finset.mem_filter.mpr ⟨hsup, Or.inl (by rw [hdk]; rcases g.heps with he|he <;> omega)⟩
        · exact absurd (g.hsupp g.kstar hsup).1 (by rw [hdk]; rcases g.heps with he|he <;> omega)
      have hkmem : ATrue g ≤ g.kstar := ATrue_le hmemocc
      rcases eq_or_lt_of_le hkmem with heq | hlt
      · exfalso
        have hd0' : (s3 g).d g.kstar = 0 := by
          have hupd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
            rw [s3, dif_pos hd]
          rw [hupd]; simp [hdk]
        have hkS : (s3 g).kstar = g.kstar + 1 := by rw [s3, dif_pos hd]
        have ht0 : SiteCost.travel g.kstar g.kstar = -1 := by
          have hpar := g.hpar g.kstar
          rw [hdk] at hpar
          have heps := g.heps
          have htc := SiteCost.travel_cases g.kstar g.kstar
          have htne1 := travel_self_ne_one g.kstar
          rcases heps with he | he <;> omega
        have ht0' : SiteCost.travel (s3 g).kstar g.kstar = 0 := by
          rw [hkS, EltBridge.Elt.travel_succ_at, ht0]; ring
        have hnotmem : g.kstar ∉ occTrue (s3 g) := by
          unfold occTrue
          by_cases hsup : g.kstar ∈ (s3 g).supp
          · simp [Finset.mem_filter, hsup, hd0', ht0']
          · intro hc; exact hsup (Finset.mem_filter.mp hc).1
        have hAne : ATrue (s3 g) ≠ 0 := by rw [hA]; omega
        exact hnotmem (heq ▸ hA ▸ ATrue_mem_occTrue_of_ne_zero h2 hAne)
      · exact hlt
    · have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := kstar_mem_corrected_window g
      simp only [Finset.mem_Icc] at hkw
      rcases eq_or_lt_of_le hkw.2 with heq | hlt
      · exfalso
        have hgt : BTrue g < g.kstar := by omega
        have hz := d_eq_zero_of_gt_BTrue g (j := g.kstar) hgt
        have heps := g.heps
        rw [hdk] at hz
        rcases heps with he | he <;> omega
      · omega
  · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
    have h1' : ¬ (g.delta = true) := by rw [hd']; simp
    have halpha : g.toPathData.alphaAt g.kstar
        = g.d (g.kstar - 1) - SiteCost.vArr g.kstar + g.eps := by
      unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
      simp [EltBridge.Elt.toPathData, h1']
    have hvarr : SiteCost.vArr g.kstar = 0 := by unfold SiteCost.vArr; simp [hk0]
    rw [hvarr] at halpha
    have hdk1 : g.d (g.kstar - 1) = -g.eps := by rw [halpha] at halphabeta; omega
    refine ⟨?_, ?_⟩
    · have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := kstar_mem_corrected_window g
      simp only [Finset.mem_Icc] at hkw
      rcases eq_or_lt_of_le hkw.1 with heq | hlt
      · exfalso
        have hlt' : g.kstar - 1 < ATrue g := by omega
        have hz := d_eq_zero_of_lt_ATrue g (j := g.kstar - 1) hlt'
        have heps := g.heps
        rw [hdk1] at hz
        rcases heps with he | he <;> omega
      · omega
    · have hmemocc : g.kstar - 1 ∈ occTrue g := by
        unfold occTrue
        by_cases hsup : g.kstar - 1 ∈ g.supp
        · exact Finset.mem_filter.mpr ⟨hsup, Or.inl (by rw [hdk1]; rcases g.heps with he|he <;> omega)⟩
        · exact absurd (g.hsupp (g.kstar - 1) hsup).1 (by rw [hdk1]; rcases g.heps with he|he <;> omega)
      have hkmem : g.kstar - 1 ≤ BTrue g := le_BTrue hmemocc
      rcases eq_or_lt_of_le hkmem with heq | hlt
      · exfalso
        have hd0' : (s3 g).d (g.kstar - 1) = 0 := by
          have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
            rw [s3, dif_neg h1']
          rw [hupd]; simp [hdk1]
        have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
        have ht0 : SiteCost.travel g.kstar (g.kstar - 1) = 1 := by
          have hpar := g.hpar (g.kstar - 1)
          rw [hdk1] at hpar
          have heps := g.heps
          have htc := SiteCost.travel_cases g.kstar (g.kstar - 1)
          have htne := travel_pred_ne_neg_one g.kstar
          rcases heps with he | he <;> omega
        have ht0' : SiteCost.travel (s3 g).kstar (g.kstar - 1) = 0 := by
          rw [hkS, EltBridge.Elt.travel_pred_at, ht0]; ring
        have hnotmem : g.kstar - 1 ∉ occTrue (s3 g) := by
          unfold occTrue
          by_cases hsup : g.kstar - 1 ∈ (s3 g).supp
          · simp [Finset.mem_filter, hsup, hd0', ht0']
          · intro hc; exact hsup (Finset.mem_filter.mp hc).1
        have hBne : BTrue (s3 g) ≠ -1 := by rw [hB]; omega
        exact hnotmem (heq ▸ hB ▸ BTrue_mem_occTrue_of_ne_neg_one h2 hBne)
      · omega


theorem siteCost_s1_eq_one_of_zero (g : EltBridge.Elt) (hM0 : g.toPathData.siteCost g.kstar = 0) :
    (s1 g).toPathData.siteCost g.kstar = 1 := by
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have heps := g.heps
  have halphabeta : g.toPathData.alphaAt g.kstar = 0 ∧ g.toPathData.betaAt g.kstar = 0 := by
    unfold SiteCost.PathData.siteCost at hM0; constructor <;> omega
  unfold SiteCost.PathData.siteCost
  rw [ha1, hb1, halphabeta.1, halphabeta.2]
  rcases heps with he | he <;> simp [he] <;> split_ifs <;> omega

theorem siteCost_s2_eq_one_of_zero (g : EltBridge.Elt) (hM0 : g.toPathData.siteCost g.kstar = 0) :
    (s2 g).toPathData.siteCost g.kstar = 1 := by
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  have halphabeta : g.toPathData.alphaAt g.kstar = 0 ∧ g.toPathData.betaAt g.kstar = 0 := by
    unfold SiteCost.PathData.siteCost at hM0; constructor <;> omega
  unfold SiteCost.PathData.siteCost
  rw [ha2, hb2, halphabeta.1, halphabeta.2]
  rcases heps with he | he <;> simp [he] <;> split_ifs <;> omega

theorem descent_of_siteCost_zero_interior (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hM0 : g.toPathData.siteCost g.kstar = 0)
    (hint : g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    PhiZ (s1 g) < PhiZ g := by
  have hkIcc : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := by
    simp only [Finset.mem_Ioo] at hint
    simp only [Finset.mem_Icc]; omega
  have hs : ¬ ShieldFires g := not_shieldFires_of_interior g hint
  have hs' : ¬ ShieldFires (s1 g) := by
    have hk' : (s1 g).kstar ∈ Finset.Ioo (ATrue (s1 g)) (BTrue (s1 g) + 1) := by
      rw [ATrue_s1, BTrue_s1]; exact hint
    exact not_shieldFires_of_interior (s1 g) hk'
  have hmu : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ) + (((s1 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu, siteSum_sub_eq_at_kstar_s1 g hkIcc]; ring
  have hc : (cTrue (s1 g) : ℤ)
      = (cTrue g : ℤ)
        + ((if (s1 g).toPathData.cut g.kstar then (1 : ℤ) else 0)
            - (if g.toPathData.cut g.kstar then (1 : ℤ) else 0)) := by
    rw [cTrue_eq_filter_of_not_shield _ hs', cTrue_eq_filter_of_not_shield _ hs,
      ATrue_s1, BTrue_s1]
    refine filter_card_eq_add_diff hint (fun s _ hsne => ?_)
    rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
      siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hsne]
  have hsc1 := siteCost_s1_eq_one_of_zero g hM0
  have hcutg : g.toPathData.cut g.kstar := (cut_iff_siteCost_zero g.toPathData g.kstar).mpr hM0
  have hcuts1 : ¬ (s1 g).toPathData.cut g.kstar := fun hcc =>
    absurd ((cut_iff_siteCost_zero (s1 g).toPathData g.kstar).mp hcc) (by omega)
  unfold PhiZ
  rw [hlR, hc, if_pos hcutg, if_neg hcuts1, hsc1, hM0]
  push_cast
  omega

theorem descent_of_siteCost_zero_interior_s2 (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hM0 : g.toPathData.siteCost g.kstar = 0)
    (hint : g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    PhiZ (s2 g) < PhiZ g := by
  have hkIcc : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := by
    simp only [Finset.mem_Ioo] at hint
    simp only [Finset.mem_Icc]; omega
  have hs : ¬ ShieldFires g := not_shieldFires_of_interior g hint
  have hs' : ¬ ShieldFires (s2 g) := by
    have hk' : (s2 g).kstar ∈ Finset.Ioo (ATrue (s2 g)) (BTrue (s2 g) + 1) := by
      rw [ATrue_s2, BTrue_s2]; exact hint
    exact not_shieldFires_of_interior (s2 g) hk'
  have hmu : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)), ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ) + (((s2 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu, siteSum_sub_eq_at_kstar_s2 g hkIcc]; ring
  have hc : (cTrue (s2 g) : ℤ)
      = (cTrue g : ℤ)
        + ((if (s2 g).toPathData.cut g.kstar then (1 : ℤ) else 0)
            - (if g.toPathData.cut g.kstar then (1 : ℤ) else 0)) := by
    rw [cTrue_eq_filter_of_not_shield _ hs', cTrue_eq_filter_of_not_shield _ hs,
      ATrue_s2, BTrue_s2]
    refine filter_card_eq_add_diff hint (fun s _ hsne => ?_)
    rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
      siteCost_eq_of_ne_kstar (P := (s2 g).toPathData) (Q := g.toPathData) rfl rfl s hsne]
  have hsc1 := siteCost_s2_eq_one_of_zero g hM0
  have hcutg : g.toPathData.cut g.kstar := (cut_iff_siteCost_zero g.toPathData g.kstar).mpr hM0
  have hcuts2 : ¬ (s2 g).toPathData.cut g.kstar := fun hcc =>
    absurd ((cut_iff_siteCost_zero (s2 g).toPathData g.kstar).mp hcc) (by omega)
  unfold PhiZ
  rw [hlR, hc, if_pos hcutg, if_neg hcuts2, hsc1, hM0]
  push_cast
  omega


theorem exists_descent (g : EltBridge.Elt) (hk0 : g.kstar ≠ 0)
    (hne : ¬ EltBridge.Elt.SameElt g EltBridge.Elt.one) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g ∨ PhiZ (s3 g) < PhiZ g := by
  by_cases hcase : ∃ h1 : (occTrue g).Nonempty, ∃ h2 : (occTrue (s3 g)).Nonempty,
      ATrue (s3 g) = ATrue g ∧ BTrue (s3 g) = BTrue g ∧
      (lRTrue (s3 g) : ℤ) = lRTrue g + 1
  · obtain ⟨h1, h2, hA, hB, hlr⟩ := hcase
    have hasc := mu_ascent_of_lRTrue_ascent_window_unchanged g hA hB hlr
    by_cases hM : 0 < g.toPathData.siteCost g.kstar
    · by_cases hd : g.delta = true
      · rw [if_pos hd] at hasc
        rcases descent_of_ascent_true g hk0 hd hasc hM with hh | hh
        · left; exact hh
        · right; left; exact hh
      · have hd' : g.delta = false := by revert hd; cases g.delta <;> simp
        rw [if_neg (by rw [hd']; simp)] at hasc
        rcases descent_of_ascent_false g hk0 hd' hasc hM with hh | hh
        · left; exact hh
        · right; left; exact hh
    · have hM0 : g.toPathData.siteCost g.kstar = 0 := by omega
      have hint := kstar_interior_of_siteCost_zero_ascent g hk0 h1 h2 hA hB hM0
      have hintIoo : g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1) := by
        simp only [Finset.mem_Ioo]; omega
      left; exact descent_of_siteCost_zero_interior g hk0 hM0 hintIoo
  · push_neg at hcase
    exact exists_descent_of_not_window_unchanged_ascent g hne hk0
      (fun ⟨h1, h2, hA, hB, hlr⟩ => absurd hlr (by
        intro hlr'; exact absurd (hcase h1 h2 hA hB) (by simp [hlr'])))



theorem alphaAt_ge_two_of_ascent_false_kstar_zero (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hd : g.delta = false)
    (hasc : ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1) :
    g.toPathData.alphaAt g.kstar * g.eps ≥ 2 := by
  have hpar := g.hpar (g.kstar - 1)
  have h1' : ¬ (g.delta = true) := by rw [hd]; simp
  have hkS : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1']
  have hd1 : (s3 g).d (g.kstar - 1) = g.d (g.kstar - 1) + g.eps := by
    have hupd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
      rw [s3, dif_neg h1']
    rw [hupd]; simp
  have ht0 : SiteCost.travel g.kstar (g.kstar - 1) = 0 := by
    rw [hkz]; exact SiteCost.travel_of_kstar_zero (-1)
  have ht1 : SiteCost.travel (s3 g).kstar (g.kstar - 1) = SiteCost.travel g.kstar (g.kstar - 1) - 1 := by
    rw [hkS, EltBridge.Elt.travel_pred_at]
  rw [ht0] at hpar ht1
  have heps := g.heps
  have halpha : g.toPathData.alphaAt g.kstar
      = g.d (g.kstar - 1) - SiteCost.vArr g.kstar + g.eps := by
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
    simp [EltBridge.Elt.toPathData, h1']
  have hvarr : SiteCost.vArr g.kstar = 1 := by rw [hkz]; unfold SiteCost.vArr; simp
  rw [hvarr] at halpha
  unfold SiteCost.PathData.mu at hasc
  simp only [EltBridge.Elt.toPathData] at hasc
  rw [ht0] at hasc
  rw [halpha]
  split_ifs at hasc with hvac1 hvac2 hvac2 <;>
    rcases heps with he | he <;> simp only [he] at hasc hd1 ht1 hpar ⊢ <;> omega

theorem siteCost_descent_of_ascent_false_kstar_zero (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hd : g.delta = false)
    (hasc : ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1) :
    (s1 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar ∨
      (s2 g).toPathData.siteCost g.kstar < g.toPathData.siteCost g.kstar := by
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have heps := g.heps
  have hpar := alphaAt_betaAt_kstar_parity g
  have hge2 := alphaAt_ge_two_of_ascent_false_kstar_zero g hkz hd hasc
  unfold SiteCost.PathData.siteCost
  rcases heps with he | he <;>
    simp [hd, he] at ha1 hb1 ha2 hb2 hge2 hpar <;>
    rcases lt_trichotomy (g.toPathData.betaAt g.kstar) 0 with hb | hb | hb <;>
    first | (left; omega) | (right; omega)

theorem siteCost_ge_two_of_ascent_false_kstar_zero (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hd : g.delta = false)
    (hasc : ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1) :
    2 ≤ g.toPathData.siteCost g.kstar := by
  have hge2 := alphaAt_ge_two_of_ascent_false_kstar_zero g hkz hd hasc
  have heps := g.heps
  unfold SiteCost.PathData.siteCost
  rcases heps with he | he <;> simp [he] at hge2 ⊢ <;> omega

theorem descent_of_ascent_false_kstar_zero (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hd : g.delta = false)
    (hasc : ((s3 g).toPathData.mu (g.kstar - 1) : ℤ) = g.toPathData.mu (g.kstar - 1) + 1) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g := by
  have hcutg : ¬ g.toPathData.cut g.kstar := fun hcc =>
    absurd ((cut_iff_siteCost_zero g.toPathData g.kstar).mp hcc)
      (by have := siteCost_ge_two_of_ascent_false_kstar_zero g hkz hd hasc; omega)
  have hs1' : ¬ ShieldFires (s1 g) := by intro h; apply absurd h.2.1; rw [s1]; simp [hd]
  have hs2' : ¬ ShieldFires (s2 g) := by intro h; apply absurd h.2.1; rw [s2]; simp [hd]
  have hgcut : ¬ (ShieldFires g ∧ g.toPathData.cut g.kstar) := fun h => hcutg h.2
  have ha1 := alphaAt_s1_kstar g
  have hb1 := betaAt_s1_kstar g
  have ha2 := alphaAt_s2_kstar g
  have hb2 := betaAt_s2_kstar g
  have hsc1 : (s1 g).toPathData.siteCost g.kstar ≠ 0 := by
    have hge2 := alphaAt_ge_two_of_ascent_false_kstar_zero g hkz hd hasc
    have heps := g.heps
    unfold SiteCost.PathData.siteCost
    rcases heps with he | he <;> simp [hd, he] at ha1 hb1 hge2 <;> omega
  have hsc2 : (s2 g).toPathData.siteCost g.kstar ≠ 0 := by
    have hge2 := alphaAt_ge_two_of_ascent_false_kstar_zero g hkz hd hasc
    have heps := g.heps
    unfold SiteCost.PathData.siteCost
    rcases heps with he | he <;> simp [he] at ha2 hb2 hge2 <;> omega
  have hcuts1 : ¬ (s1 g).toPathData.cut g.kstar := fun hcc =>
    hsc1 ((cut_iff_siteCost_zero (s1 g).toPathData g.kstar).mp hcc)
  have hcuts2 : ¬ (s2 g).toPathData.cut g.kstar := fun hcc =>
    hsc2 ((cut_iff_siteCost_zero (s2 g).toPathData g.kstar).mp hcc)
  have hmu1 : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hmu2 : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)), ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := kstar_mem_corrected_window g
  have hlR1 : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ) + (((s1 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu1, siteSum_sub_eq_at_kstar_s1 g hkw]; ring
  have hlR2 : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ) + (((s2 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu2, siteSum_sub_eq_at_kstar_s2 g hkw]; ring
  have hc1 : cTrue (s1 g) = cTrue g := by
    rw [hkz] at hcutg hgcut hcuts1
    have hzcast : ((cTrue (s1 g) : ℤ)) = ((cTrue g : ℤ)) := by
      unfold cTrue
      rw [ATrue_s1, BTrue_s1, if_neg (fun h : ShieldFires (s1 g) ∧ (s1 g).toPathData.cut 0 => hs1' h.1),
        if_neg hgcut]
      have hfilt : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s1 g).toPathData.cut
          = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
        apply Finset.filter_congr
        intro s _
        by_cases hsk : s = g.kstar
        · subst hsk; rw [hkz]; simp [hcuts1, hcutg]
        · rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
            siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
      rw [hfilt]
    exact_mod_cast hzcast
  have hc2 : cTrue (s2 g) = cTrue g := by
    rw [hkz] at hcutg hgcut hcuts2
    have hzcast : ((cTrue (s2 g) : ℤ)) = ((cTrue g : ℤ)) := by
      unfold cTrue
      rw [ATrue_s2, BTrue_s2, if_neg (fun h : ShieldFires (s2 g) ∧ (s2 g).toPathData.cut 0 => hs2' h.1),
        if_neg hgcut]
      have hfilt : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s2 g).toPathData.cut
          = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
        apply Finset.filter_congr
        intro s _
        by_cases hsk : s = g.kstar
        · subst hsk; rw [hkz]; simp [hcuts2, hcutg]
        · rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
            siteCost_eq_of_ne_kstar (P := (s2 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
      rw [hfilt]
    exact_mod_cast hzcast
  rcases siteCost_descent_of_ascent_false_kstar_zero g hkz hd hasc with hs | hs
  · left; unfold PhiZ; rw [hlR1, hc1]; omega
  · right; unfold PhiZ; rw [hlR2, hc2]; omega


theorem descent_of_ascent_true_kstar_zero_pos (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hd : g.delta = true)
    (hasc : ((s3 g).toPathData.mu g.kstar : ℤ) = g.toPathData.mu g.kstar + 1)
    (hM : 0 < g.toPathData.siteCost g.kstar) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g := by
  have hcutg : ¬ g.toPathData.cut g.kstar := fun hcc =>
    absurd ((cut_iff_siteCost_zero g.toPathData g.kstar).mp hcc) (by omega)
  have hs0 : ¬ ShieldFires g := fun h => absurd hd (by rw [h.2.1]; simp)
  have hgcut : ¬ (ShieldFires g ∧ g.toPathData.cut g.kstar) := fun h => hs0 h.1
  have hne1 := betaAt_ne_pm_one_of_ascent_true g hd hasc
  have hpar := alphaAt_betaAt_kstar_parity g
  have hM0 : g.toPathData.siteCost g.kstar ≠ 1 := by
    unfold SiteCost.PathData.siteCost; omega
  have hM2 : 2 ≤ g.toPathData.siteCost g.kstar := by omega
  have hmu1 : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hmu2 : (∑ j ∈ Finset.Icc (ATrue (s2 g)) (BTrue (s2 g)), ((s2 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s2, BTrue_s2]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hkw : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := kstar_mem_corrected_window g
  have hlR1 : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ) + (((s1 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu1, siteSum_sub_eq_at_kstar_s1 g hkw]; ring
  have hlR2 : (lRTrue (s2 g) : ℤ)
      = (lRTrue g : ℤ) + (((s2 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu2, siteSum_sub_eq_at_kstar_s2 g hkw]; ring
  rcases siteCost_descent_of_ascent_true g hd hasc hM with hs | hs
  · obtain ⟨hb1, hb2⟩ := s1_siteCost_kstar g
    have hsc1 : (s1 g).toPathData.siteCost g.kstar ≠ 0 := by omega
    have hcuts1 : ¬ (s1 g).toPathData.cut g.kstar := fun hcc =>
      hsc1 ((cut_iff_siteCost_zero (s1 g).toPathData g.kstar).mp hcc)
    have hgcut1 : ¬ (ShieldFires (s1 g) ∧ (s1 g).toPathData.cut g.kstar) := fun h => hcuts1 h.2
    have hc1 : cTrue (s1 g) = cTrue g := by
      rw [hkz] at hcutg hgcut hgcut1 hcuts1
      have hzcast : ((cTrue (s1 g) : ℤ)) = ((cTrue g : ℤ)) := by
        unfold cTrue
        rw [ATrue_s1, BTrue_s1, if_neg hgcut1, if_neg hgcut]
        have hfilt : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s1 g).toPathData.cut
            = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
          apply Finset.filter_congr
          intro s _
          by_cases hsk : s = g.kstar
          · subst hsk; rw [hkz]; simp [hcuts1, hcutg]
          · rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
              siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
        rw [hfilt]
      exact_mod_cast hzcast
    left; unfold PhiZ; rw [hlR1, hc1]; omega
  · obtain ⟨hb1, hb2⟩ := s2_siteCost_kstar g
    have hsc2 : (s2 g).toPathData.siteCost g.kstar ≠ 0 := by omega
    have hcuts2 : ¬ (s2 g).toPathData.cut g.kstar := fun hcc =>
      hsc2 ((cut_iff_siteCost_zero (s2 g).toPathData g.kstar).mp hcc)
    have hgcut2 : ¬ (ShieldFires (s2 g) ∧ (s2 g).toPathData.cut g.kstar) := fun h => hcuts2 h.2
    have hc2 : cTrue (s2 g) = cTrue g := by
      rw [hkz] at hcutg hgcut hgcut2 hcuts2
      have hzcast : ((cTrue (s2 g) : ℤ)) = ((cTrue g : ℤ)) := by
        unfold cTrue
        rw [ATrue_s2, BTrue_s2, if_neg hgcut2, if_neg hgcut]
        have hfilt : (Finset.Ioo (ATrue g) (BTrue g + 1)).filter (s2 g).toPathData.cut
            = (Finset.Ioo (ATrue g) (BTrue g + 1)).filter g.toPathData.cut := by
          apply Finset.filter_congr
          intro s _
          by_cases hsk : s = g.kstar
          · subst hsk; rw [hkz]; simp [hcuts2, hcutg]
          · rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
              siteCost_eq_of_ne_kstar (P := (s2 g).toPathData) (Q := g.toPathData) rfl rfl s hsk]
        rw [hfilt]
      exact_mod_cast hzcast
    right; unfold PhiZ; rw [hlR2, hc2]; omega


theorem kstar_interior_of_siteCost_zero_ascent_true_kstar_zero (g : EltBridge.Elt)
    (hkz : g.kstar = 0) (hd : g.delta = true)
    (hM0 : g.toPathData.siteCost g.kstar = 0) :
    g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1) := by
  have halphabeta : g.toPathData.alphaAt g.kstar = 0 ∧ g.toPathData.betaAt g.kstar = 0 := by
    unfold SiteCost.PathData.siteCost at hM0
    constructor <;> omega
  have hbeta : g.toPathData.betaAt g.kstar = g.d g.kstar - g.eps := by
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR SiteCost.PathData.vD
    simp [EltBridge.Elt.toPathData, hd]
  have halpha : g.toPathData.alphaAt g.kstar = g.d (g.kstar - 1) - SiteCost.vArr g.kstar := by
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.PathData.vD
    simp [EltBridge.Elt.toPathData, hd]
  have hvarr : SiteCost.vArr g.kstar = 1 := by rw [hkz]; unfold SiteCost.vArr; simp
  rw [hvarr] at halpha
  have hdk : g.d g.kstar = g.eps := by rw [hbeta] at halphabeta; omega
  have hdk1 : g.d (g.kstar - 1) = 1 := by rw [halpha] at halphabeta; omega
  have hmemA : g.kstar - 1 ∈ occTrue g := by
    unfold occTrue
    by_cases hsup : g.kstar - 1 ∈ g.supp
    · exact Finset.mem_filter.mpr ⟨hsup, Or.inl (by rw [hdk1]; omega)⟩
    · exact absurd (g.hsupp (g.kstar - 1) hsup).1 (by rw [hdk1]; omega)
  have hmemB : g.kstar ∈ occTrue g := by
    unfold occTrue
    by_cases hsup : g.kstar ∈ g.supp
    · exact Finset.mem_filter.mpr ⟨hsup, Or.inl (by rw [hdk]; rcases g.heps with he|he <;> omega)⟩
    · exact absurd (g.hsupp g.kstar hsup).1 (by rw [hdk]; rcases g.heps with he|he <;> omega)
  have hA : ATrue g ≤ g.kstar - 1 := ATrue_le hmemA
  have hB : g.kstar ≤ BTrue g := le_BTrue hmemB
  simp only [Finset.mem_Ioo]
  omega

theorem descent_of_siteCost_zero_interior' (g : EltBridge.Elt)
    (hM0 : g.toPathData.siteCost g.kstar = 0)
    (hint : g.kstar ∈ Finset.Ioo (ATrue g) (BTrue g + 1)) :
    PhiZ (s1 g) < PhiZ g := by
  have hkIcc : g.kstar ∈ Finset.Icc (ATrue g) (BTrue g + 1) := by
    simp only [Finset.mem_Ioo] at hint
    simp only [Finset.mem_Icc]; omega
  have hs : ¬ ShieldFires g := not_shieldFires_of_interior g hint
  have hs' : ¬ ShieldFires (s1 g) := by
    have hk' : (s1 g).kstar ∈ Finset.Ioo (ATrue (s1 g)) (BTrue (s1 g) + 1) := by
      rw [ATrue_s1, BTrue_s1]; exact hint
    exact not_shieldFires_of_interior (s1 g) hk'
  have hmu : (∑ j ∈ Finset.Icc (ATrue (s1 g)) (BTrue (s1 g)), ((s1 g).toPathData.mu j : ℤ))
      = ∑ j ∈ Finset.Icc (ATrue g) (BTrue g), (g.toPathData.mu j : ℤ) := by
    rw [ATrue_s1, BTrue_s1]
    exact Finset.sum_congr rfl
      (fun j _ => by unfold SiteCost.PathData.mu; simp [EltBridge.Elt.toPathData])
  have hlR : (lRTrue (s1 g) : ℤ)
      = (lRTrue g : ℤ) + (((s1 g).toPathData.siteCost g.kstar : ℤ)
          - (g.toPathData.siteCost g.kstar : ℤ)) := by
    unfold lRTrue; push_cast
    rw [hmu, siteSum_sub_eq_at_kstar_s1 g hkIcc]; ring
  have hc : (cTrue (s1 g) : ℤ)
      = (cTrue g : ℤ)
        + ((if (s1 g).toPathData.cut g.kstar then (1 : ℤ) else 0)
            - (if g.toPathData.cut g.kstar then (1 : ℤ) else 0)) := by
    rw [cTrue_eq_filter_of_not_shield _ hs', cTrue_eq_filter_of_not_shield _ hs,
      ATrue_s1, BTrue_s1]
    refine filter_card_eq_add_diff hint (fun s _ hsne => ?_)
    rw [cut_iff_siteCost_zero, cut_iff_siteCost_zero,
      siteCost_eq_of_ne_kstar (P := (s1 g).toPathData) (Q := g.toPathData) rfl rfl s hsne]
  have hsc1 := siteCost_s1_eq_one_of_zero g hM0
  have hcutg : g.toPathData.cut g.kstar := (cut_iff_siteCost_zero g.toPathData g.kstar).mpr hM0
  have hcuts1 : ¬ (s1 g).toPathData.cut g.kstar := fun hcc =>
    absurd ((cut_iff_siteCost_zero (s1 g).toPathData g.kstar).mp hcc) (by omega)
  unfold PhiZ
  rw [hlR, hc, if_pos hcutg, if_neg hcuts1, hsc1, hM0]
  push_cast
  omega

theorem descent_of_ascent_true_kstar_zero (g : EltBridge.Elt) (hkz : g.kstar = 0)
    (hd : g.delta = true)
    (hasc : ((s3 g).toPathData.mu g.kstar : ℤ) = g.toPathData.mu g.kstar + 1) :
    PhiZ (s1 g) < PhiZ g ∨ PhiZ (s2 g) < PhiZ g := by
  by_cases hM : 0 < g.toPathData.siteCost g.kstar
  · exact descent_of_ascent_true_kstar_zero_pos g hkz hd hasc hM
  · have hM0 : g.toPathData.siteCost g.kstar = 0 := by omega
    have hint := kstar_interior_of_siteCost_zero_ascent_true_kstar_zero g hkz hd hM0
    left
    exact descent_of_siteCost_zero_interior' g hM0 hint

end PhiLipschitz
