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

end PhiLipschitz

#print axioms PhiLipschitz.sum_eq_add_diff_of_eq_off
#print axioms PhiLipschitz.siteSum_sub_eq_at_kstar_s1
#print axioms PhiLipschitz.siteSum_sub_eq_at_kstar_s2
#print axioms PhiLipschitz.siteSum_dist_le_one_s1
#print axioms PhiLipschitz.cut_iff_siteCost_zero
#print axioms PhiLipschitz.filter_cut_eq_filter_siteCost_zero
#print axioms PhiLipschitz.exchange_le_one
#print axioms PhiLipschitz.exchange_sq_le_one
