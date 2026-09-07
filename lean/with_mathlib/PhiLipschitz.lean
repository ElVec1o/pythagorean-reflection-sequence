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

end PhiLipschitz

#print axioms PhiLipschitz.sum_eq_add_diff_of_eq_off
#print axioms PhiLipschitz.siteSum_sub_eq_at_kstar_s1
#print axioms PhiLipschitz.siteSum_sub_eq_at_kstar_s2
#print axioms PhiLipschitz.siteSum_dist_le_one_s1
