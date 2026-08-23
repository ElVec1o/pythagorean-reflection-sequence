/-
Cost across the merge.

`EndData.transCost` sums `pcostF a (π a)` over *arrivals only*.  The re-pairing
changes the turn at the two arrivals `a, a'` and at the two departures `d, d'`, so
only the arrival terms are visible to the cost.

On arrivals the re-paired turn agrees with `swap d d' ∘ t`: both send `a ↦ d'` and
`a' ↦ d`, and away from the four ends neither moves anything, since `t x ∈ {d, d'}`
forces `x ∈ {a, a'}`.  They differ only at `d` and `d'` themselves, which are
departures.  So `EndData.transCost_swap_free` applies to the involutive re-pairing
even though `swapT ≠ swap ∘ t` as functions.
-/
import Mathlib.Tactic
import EndData
import WalkGraph
import ConfigMerge
import WalkSupport

namespace CostMerge

open WalkGraph

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The turn of a walk-graph datum as a permutation; it is its own inverse. -/
def turnPerm (D : Data α) : Equiv.Perm α :=
  ⟨D.t, D.t, fun x => D.t_invol x, fun x => D.t_invol x⟩

omit [Fintype α] [DecidableEq α] in
@[simp] theorem turnPerm_apply (D : Data α) (x : α) : turnPerm D x = D.t x := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem turnPerm_symm (D : Data α) (x : α) : (turnPerm D).symm x = D.t x := rfl

/-- The cost of a walk-graph datum against end data. -/
noncomputable def costOf (d : EndData.Data α) (D : Data α) : ℤ :=
  EndData.transCost d (turnPerm D)

omit [DecidableEq α] in
/-- **The cost sees only the turn's values at arrivals.** -/
theorem cost_congr (d : EndData.Data α) (D₁ D₂ : Data α)
    (h : ∀ a, d.isArr a = true → D₁.t a = D₂.t a) :
    costOf d D₁ = costOf d D₂ := by
  unfold costOf EndData.transCost
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_filter] at ha
  rw [turnPerm_apply, turnPerm_apply, h a ha.2]

omit [Fintype α] in
/-- **On arrivals, the re-paired turn is the transposition of the two departures.**
Away from the four ends nothing moves, because `t x ∈ {d, d'}` forces `x ∈ {a, a'}`. -/
theorem swapT_eq_on_arr (d : EndData.Data α) (t : α → α) (a a' : α)
    (hinv : ∀ x, t (t x) = x)
    (hd : d.isArr (t a) = false) (hd' : d.isArr (t a') = false)
    (x : α) (hx : d.isArr x = true) :
    swapT t a (t a) a' (t a') x = Equiv.swap (t a) (t a') (t x) := by
  have hxd : x ≠ t a := fun h => by rw [h, hd] at hx; exact Bool.noConfusion hx
  have hxd' : x ≠ t a' := fun h => by rw [h, hd'] at hx; exact Bool.noConfusion hx
  unfold swapT
  by_cases h1 : x = a
  · subst h1; rw [if_pos rfl, Equiv.swap_apply_left]
  by_cases h3 : x = a'
  · subst h3
    rw [if_neg h1, if_neg hxd', if_pos rfl, Equiv.swap_apply_right]
  rw [if_neg h1, if_neg hxd', if_neg h3, if_neg hxd]
  refine (Equiv.swap_apply_of_ne_of_ne ?_ ?_).symm
  · intro hc; exact h1 (by rw [← hinv x, hc, hinv])
  · intro hc; exact h3 (by rw [← hinv x, hc, hinv])

/-- **The merge is cost-neutral.**  The re-pairing of two arrivals sharing a side --
or whose departures share one -- leaves the transition cost unchanged.

This is `EndData.transCost_swap_free` transported along `swapT_eq_on_arr`: the cost
cannot tell the involutive re-pairing from the transposition of the two departures,
because they differ only at departures. -/
theorem cost_swapData (d : EndData.Data α) (D : Data α) (a a' : α)
    (harr : d.isArr a = true) (harr' : d.isArr a' = true)
    (hd : d.isArr (D.t a) = false) (hd' : d.isArr (D.t a') = false)
    (hne : a ≠ a')
    (hshared : d.side a = d.side a' ∨ d.side (D.t a) = d.side (D.t a'))
    (h1 h2 h3) :
    costOf d (swapData D a (D.t a) a' (D.t a') h1 h2 h3) = costOf d D := by
  have hsa : (turnPerm D).symm (D.t a) = a := by
    rw [turnPerm_symm, D.t_invol]
  have hsa' : (turnPerm D).symm (D.t a') = a' := by
    rw [turnPerm_symm, D.t_invol]
  have key : costOf d (swapData D a (D.t a) a' (D.t a') h1 h2 h3)
      = EndData.transCost d (Equiv.swap (D.t a) (D.t a') * turnPerm D) := by
    unfold costOf EndData.transCost
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_filter] at hx
    show EndData.pcostF d x (swapT D.t a (D.t a) a' (D.t a') x) = _
    rw [swapT_eq_on_arr d D.t a a' D.t_invol hd hd' x hx.2]
    rfl
  rw [key]
  exact EndData.transCost_swap_free d (turnPerm D) (D.t a) (D.t a') hd hd'
    (by rw [hsa]; exact harr) (by rw [hsa']; exact harr')
    (by rw [hsa, hsa']; exact hne)
    (by rw [hsa, hsa']; exact hshared)

/-! ### The cost-preserving descent

`cost_swapData` says the merge is free; `ConfigMerge.descent_of_split` says it lowers
the walk count.  Together they are the step the paper's argument runs inside the set
of cost-minimal realisations. -/

/-- **One step, free and strictly descending.** -/
theorem cost_preserving_step (d : EndData.Data α) (D : Data α) (a a' : α)
    (harr : d.isArr a = true) (harr' : d.isArr a' = true)
    (hd : d.isArr (D.t a) = false) (hd' : d.isArr (D.t a') = false)
    (hsplit : ¬ (graph D).Reachable a a')
    (hshared : d.side a = d.side a' ∨ d.side (D.t a) = d.side (D.t a'))
    (h1 h2 h3) :
    costOf d (swapData D a (D.t a) a' (D.t a') h1 h2 h3) = costOf d D ∧
      walkCount (swapData D a (D.t a) a' (D.t a') h1 h2 h3) < walkCount D :=
  ⟨cost_swapData d D a a' harr harr' hd hd'
     (Ne.symm (ConfigMerge.ne_of_split D hsplit)) hshared h1 h2 h3,
   ConfigMerge.descent_of_split D a a' hsplit h1 h2 h3⟩

/-- The property the numerics support and the descent needs: a cost-minimal datum
with more than one walk admits a **free** merge -- two arrivals at a common site, in
different walks, sharing a side or with their departures sharing one.

Verified over all cost-minimal transition systems on one to three edges: 146 of 146
multi-walk cases (`code/zeta_probe/tools/nogap/side_probe2.py`).  Not proved. -/
def HasFreePair (d : EndData.Data α) (siteOf : α → ℤ) (D : Data α) : Prop :=
  1 < walkCount D → ∃ a a' : α,
    siteOf a = siteOf a' ∧ d.isArr a = true ∧ d.isArr a' = true ∧
    d.isArr (D.t a) = false ∧ d.isArr (D.t a') = false ∧
    ¬ (graph D).Reachable a a' ∧
    (d.side a = d.side a' ∨ d.side (D.t a) = d.side (D.t a'))

/-- The invariant carried by the cost-preserving descent: the merge invariant, plus
a fixed cost. -/
def MergesCost (siteOf : α → ℤ) (isArr : α → Bool) (p₀ : α → α)
    (d : EndData.Data α) (c₀ : ℤ) (D : Data α) : Prop :=
  WalkSupport.Merges siteOf isArr p₀ D ∧ costOf d D = c₀

/-- **The cost-preserving merge loop.**  Given a free pair whenever more than one walk
remains, the walks merge to one **at unchanged cost**.

The free-pair hypothesis is `HasFreePair`, which the numerics support at cost-minimal
data and which is not proved here. -/
theorem cost_merges_to_one (siteOf : α → ℤ) (p₀ : α → α) (d : EndData.Data α) (c₀ : ℤ)
    (hp₀ : ∀ x, siteOf (p₀ x) ≠ siteOf x)
    (hfp : ∀ E : Data α, MergesCost siteOf d.isArr p₀ d c₀ E →
      HasFreePair d siteOf E)
    (D : Data α) (hD : MergesCost siteOf d.isArr p₀ d c₀ D) :
    ∃ D', MergesCost siteOf d.isArr p₀ d c₀ D' ∧ walkCount D' ≤ 1 := by
  classical
  refine ConfigMerge.reaches_one (P := MergesCost siteOf d.isArr p₀ d c₀) ?_ D hD
  intro E hmany hE
  obtain ⟨⟨hp, hts, hta⟩, hc⟩ := hE
  obtain ⟨a, a', hss, harr, harr', hd, hd', hsplit, hshared⟩ := hfp E ⟨⟨hp, hts, hta⟩, hc⟩ hmany
  have haa' : a' ≠ a := ConfigMerge.ne_of_split E hsplit
  have hsd : siteOf (E.t a) = siteOf a := hts a
  have hsa' : siteOf a' = siteOf a := hss.symm
  have hsd' : siteOf (E.t a') = siteOf a := by rw [hts a', hss]
  refine ⟨swapData E a (E.t a) a' (E.t a')
      (swapT_invol E.t_invol rfl rfl (ConfigMerge.dep_ne_arr' E rfl)
        (ConfigMerge.dep_ne_other E rfl hsplit) haa'
        (ConfigMerge.dep_ne_dep' E rfl rfl haa')
        (Ne.symm (ConfigMerge.dep_ne_arr' E rfl))
        (ConfigMerge.dep_ne_other' E rfl hsplit))
      (swapT_ne E.t a (E.t a) a' (E.t a') E.t_ne
        (ConfigMerge.dep_ne_other E rfl hsplit) (ConfigMerge.dep_ne_other' E rfl hsplit))
      (partner_ne_swapT siteOf E.p E.t a (E.t a) a' (E.t a')
        (by rw [hp]; exact hp₀) hts hsd hsa' hsd'),
    ⟨⟨hp, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact swapT_site siteOf E.t a (E.t a) a' (E.t a') hts hsd hsa' hsd'
  · exact swapT_arr d.isArr E.t a (E.t a) a' (E.t a') hta rfl rfl harr harr'
  · rw [cost_swapData d E a a' harr harr' hd hd' (Ne.symm haa') hshared]; exact hc
  · exact ConfigMerge.descent_of_split E a a' hsplit _ _ _

/-! ### What minimality does and does not force

For an arrival and its departure, `pcostF` is `2` when they share a side (always a
sign-flipped bounce) and `1` when they do not.  Write `sa, sa'` for the two arrivals'
sides and `da, da'` for their departures'.

A free merge needs `sa = sa'` or `da = da'`.  When it fails, both differ, and there
are exactly two sub-cases -- which behave **oppositely**. -/

/-- The cost of pairing an arrival of side `s` with a departure of side `t`. -/
def pairCost (s t : Bool) : ℤ := if s = t then 2 else 1

/-- **When the free condition fails and the arrival aligns with its own departure,
the cross-pairing is strictly cheaper.**  So such a configuration is not minimal. -/
theorem cross_cheaper : ∀ sa sa' da da' : Bool, sa ≠ sa' → da ≠ da' → sa = da →
    pairCost sa da' + pairCost sa' da < pairCost sa da + pairCost sa' da' := by decide

/-- **But in the other sub-case the cross-pairing is strictly dearer.**  Both arrivals
are passes, and exchanging their departures turns both into bounces.  So minimality
alone does not force a free pair *at a given site*: this configuration is locally
optimal and its cross merge costs `+2`. -/
theorem cross_dearer : ∀ sa sa' da da' : Bool, sa ≠ sa' → da ≠ da' → sa ≠ da →
    pairCost sa da + pairCost sa' da' < pairCost sa da' + pairCost sa' da := by decide

/-! ### The canonical form of the remaining gap

`WalkSupport.maximising_walk_all_bottom` proves that at `s*` the maximising walk is
all bottom ends.  What is left is that a *second* walk contributes a bottom
**arrival** there.  Stated as one Prop, it implies `HasFreePair` outright, because two
bottom ends share a side. -/

/-- The conjecture, in its canonical form: at `s*` two bottom arrivals lie in
different walks.  Verified 1114 of 1114 on at most four edges
(`code/zeta_probe/tools/nogap/maxwlo_probe.py`); not proved. -/
def CanonicalPair (d : EndData.Data α) (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (z₀ : α) (D : Data α) : Prop :=
  1 < walkCount D → ∃ a a' : α,
    siteOf a = WalkSupport.maxWLo edgeOf (graph D) z₀ ∧
    siteOf a' = WalkSupport.maxWLo edgeOf (graph D) z₀ ∧
    atTop a = false ∧ atTop a' = false ∧
    d.isArr a = true ∧ d.isArr a' = true ∧
    d.isArr (D.t a) = false ∧ d.isArr (D.t a') = false ∧
    ¬ (graph D).Reachable a a'

omit [DecidableEq α] in
/-- **The canonical form implies the free-pair hypothesis.**  Two bottom ends share a
side, which is exactly what the merge needs. -/
theorem hasFreePair_of_canonical (d : EndData.Data α) (edgeOf siteOf : α → ℤ)
    (atTop : α → Bool) (z₀ : α) (D : Data α)
    (hside : ∀ x, d.side x = atTop x)
    (h : CanonicalPair d edgeOf siteOf atTop z₀ D) :
    HasFreePair d siteOf D := by
  intro hmany
  obtain ⟨a, a', hsa, hsa', hba, hba', harr, harr', hd, hd', hsplit⟩ := h hmany
  exact ⟨a, a', by rw [hsa, hsa'], harr, harr', hd, hd', hsplit,
    Or.inl (by rw [hside, hside, hba, hba'])⟩

/-- **The exchange construction.**  If the two arrivals' sides differ, their
departures' sides differ, and an arrival aligns with its own departure, then the
re-pairing yields a transition system of *strictly smaller* cost.  So no cost-minimal
datum contains such a pattern.

This is `cost_swapData` with the strict inequality, transported along the same
observation: the cost cannot tell `swapT` from `swap (t a) (t a')` composed with `t`. -/
theorem cost_swapData_lt (d : EndData.Data α) (D : Data α) (a a' : α)
    (harr : d.isArr a = true) (harr' : d.isArr a' = true)
    (hd : d.isArr (D.t a) = false) (hd' : d.isArr (D.t a') = false)
    (hne : a ≠ a')
    (hs1 : d.side a ≠ d.side a')
    (hs2 : d.side (D.t a) ≠ d.side (D.t a'))
    (hs3 : d.side a = d.side (D.t a))
    (h1 h2 h3) :
    costOf d (swapData D a (D.t a) a' (D.t a') h1 h2 h3) < costOf d D := by
  have hsa : (turnPerm D).symm (D.t a) = a := by rw [turnPerm_symm, D.t_invol]
  have hsa' : (turnPerm D).symm (D.t a') = a' := by rw [turnPerm_symm, D.t_invol]
  have key : costOf d (swapData D a (D.t a) a' (D.t a') h1 h2 h3)
      = EndData.transCost d (Equiv.swap (D.t a) (D.t a') * turnPerm D) := by
    unfold costOf EndData.transCost
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_filter] at hx
    show EndData.pcostF d x (swapT D.t a (D.t a) a' (D.t a') x) = _
    rw [swapT_eq_on_arr d D.t a a' D.t_invol hd hd' x hx.2]
    rfl
  rw [key]
  exact EndData.transCost_swap_lt d (turnPerm D) (D.t a) (D.t a') hd hd'
    (by rw [hsa]; exact harr) (by rw [hsa']; exact harr')
    (by rw [hsa, hsa']; exact hne)
    (by rw [hsa, hsa']; exact hs1) hs2 (by rw [hsa]; exact hs3)

/-- **Minimality forces a free pair.**  Take the maximising walk's bottom arrival `a`
at its leftmost site -- whose departure is a bottom too -- and any arrival `a'` of
another walk at that same site.  Then the two share a side, or their departures do.

If neither held, the sides would differ, the departures' sides would differ, and `a`
would align with its own departure, so `cost_swapData_lt` would produce a strictly
cheaper system.  The one configuration `cross_dearer` allows is excluded by the
alignment, which `WalkSupport.maximiser_departure_bottom` supplies. -/
theorem free_pair_of_minimal (d : EndData.Data α) (atTop : α → Bool) (D : Data α)
    (a a' : α)
    (hside : ∀ x, d.side x = atTop x)
    (hab : atTop a = false) (hdb : atTop (D.t a) = false)
    (harr : d.isArr a = true) (harr' : d.isArr a' = true)
    (hd : d.isArr (D.t a) = false) (hd' : d.isArr (D.t a') = false)
    (hne : a ≠ a')
    (h1 h2 h3)
    (hmin : ¬ costOf d (swapData D a (D.t a) a' (D.t a') h1 h2 h3) < costOf d D) :
    d.side a = d.side a' ∨ d.side (D.t a) = d.side (D.t a') := by
  by_contra hc
  push Not at hc
  obtain ⟨hs1, hs2⟩ := hc
  exact hmin (cost_swapData_lt d D a a' harr harr' hd hd' hne hs1 hs2
    (by rw [hside, hside, hab, hdb]) h1 h2 h3)

/-- **`HasFreePair`, proved.**  A locally cost-minimal datum with more than one walk
admits a free merge.

Assembly: take the maximising walk `z`; `maximiser_has_bottom_arrival` gives a bottom
arrival `a` at its leftmost site, and `maximiser_departure_bottom` makes its departure
a bottom too.  `exists_other_walk` and `other_end_at_wLo` put another walk's end at
that same site, and `walk_has_arrival_at_site` upgrades it to an arrival `a'`.
`free_pair_of_minimal` then forces `a` and `a'` to share a side, or their departures
to. -/
theorem hasFreePair_of_minimal (d : EndData.Data α) (edgeOf siteOf : α → ℤ)
    (atTop : α → Bool) (D : Data α)
    (hside : ∀ x, d.side x = atTop x)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, d.isArr (D.t e) = !d.isArr e)
    (hpsite : ∀ x, siteOf (D.p x) ≠ siteOf x)
    (z : α)
    (hzmax : ∀ w : α, WalkSupport.wLo edgeOf (graph D) w ≤ WalkSupport.wLo edgeOf (graph D) z)
    (hcov : ∀ v : α, edgeOf v < WalkSupport.wLo edgeOf (graph D) z →
      ∃ y : α, edgeOf y = WalkSupport.wLo edgeOf (graph D) z - 1 ∧ atTop y = true)
    (hmin : ∀ (b b' : α), siteOf b = siteOf b' →
      d.isArr b = true → d.isArr b' = true → ∀ h1 h2 h3,
      ¬ costOf d (swapData D b (D.t b) b' (D.t b') h1 h2 h3) < costOf d D) :
    HasFreePair d siteOf D := by
  intro hmany
  obtain ⟨a, hza, hasite, hab, haarr⟩ :=
    WalkSupport.maximiser_has_bottom_arrival edgeOf siteOf atTop d.isArr D
      hsite hpe hpt hts hta z
  obtain ⟨z', hzz'⟩ := ConfigMerge.exists_other_walk D hmany z
  obtain ⟨y, hys, hyn⟩ :=
    WalkSupport.other_end_at_wLo edgeOf siteOf atTop D hsite hpe hpt z z' hcov hzz' (hzmax z')
  obtain ⟨a', hya', ha'site, ha'arr⟩ :=
    WalkSupport.walk_has_arrival_at_site siteOf d.isArr D hts hta y y
      (SimpleGraph.Reachable.refl _) _ hys
  have hna' : ¬ (graph D).Reachable z a' := fun hc => hyn (hc.trans hya'.symm)
  have hne : a ≠ a' := fun h => hna' (h ▸ hza)
  have hdb : atTop (D.t a) = false :=
    WalkSupport.maximiser_departure_bottom edgeOf siteOf atTop D hsite hts z a hza hasite
  have hda : d.isArr (D.t a) = false := by rw [hta, haarr]; rfl
  have hda' : d.isArr (D.t a') = false := by rw [hta, ha'arr]; rfl
  have hsplit : ¬ (graph D).Reachable a a' := fun hc => hna' (hza.trans hc)
  have hss : siteOf a' = siteOf a := by rw [hasite, ha'site]
  have h1 := swapT_invol D.t_invol (rfl : D.t a = D.t a) (rfl : D.t a' = D.t a')
    (ConfigMerge.dep_ne_arr' D rfl) (ConfigMerge.dep_ne_other D rfl hsplit)
    (ConfigMerge.ne_of_split D hsplit)
    (ConfigMerge.dep_ne_dep' D rfl rfl (ConfigMerge.ne_of_split D hsplit))
    (Ne.symm (ConfigMerge.dep_ne_arr' D rfl)) (ConfigMerge.dep_ne_other' D rfl hsplit)
  have h2 := swapT_ne D.t a (D.t a) a' (D.t a') D.t_ne
    (ConfigMerge.dep_ne_other D rfl hsplit) (ConfigMerge.dep_ne_other' D rfl hsplit)
  have h3 := partner_ne_swapT siteOf D.p D.t a (D.t a) a' (D.t a')
    hpsite hts (hts a) hss (by rw [hts a', hss])
  exact ⟨a, a', hss.symm, haarr, ha'arr, hda, hda', hsplit,
    free_pair_of_minimal d atTop D a a' hside hab hdb haarr ha'arr hda hda' hne
      h1 h2 h3 (hmin a a' hss.symm haarr ha'arr h1 h2 h3)⟩

/-! ### Global minimality, which the descent preserves

Local minimality is awkward to carry: the merge could in principle open up a cheaper
re-pairing that was unavailable before.  Global minimality does not have that problem
-- the merge stays inside the class and preserves the cost, so a minimum stays a
minimum. -/

/-- The merge invariant, together with being cost-minimal in the class. -/
def MergesMin (siteOf : α → ℤ) (isArr : α → Bool) (p₀ : α → α)
    (d : EndData.Data α) (E : Data α) : Prop :=
  WalkSupport.Merges siteOf isArr p₀ E ∧
    ∀ F : Data α, WalkSupport.Merges siteOf isArr p₀ F → costOf d E ≤ costOf d F

/-- **A merge of two arrivals at one site stays in the class.** -/
theorem merges_swapData (siteOf : α → ℤ) (p₀ : α → α) (d : EndData.Data α)
    (E : Data α) (hE : WalkSupport.Merges siteOf d.isArr p₀ E)
    (b b' : α) (hss : siteOf b = siteOf b')
    (hb : d.isArr b = true) (hb' : d.isArr b' = true) (h1 h2 h3) :
    WalkSupport.Merges siteOf d.isArr p₀ (swapData E b (E.t b) b' (E.t b') h1 h2 h3) := by
  obtain ⟨hp, hts, hta⟩ := hE
  refine ⟨hp, ?_, ?_⟩
  · exact swapT_site siteOf E.t b (E.t b) b' (E.t b') hts (hts b) hss.symm
      (by rw [hts b', hss])
  · exact swapT_arr d.isArr E.t b (E.t b) b' (E.t b') hta rfl rfl hb hb'

/-- **Global minimality supplies the hypothesis.** -/
theorem hmin_of_mergesMin (siteOf : α → ℤ) (p₀ : α → α) (d : EndData.Data α)
    (E : Data α) (hE : MergesMin siteOf d.isArr p₀ d E) :
    ∀ (b b' : α), siteOf b = siteOf b' →
      d.isArr b = true → d.isArr b' = true → ∀ h1 h2 h3,
      ¬ costOf d (swapData E b (E.t b) b' (E.t b') h1 h2 h3) < costOf d E := by
  intro b b' hss hb hb' h1 h2 h3
  exact not_lt.mpr (hE.2 _ (merges_swapData siteOf p₀ d E hE.1 b b' hss hb hb' h1 h2 h3))

/-- **The cost-minimal merge loop, unconditional.**  A cost-minimal datum merges down
to a single walk, staying cost-minimal throughout.  No free-pair hypothesis: it is
supplied at each step by `hasFreePair_of_minimal`. -/
theorem min_merges_to_one (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (p₀ : α → α)
    (d : EndData.Data α)
    (hside : ∀ x, d.side x = atTop x)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (p₀ x) = edgeOf x)
    (hpt : ∀ x, atTop (p₀ x) = !atTop x)
    (hcov0 : ∀ j : ℤ, (∃ u : α, edgeOf u = j) → (∃ v : α, edgeOf v < j) →
      ∃ y : α, edgeOf y = j - 1 ∧ atTop y = true)
    (z₀ : α)
    (D : Data α) (hD : MergesMin siteOf d.isArr p₀ d D) :
    ∃ D', MergesMin siteOf d.isArr p₀ d D' ∧ walkCount D' ≤ 1 := by
  classical
  refine ConfigMerge.reaches_one (P := MergesMin siteOf d.isArr p₀ d) ?_ D hD
  intro E hmany hE
  obtain ⟨⟨hp, hts, hta⟩, hmin⟩ := hE
  obtain ⟨⟨z, hz⟩, hzle⟩ := WalkSupport.maxWLo_spec edgeOf (graph E) z₀
  have hzmax : ∀ w : α, WalkSupport.wLo edgeOf (graph E) w
      ≤ WalkSupport.wLo edgeOf (graph E) z := fun w => by rw [hz]; exact hzle w
  have hcov : ∀ v : α, edgeOf v < WalkSupport.wLo edgeOf (graph E) z →
      ∃ y : α, edgeOf y = WalkSupport.wLo edgeOf (graph E) z - 1 ∧ atTop y = true := by
    intro v hv
    obtain ⟨u, _, hue⟩ := WalkSupport.exists_end_at_wLo edgeOf (graph E) z
    exact hcov0 _ ⟨u, hue⟩ ⟨v, hv⟩
  have hpsite : ∀ x, siteOf (E.p x) ≠ siteOf x := by
    rw [hp]; exact WalkSupport.p_site_ne edgeOf siteOf atTop p₀ hsite hpe hpt
  obtain ⟨a, a', hss, harr, harr', hd, hd', hsplit, hshared⟩ :=
    hasFreePair_of_minimal d edgeOf siteOf atTop E hside hsite
      (by rw [hp]; exact hpe) (by rw [hp]; exact hpt) hts hta hpsite z hzmax hcov
      (hmin_of_mergesMin siteOf p₀ d E ⟨⟨hp, hts, hta⟩, hmin⟩) hmany
  have haa' : a' ≠ a := ConfigMerge.ne_of_split E hsplit
  have h1 := swapT_invol E.t_invol (rfl : E.t a = E.t a) (rfl : E.t a' = E.t a')
    (ConfigMerge.dep_ne_arr' E rfl) (ConfigMerge.dep_ne_other E rfl hsplit) haa'
    (ConfigMerge.dep_ne_dep' E rfl rfl haa')
    (Ne.symm (ConfigMerge.dep_ne_arr' E rfl)) (ConfigMerge.dep_ne_other' E rfl hsplit)
  have h2 := swapT_ne E.t a (E.t a) a' (E.t a') E.t_ne
    (ConfigMerge.dep_ne_other E rfl hsplit) (ConfigMerge.dep_ne_other' E rfl hsplit)
  have h3 := partner_ne_swapT siteOf E.p E.t a (E.t a) a' (E.t a')
    hpsite hts (hts a) hss.symm (by rw [hts a', hss])
  have hcost : costOf d (swapData E a (E.t a) a' (E.t a') h1 h2 h3) = costOf d E :=
    cost_swapData d E a a' harr harr' hd hd' (Ne.symm haa') hshared h1 h2 h3
  refine ⟨swapData E a (E.t a) a' (E.t a') h1 h2 h3,
    ⟨merges_swapData siteOf p₀ d E ⟨hp, hts, hta⟩ a a' hss harr harr' h1 h2 h3,
     fun F hF => by rw [hcost]; exact hmin F hF⟩,
    ConfigMerge.descent_of_split E a a' hsplit h1 h2 h3⟩

/-! ### A minimum exists

The class is not obviously finite -- `Data α` bundles proofs -- but the costs are
non-negative integers, so the set of achievable costs has a least element and any
datum attaining it is minimal. -/

omit [Fintype α] [DecidableEq α] in
theorem pcostF_nonneg (d : EndData.Data α) (a b : α) : 0 ≤ EndData.pcostF d a b := by
  unfold EndData.pcostF
  split <;> [split; skip] <;> norm_num

omit [DecidableEq α] in
theorem costOf_nonneg (d : EndData.Data α) (D : Data α) : 0 ≤ costOf d D :=
  Finset.sum_nonneg (fun a _ => pcostF_nonneg d a _)

/-- **A cost-minimal datum exists in the class**, given any datum in it. -/
theorem exists_mergesMin (siteOf : α → ℤ) (p₀ : α → α) (d : EndData.Data α)
    (D : Data α) (hD : WalkSupport.Merges siteOf d.isArr p₀ D) :
    ∃ E, MergesMin siteOf d.isArr p₀ d E := by
  classical
  obtain ⟨c, ⟨E, hE, hEc⟩, hleast⟩ :=
    Int.exists_least_of_bdd (P := fun c => ∃ F, WalkSupport.Merges siteOf d.isArr p₀ F ∧
        costOf d F = c)
      ⟨0, fun z hz => by obtain ⟨F, _, hF⟩ := hz; rw [← hF]; exact costOf_nonneg d F⟩
      ⟨costOf d D, D, hD, rfl⟩
  exact ⟨E, hE, fun F hF => by rw [hEc]; exact hleast _ ⟨F, hF, rfl⟩⟩

/-! ### The cost splits over sites

`costOf` sums `pcostF a (t a)` over the arrivals, and every arrival lies at exactly
one site, so the sum splits site by site.  That is what makes site-wise minimality
follow from global minimality: a re-pairing at one site changes only that site's
summand. -/

omit [DecidableEq α] in
/-- **The cost is the sum of its site contributions.** -/
theorem cost_split_by_site (d : EndData.Data α) (D : Data α) (siteOf : α → ℤ)
    (S : Finset ℤ) (hall : ∀ a, d.isArr a = true → siteOf a ∈ S) :
    costOf d D
      = ∑ s ∈ S, ∑ a ∈ (Finset.univ.filter (fun a => d.isArr a = true)).filter
          (fun a => siteOf a = s), EndData.pcostF d a (D.t a) := by
  classical
  unfold costOf EndData.transCost
  refine (Finset.sum_fiberwise_of_maps_to (fun a ha => ?_) _).symm
  rw [Finset.mem_filter] at ha
  exact hall a ha.2

omit [DecidableEq α] in
/-- **Site-wise minimality follows from global minimality.**  If two data agree away
from one site, their costs differ only in that site's summand, so a globally minimal
datum minimises each site. -/
theorem site_cost_le_of_global (d : EndData.Data α) (D E : Data α) (siteOf : α → ℤ)
    (s : ℤ) (hagree : ∀ a, d.isArr a = true → siteOf a ≠ s → D.t a = E.t a)
    (hmin : costOf d D ≤ costOf d E)
    (S : Finset ℤ) (hall : ∀ a, d.isArr a = true → siteOf a ∈ S) (hs : s ∈ S) :
    ∑ a ∈ (Finset.univ.filter (fun a => d.isArr a = true)).filter (fun a => siteOf a = s),
        EndData.pcostF d a (D.t a)
      ≤ ∑ a ∈ (Finset.univ.filter (fun a => d.isArr a = true)).filter
          (fun a => siteOf a = s), EndData.pcostF d a (E.t a) := by
  classical
  rw [cost_split_by_site d D siteOf S hall, cost_split_by_site d E siteOf S hall] at hmin
  have hoff : ∀ t ∈ S, t ≠ s →
      ∑ a ∈ (Finset.univ.filter (fun a => d.isArr a = true)).filter (fun a => siteOf a = t),
          EndData.pcostF d a (D.t a)
        = ∑ a ∈ (Finset.univ.filter (fun a => d.isArr a = true)).filter
            (fun a => siteOf a = t), EndData.pcostF d a (E.t a) := by
    intro t _ hts
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter, Finset.mem_filter] at ha
    rw [hagree a ha.1.2 (by rw [ha.2]; exact hts)]
  rw [← Finset.add_sum_erase _ _ hs, ← Finset.add_sum_erase _ _ hs] at hmin
  have := Finset.sum_congr rfl (fun t ht =>
    hoff t (Finset.mem_of_mem_erase ht) (Finset.ne_of_mem_erase ht))
  omega

/-! ### The free pair, from a given split

`hasFreePair_of_minimal` finds the second walk with `exists_other_walk`, which picks an
arbitrary one.  For the run induction the second walk is *given* -- separation failure
names two ends of the same run that are unreachable -- so the core is extracted here
with that end as input. -/

/-- **A free pair from a given split.**  Same as `hasFreePair_of_minimal` but with the
second walk supplied rather than found, so it can be chosen inside a run. -/
theorem freePair_of_split (d : EndData.Data α) (edgeOf siteOf : α → ℤ)
    (atTop : α → Bool) (D : Data α)
    (hside : ∀ x, d.side x = atTop x)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, d.isArr (D.t e) = !d.isArr e)
    (hpsite : ∀ x, siteOf (D.p x) ≠ siteOf x)
    (z z' : α)
    (hzz' : ¬ (graph D).Reachable z z')
    (hle : WalkSupport.wLo edgeOf (graph D) z' ≤ WalkSupport.wLo edgeOf (graph D) z)
    (hcov : ∀ v : α, edgeOf v < WalkSupport.wLo edgeOf (graph D) z →
      ∃ y : α, edgeOf y = WalkSupport.wLo edgeOf (graph D) z - 1 ∧ atTop y = true)
    (hmin : ∀ (b b' : α), siteOf b = siteOf b' →
      d.isArr b = true → d.isArr b' = true → ∀ h1 h2 h3,
      ¬ costOf d (swapData D b (D.t b) b' (D.t b') h1 h2 h3) < costOf d D) :
    ∃ a a' : α,
      siteOf a = siteOf a' ∧ d.isArr a = true ∧ d.isArr a' = true ∧
      d.isArr (D.t a) = false ∧ d.isArr (D.t a') = false ∧
      ¬ (graph D).Reachable a a' ∧
      (d.side a = d.side a' ∨ d.side (D.t a) = d.side (D.t a')) := by
  obtain ⟨a, hza, hasite, hab, haarr⟩ :=
    WalkSupport.maximiser_has_bottom_arrival edgeOf siteOf atTop d.isArr D
      hsite hpe hpt hts hta z
  obtain ⟨y, hys, hyn⟩ :=
    WalkSupport.other_end_at_wLo edgeOf siteOf atTop D hsite hpe hpt z z' hcov hzz' hle
  obtain ⟨a', hya', ha'site, ha'arr⟩ :=
    WalkSupport.walk_has_arrival_at_site siteOf d.isArr D hts hta y y
      (SimpleGraph.Reachable.refl _) _ hys
  have hna' : ¬ (graph D).Reachable z a' := fun hc => hyn (hc.trans hya'.symm)
  have hne : a ≠ a' := fun h => hna' (h ▸ hza)
  have hdb : atTop (D.t a) = false :=
    WalkSupport.maximiser_departure_bottom edgeOf siteOf atTop D hsite hts z a hza hasite
  have hda : d.isArr (D.t a) = false := by rw [hta, haarr]; rfl
  have hda' : d.isArr (D.t a') = false := by rw [hta, ha'arr]; rfl
  have hsplit : ¬ (graph D).Reachable a a' := fun hc => hna' (hza.trans hc)
  have hss : siteOf a' = siteOf a := by rw [hasite, ha'site]
  have h1 := swapT_invol D.t_invol (rfl : D.t a = D.t a) (rfl : D.t a' = D.t a')
    (ConfigMerge.dep_ne_arr' D rfl) (ConfigMerge.dep_ne_other D rfl hsplit)
    (ConfigMerge.ne_of_split D hsplit)
    (ConfigMerge.dep_ne_dep' D rfl rfl (ConfigMerge.ne_of_split D hsplit))
    (Ne.symm (ConfigMerge.dep_ne_arr' D rfl)) (ConfigMerge.dep_ne_other' D rfl hsplit)
  have h2 := swapT_ne D.t a (D.t a) a' (D.t a') D.t_ne
    (ConfigMerge.dep_ne_other D rfl hsplit) (ConfigMerge.dep_ne_other' D rfl hsplit)
  have h3 := partner_ne_swapT siteOf D.p D.t a (D.t a) a' (D.t a')
    hpsite hts (hts a) hss (by rw [hts a', hss])
  exact ⟨a, a', hss.symm, haarr, ha'arr, hda, hda', hsplit,
    free_pair_of_minimal d atTop D a a' hside hab hdb haarr ha'arr hda hda' hne
      h1 h2 h3 (hmin a a' hss.symm haarr ha'arr h1 h2 h3)⟩

/-- **Order a split by leftmost edge.**  `freePair_of_split` wants the first end to be
the one with the larger `wLo`; either order of a split will do, so pick that one. -/
theorem order_split {α : Type*} [DecidableEq α] [Fintype α]
    (D : Data α) (edgeOf : α → ℤ) (x y : α)
    (hnr : ¬ (graph D).Reachable x y) :
    ∃ z z' : α, ¬ (graph D).Reachable z z' ∧
      WalkSupport.wLo edgeOf (graph D) z' ≤ WalkSupport.wLo edgeOf (graph D) z := by
  rcases le_total (WalkSupport.wLo edgeOf (graph D) y)
    (WalkSupport.wLo edgeOf (graph D) x) with h | h
  · exact ⟨x, y, hnr, h⟩
  · exact ⟨y, x, fun hc => hnr hc.symm, h⟩

/-- **A split yields a strictly descending merge.**  Order the split, take the free
pair, and merge: the walk count drops.

The covering hypothesis is stated for every end, which the run descent supplies
because every walk of the run has its leftmost edge inside the run. -/
theorem step_of_split (d : EndData.Data α) (edgeOf siteOf : α → ℤ)
    (atTop : α → Bool) (D : Data α)
    (hside : ∀ x, d.side x = atTop x)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, d.isArr (D.t e) = !d.isArr e)
    (hpsite : ∀ x, siteOf (D.p x) ≠ siteOf x)
    (hcov : ∀ z v : α, edgeOf v < WalkSupport.wLo edgeOf (graph D) z →
      ∃ w : α, edgeOf w = WalkSupport.wLo edgeOf (graph D) z - 1 ∧ atTop w = true)
    (hmin : ∀ (b b' : α), siteOf b = siteOf b' →
      d.isArr b = true → d.isArr b' = true → ∀ h1 h2 h3,
      ¬ costOf d (swapData D b (D.t b) b' (D.t b') h1 h2 h3) < costOf d D)
    (x y : α) (hnr : ¬ (graph D).Reachable x y) :
    ∃ D' : Data α, walkCount D' < walkCount D := by
  obtain ⟨z, z', hzz', hle⟩ := order_split D edgeOf x y hnr
  obtain ⟨a, a', hss, harr, harr', hd, hd', hsplit, hshared⟩ :=
    freePair_of_split d edgeOf siteOf atTop D hside hsite hpe hpt hts hta hpsite
      z z' hzz' hle (hcov z) hmin
  have haa' : a' ≠ a := ConfigMerge.ne_of_split D hsplit
  have h1 := swapT_invol D.t_invol (rfl : D.t a = D.t a) (rfl : D.t a' = D.t a')
    (ConfigMerge.dep_ne_arr' D rfl) (ConfigMerge.dep_ne_other D rfl hsplit) haa'
    (ConfigMerge.dep_ne_dep' D rfl rfl haa')
    (Ne.symm (ConfigMerge.dep_ne_arr' D rfl)) (ConfigMerge.dep_ne_other' D rfl hsplit)
  have h2 := swapT_ne D.t a (D.t a) a' (D.t a') D.t_ne
    (ConfigMerge.dep_ne_other D rfl hsplit) (ConfigMerge.dep_ne_other' D rfl hsplit)
  have h3 := partner_ne_swapT siteOf D.p D.t a (D.t a) a' (D.t a')
    hpsite hts (hts a) hss.symm (by rw [hts a', hss])
  exact ⟨_, ConfigMerge.descent_of_split D a a' hsplit h1 h2 h3⟩

/-- **The descending merge, with what the invariant needs.**  Same as
`step_of_split`, but returning the merged datum together with the two arrivals and the
equation `D'.t = swapT …`.  That is enough for `ConfigLoop.hturn_swapT` to carry the
cut condition across the step, and it avoids the dependent binders that made the
side conditions unusable inside an existential. -/
theorem step_of_split' (d : EndData.Data α) (edgeOf siteOf : α → ℤ)
    (atTop : α → Bool) (D : Data α)
    (hside : ∀ x, d.side x = atTop x)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, d.isArr (D.t e) = !d.isArr e)
    (hpsite : ∀ x, siteOf (D.p x) ≠ siteOf x)
    (hcov : ∀ z v : α, edgeOf v < WalkSupport.wLo edgeOf (graph D) z →
      ∃ w : α, edgeOf w = WalkSupport.wLo edgeOf (graph D) z - 1 ∧ atTop w = true)
    (hmin : ∀ (b b' : α), siteOf b = siteOf b' →
      d.isArr b = true → d.isArr b' = true → ∀ h1 h2 h3,
      ¬ costOf d (swapData D b (D.t b) b' (D.t b') h1 h2 h3) < costOf d D)
    (x y : α) (hnr : ¬ (graph D).Reachable x y) :
    ∃ D' : Data α, walkCount D' < walkCount D ∧ D'.p = D.p ∧
      ∃ a a' : α, d.isArr a = true ∧ d.isArr a' = true ∧ siteOf a' = siteOf a ∧
        ¬ (graph D).Reachable a a' ∧
        (d.side a = d.side a' ∨ d.side (D.t a) = d.side (D.t a')) ∧
        D'.t = swapT D.t a (D.t a) a' (D.t a') := by
  obtain ⟨z, z', hzz', hle⟩ := order_split D edgeOf x y hnr
  obtain ⟨a, a', hss, harr, harr', hd, hd', hsplit, hshared⟩ :=
    freePair_of_split d edgeOf siteOf atTop D hside hsite hpe hpt hts hta hpsite
      z z' hzz' hle (hcov z) hmin
  have haa' : a' ≠ a := ConfigMerge.ne_of_split D hsplit
  have h1 := swapT_invol D.t_invol (rfl : D.t a = D.t a) (rfl : D.t a' = D.t a')
    (ConfigMerge.dep_ne_arr' D rfl) (ConfigMerge.dep_ne_other D rfl hsplit) haa'
    (ConfigMerge.dep_ne_dep' D rfl rfl haa')
    (Ne.symm (ConfigMerge.dep_ne_arr' D rfl)) (ConfigMerge.dep_ne_other' D rfl hsplit)
  have h2 := swapT_ne D.t a (D.t a) a' (D.t a') D.t_ne
    (ConfigMerge.dep_ne_other D rfl hsplit) (ConfigMerge.dep_ne_other' D rfl hsplit)
  have h3 := partner_ne_swapT siteOf D.p D.t a (D.t a) a' (D.t a')
    hpsite hts (hts a) hss.symm (by rw [hts a', hss])
  exact ⟨swapData D a (D.t a) a' (D.t a') h1 h2 h3,
    ConfigMerge.descent_of_split D a a' hsplit h1 h2 h3, rfl,
    a, a', harr, harr', hss.symm, hsplit, hshared, rfl⟩

-- Certification (Rule 5).
#print axioms CostMerge.step_of_split'
