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

-- Certification (Rule 5).
#print axioms CostMerge.hasFreePair_of_canonical
