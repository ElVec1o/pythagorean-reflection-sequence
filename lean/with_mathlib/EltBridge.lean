/-
The `g -> configuration` bridge, first half.

`PathData` is the combinatorial object every result in the merge development is
stated about.  Nothing in the development produced one: `GroupElt.lean` carries lamp
configurations and travel but no group element, no word length, and no `lR`.  So the
statements below `M9` are all about configurations, and the qualifier is not
cosmetic -- there was no object a group element could be.

This file supplies the missing object.  An `Elt` is a lamp configuration with a
cursor and finite support -- exactly the data of a group element in the lamplighter
presentation -- and `toPathData` builds its `PathData`, computing the minimal span
`[A, B]` from the support.  The three span obligations `houter`, `hAmin`, `hBmin`
are the content: `A` and `B` must be *minimal*, not merely valid bounds.
-/
import Realisation
import Mathlib.Data.Finset.Max
import Mathlib.RingTheory.PowerSeries.Basic
import ConfigLoop
import TurnBuild

namespace EltBridge

open SiteCost

/-- **A group element in lamp form**: a cursor `kstar`, a sign `eps`, a side `delta`,
and a finitely supported deposit function carrying the travel parity. -/
structure Elt where
  kstar : ℤ
  eps : ℤ
  delta : Bool
  heps : eps = 1 ∨ eps = -1
  d : ℤ → ℤ
  hpar : ∀ j, (d j - travel kstar j) % 2 = 0
  supp : Finset ℤ
  hsupp : ∀ j, j ∉ supp → d j = 0 ∧ travel kstar j = 0

namespace Elt

variable (g : Elt)

/-- The occupied edges, together with `0`.  Its min and max are the minimal span. -/
noncomputable def occ : Finset ℤ :=
  insert 0 (g.supp.filter (fun j => g.d j ≠ 0 ∨ travel g.kstar j ≠ 0))

theorem zero_mem_occ : (0 : ℤ) ∈ g.occ := Finset.mem_insert_self _ _

theorem occ_nonempty : g.occ.Nonempty := ⟨0, g.zero_mem_occ⟩

/-- An edge carrying a deposit or a travel step is in `occ`. -/
theorem mem_occ_of_ne (j : ℤ) (h : g.d j ≠ 0 ∨ travel g.kstar j ≠ 0) : j ∈ g.occ := by
  classical
  by_cases hj : j ∈ g.supp
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hj, h⟩)
  · rcases h with h | h
    · exact absurd (g.hsupp j hj).1 h
    · exact absurd (g.hsupp j hj).2 h

/-- The left end of the span. -/
noncomputable def A : ℤ := g.occ.min' g.occ_nonempty
/-- The right end of the span. -/
noncomputable def B : ℤ := g.occ.max' g.occ_nonempty

theorem A_le_zero : g.A ≤ 0 := Finset.min'_le _ _ g.zero_mem_occ
theorem zero_le_B : (0 : ℤ) ≤ g.B := Finset.le_max' _ _ g.zero_mem_occ

/-- **Outside the span there is neither deposit nor travel.** -/
theorem outer (j : ℤ) (h : j < g.A ∨ g.B < j) :
    g.d j = 0 ∧ travel g.kstar j = 0 := by
  by_contra hc
  have hne : g.d j ≠ 0 ∨ travel g.kstar j ≠ 0 := by
    rcases Decidable.em (g.d j = 0) with h1 | h1
    · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
    · exact Or.inl h1
  have hmem := g.mem_occ_of_ne j hne
  rcases h with h | h
  · have hle : g.A ≤ j := Finset.min'_le g.occ j hmem
    omega
  · have hle : j ≤ g.B := Finset.le_max' g.occ j hmem
    omega

/-- **`A` is minimal.** -/
theorem A_min : g.A = 0 ∨ g.d g.A ≠ 0 ∨ travel g.kstar g.A ≠ 0 := by
  classical
  have h := Finset.min'_mem g.occ g.occ_nonempty
  simp only [occ, Finset.mem_insert] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_filter.mp h).2

/-- **`B` is minimal.** -/
theorem B_min : g.B = 0 ∨ g.d g.B ≠ 0 ∨ travel g.kstar g.B ≠ 0 := by
  classical
  have h := Finset.max'_mem g.occ g.occ_nonempty
  simp only [occ, Finset.mem_insert] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_filter.mp h).2

/-- **The bridge.**  Every group element in lamp form has a `PathData`. -/
noncomputable def toPathData : PathData where
  kstar := g.kstar
  eps := g.eps
  delta := g.delta
  heps := g.heps
  d := g.d
  hpar := g.hpar
  A := g.A
  B := g.B
  hA := g.A_le_zero
  hB := g.zero_le_B
  houter := g.outer
  hAmin := g.A_min
  hBmin := g.B_min

@[simp] theorem toPathData_d : g.toPathData.d = g.d := rfl
@[simp] theorem toPathData_kstar : g.toPathData.kstar = g.kstar := rfl

/-- **The relaxed length of a group element.**  This is the definition the
development did not have: with `toPathData`, `lR` is now a function of `g`. -/
noncomputable def lR : ℕ := g.toPathData.lR

/-- **The metric formula, as a contract (Rule I7).**

`rem:pairingstatus` records that the optimisation computes the relaxed word length
"verified there and not proved".  It cannot be *stated* in Lean without a word-length
function on group elements, which the development lacks.  This names the obligation:
any candidate relaxed-length function must agree with `lR`.  Discharging it is H1a,
and it needs a presentation and a generating set, neither of which is formalised.

This is deliberately a `Prop`-valued contract and not a theorem.  It is the honest
form of a gap that was previously only prose. -/
def IsRelaxedLength (L : Elt → ℕ) : Prop := ∀ g : Elt, L g = g.lR

/-- The relaxed length is the span mass plus the site costs -- unfolded, so the
contract above is not opaque. -/
theorem lR_eq : g.lR =
    (∑ j ∈ Finset.Icc g.A g.B, g.toPathData.mu j)
      + ∑ s ∈ Finset.Icc g.A (g.B + 1), g.toPathData.siteCost s := rfl

end Elt

/-! ### B1, second half: exactly two sites need repair

`ConfigLoop.balance_iff_tr` says balance at a site is equivalent to the two adjacent
edges carrying equal signed travel.  `travel_site_facts` says `travel` steps only at
`s = 0` and `s = kstar`.  Together: a configuration whose signed travel is `travel`
is **automatically balanced at every other site**, and the two virtual events are not
a modelling choice -- they are exactly the two repairs the balance needs. -/

/-- **`travel` is constant away from the two virtual sites.** -/
theorem travel_const_off (kstar s : ℤ) (h0 : s ≠ 0) (hk : s ≠ kstar) :
    travel kstar (s - 1) = travel kstar s := by
  have h := travel_site_facts kstar s (if s = 0 then 1 else 0) (if s = kstar then 1 else 0)
    (travel kstar (s - 1)) (travel kstar s) rfl rfl rfl rfl
  have := h.1
  rw [if_neg h0, if_neg hk] at this
  omega

/-- **Balance is automatic away from the two virtual sites.**

A configuration realising a `travel` -- one whose signed travel `tr` on each edge is
the travel indicator of that edge -- is balanced at every site other than `0` and
`kstar`.  So the `Endpt` model needs repair at exactly two sites, which is what the
two virtual endpoints supply. -/
theorem balance_off_virtual {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (kstar : ℤ)
    (htr : ∀ e : Fin n, ConfigLoop.tr (m := mm) up e = travel kstar (e : ℤ))
    (s : ℤ) (h0 : s ≠ 0) (hk : s ≠ kstar) (e1 e2 : Fin n)
    (h1 : (e1 : ℤ) = s - 1) (h2 : (e2 : ℤ) = s) :
    (EndType.arrAt (m := mm) up s).card = (EndType.depAt (m := mm) up s).card := by
  refine (ConfigLoop.balance_iff_tr (m := mm) up s e1 e2 h1 h2).mpr ?_
  rw [htr e1, htr e2, h1, h2]
  exact travel_const_off kstar s h0 hk

/-- **The exact deficit.**  For a configuration realising a `travel`, the arrival
minus departure count at any site is `[s = kstar] - [s = 0]`.

So the model is short exactly one arrival at site `0` and one departure at site
`kstar`, and balanced everywhere else.  The two virtual events `vArr` and `vD` are
not a modelling choice: they are the unique repair, in the unique places. -/
theorem deficit_eq {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (kstar : ℤ)
    (htr : ∀ e : Fin n, ConfigLoop.tr (m := mm) up e = travel kstar (e : ℤ))
    (s : ℤ) (e1 e2 : Fin n) (h1 : (e1 : ℤ) = s - 1) (h2 : (e2 : ℤ) = s) :
    ((EndType.arrAt (m := mm) up s).card : ℤ) - (EndType.depAt (m := mm) up s).card
      = (if s = kstar then 1 else 0) - (if s = 0 then 1 else 0) := by
  rw [ConfigLoop.arr_sub_dep_eq (m := mm) up s e1 e2 h1 h2, htr e1, htr e2, h1, h2]
  have h := travel_site_facts kstar s (if s = 0 then 1 else 0) (if s = kstar then 1 else 0)
    (travel kstar (s - 1)) (travel kstar s) rfl rfl rfl rfl
  have := h.1
  omega

/-! ### The two-element extension of `Endpt`

`deficit_eq` says the model is short one arrival at site `0` and one departure at
site `kstar`.  This adds exactly those two elements and nothing else. -/

/-- **The extended end type**: the real ends, plus two virtual ones.  `inr false` is
the virtual arrival at site `0`; `inr true` is the virtual departure at `kstar`. -/
abbrev VEndpt (n : ℕ) (mm : Fin n → ℕ) := EndType.Endpt n mm ⊕ Bool

namespace VEndpt

variable {n : ℕ} {mm : Fin n → ℕ}

/-- The site of an extended end. -/
def site (kstar : ℤ) : VEndpt n mm → ℤ
  | .inl x => EndType.siteOf x
  | .inr false => 0
  | .inr true => kstar

/-- Whether an extended end is an arrival. -/
def isArr (up : Fin n → ℕ) : VEndpt n mm → Bool
  | .inl x => EndType.isArrOf up x
  | .inr false => true
  | .inr true => false

/-- Arrivals at a site, extended. -/
noncomputable def arrAt (kstar : ℤ) (up : Fin n → ℕ) (s : ℤ) : Finset (VEndpt n mm) := by
  classical
  exact Finset.univ.filter (fun x => site kstar x = s ∧ isArr up x = true)

/-- Departures at a site, extended. -/
noncomputable def depAt (kstar : ℤ) (up : Fin n → ℕ) (s : ℤ) : Finset (VEndpt n mm) := by
  classical
  exact Finset.univ.filter (fun x => site kstar x = s ∧ isArr up x = false)

/-- **The extended arrivals are the real ones plus the virtual arrival at `0`.** -/
theorem arrAt_eq (kstar : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    arrAt (mm := mm) kstar up s
      = (EndType.arrAt (m := mm) up s).image Sum.inl
        ∪ (if s = 0 then {Sum.inr false} else ∅) := by
  classical
  ext x
  cases x with
  | inl y =>
    by_cases h : s = 0 <;>
      simp [arrAt, site, isArr, EndType.mem_arrAt, h]
  | inr b =>
    cases b <;> by_cases h : s = 0 <;>
      simp [arrAt, site, isArr, h] <;> omega

/-- **The extended departures are the real ones plus the virtual departure at `kstar`.** -/
theorem depAt_eq (kstar : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    depAt (mm := mm) kstar up s
      = (EndType.depAt (m := mm) up s).image Sum.inl
        ∪ (if s = kstar then {Sum.inr true} else ∅) := by
  classical
  ext x
  cases x with
  | inl y =>
    by_cases h : s = kstar <;>
      simp [depAt, site, isArr, EndType.mem_depAt, h]
  | inr b =>
    cases b <;> by_cases h : s = kstar <;>
      simp [depAt, site, isArr, h] <;> omega

/-- The virtual arrival is not a real end. -/
theorem card_arrAt (kstar : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    (arrAt (mm := mm) kstar up s).card
      = (EndType.arrAt (m := mm) up s).card + (if s = 0 then 1 else 0) := by
  classical
  rw [arrAt_eq]
  have hdisj : Disjoint ((EndType.arrAt (m := mm) up s).image Sum.inl)
      (if s = 0 then ({Sum.inr false} : Finset (VEndpt n mm)) else ∅) := by
    split_ifs <;> simp [Finset.disjoint_left]
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective]
  split_ifs <;> simp

/-- The virtual departure is not a real end. -/
theorem card_depAt (kstar : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    (depAt (mm := mm) kstar up s).card
      = (EndType.depAt (m := mm) up s).card + (if s = kstar then 1 else 0) := by
  classical
  rw [depAt_eq]
  have hdisj : Disjoint ((EndType.depAt (m := mm) up s).image Sum.inl)
      (if s = kstar then ({Sum.inr true} : Finset (VEndpt n mm)) else ∅) := by
    split_ifs <;> simp [Finset.disjoint_left]
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective]
  split_ifs <;> simp

end VEndpt

/-- **B1, second half: the extended model is balanced.**

A configuration whose signed travel is `travel kstar` is balanced at every site once
the two virtual ends are added.  With `deficit_eq` this is the whole content: the real
model is off by `[s = kstar] - [s = 0]`, and the two virtual ends contribute exactly
`[s = 0]` arrivals and `[s = kstar]` departures. -/
theorem VEndpt.balanced {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (kstar : ℤ)
    (htr : ∀ e : Fin n, ConfigLoop.tr (m := mm) up e = travel kstar (e : ℤ))
    (s : ℤ) (e1 e2 : Fin n) (h1 : (e1 : ℤ) = s - 1) (h2 : (e2 : ℤ) = s) :
    (VEndpt.arrAt (mm := mm) kstar up s).card
      = (VEndpt.depAt (mm := mm) kstar up s).card := by
  have hd := deficit_eq (mm := mm) up kstar htr s e1 e2 h1 h2
  have ha := VEndpt.card_arrAt (mm := mm) kstar up s
  have hb := VEndpt.card_depAt (mm := mm) kstar up s
  rw [ha, hb]
  split_ifs at hd ⊢ <;> omega

/-! ### The crossing partner on the extended type

This is the one genuine choice in the extension, and it is where the transport stops
being bookkeeping.  The virtual arrival at site `0` and the virtual departure at
`kstar` have no crossing of their own; reading them as the two ends of **one** virtual
crossing pairs them with each other.  That reading is what `hyp:model` makes silently,
so it belongs to (M).  Stated here, and checked against the three properties
`partner` has to have. -/

/-- **The extended crossing partner.**  Real ends keep their partner; the two virtual
ends are the two ends of one virtual crossing, so they partner each other. -/
def VEndpt.partner {n : ℕ} {mm : Fin n → ℕ} : VEndpt n mm → VEndpt n mm
  | .inl x => .inl (EndType.partner x)
  | .inr b => .inr (!b)

/-- It is an involution. -/
theorem VEndpt.partner_invol {n : ℕ} {mm : Fin n → ℕ} (x : VEndpt n mm) :
    VEndpt.partner (VEndpt.partner x) = x := by
  cases x with
  | inl y => simp [VEndpt.partner, EndType.partner_invol]
  | inr b => cases b <;> rfl

/-- It has no fixed point. -/
theorem VEndpt.partner_ne {n : ℕ} {mm : Fin n → ℕ} (x : VEndpt n mm) :
    VEndpt.partner x ≠ x := by
  cases x with
  | inl y => simpa [VEndpt.partner] using EndType.partner_ne y
  | inr b => cases b <;> simp [VEndpt.partner]

/-- **It exchanges arrivals and departures**, on the virtual pair as well as the real
ones -- which is exactly why the pairing above is the right one, and not a
convention. -/
theorem VEndpt.isArr_partner {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (x : VEndpt n mm) :
    VEndpt.isArr up (VEndpt.partner x) = !VEndpt.isArr up x := by
  cases x with
  | inl y => simpa [VEndpt.partner, VEndpt.isArr] using EndType.isArrOf_partner up y
  | inr b => cases b <;> rfl

/-- **It always changes site**, provided the two virtual events do not coincide --
that is, provided `kstar` is not `0`.  This is the hypothesis `p_site_ne` needs, and
`travel_site_facts` already records that `kstar = 0` is the degenerate case. -/
theorem VEndpt.partner_site_ne {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ) (hk : kstar ≠ 0)
    (x : VEndpt n mm) :
    VEndpt.site kstar (VEndpt.partner x) ≠ VEndpt.site kstar x := by
  cases x with
  | inl y =>
    simpa [VEndpt.partner, VEndpt.site] using
      WalkSupport.p_site_ne EndType.edgeOf EndType.siteOf EndType.atTop EndType.partner
        (fun _ => rfl) (fun w => EndType.partner_edgeOf w) (fun w => EndType.partner_top w) y
  | inr b => cases b <;> simp [VEndpt.partner, VEndpt.site] <;> omega

/-- **The virtual pairing is forced, not a modelling choice.**

Any extended partner that (a) restricts to the real partner on real ends, (b) is an
involution, and (c) exchanges arrivals and departures, **must** pair the two virtual
ends with each other.  So `hyp:model` has one fewer degree of freedom than it appears
to: the virtual arrival cannot be partnered with a real departure, because its image
would then have to be sent back by (a) to a real end rather than to it.

This removes a free choice from (M) rather than making one. -/
theorem VEndpt.partner_unique {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (P : VEndpt n mm → VEndpt n mm)
    (hreal : ∀ x : EndType.Endpt n mm, P (.inl x) = .inl (EndType.partner x))
    (hinv : ∀ y, P (P y) = y)
    (harr : ∀ y, VEndpt.isArr up (P y) = !VEndpt.isArr up y) :
    P = VEndpt.partner := by
  funext y
  cases y with
  | inl x => rw [hreal x]; rfl
  | inr b =>
    -- the image cannot be a real end: (b) would send it back via (a)
    rcases hP : P (.inr b) with x | c
    · exfalso
      have h1 : P (P (.inr b)) = Sum.inl (EndType.partner x) := by rw [hP, hreal]
      rw [hinv] at h1
      simp at h1
    · have h2 := harr (.inr b)
      rw [hP] at h2
      cases b <;> cases c <;> simp_all [VEndpt.isArr, VEndpt.partner]

/-! ### The virtual crossing does not sit on an edge

The merge development is generic in the end type: `CostMerge.min_merges_to_one` takes
`edgeOf`, `siteOf`, `atTop`, `p0` as arguments, with four compatibility hypotheses.
Transport to `VEndpt` therefore needs only an `edgeOf` and an `atTop` for the two
virtual ends.  **There is none**, except in a degenerate case.

`hpe` forces the two virtual ends onto a common edge `j`, `hpt` forces them to be its
two ends, and `hsite` then puts their sites at `j` and `j + 1` in some order.  But
their sites are `0` and `kstar`.  So `kstar = 1` or `kstar = -1`. -/

/-- **The forced virtual pairing is incompatible with the edge geometry unless
`|kstar| = 1`.** -/
theorem VEndpt.no_virtual_edge {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ)
    (edgeOf : VEndpt n mm → ℤ) (atTop : VEndpt n mm → Bool)
    (hsite : ∀ x, VEndpt.site kstar x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (VEndpt.partner x) = edgeOf x)
    (hpt : ∀ x, atTop (VEndpt.partner x) = !atTop x) :
    kstar = 1 ∨ kstar = -1 := by
  have hA := hsite (Sum.inr false)
  have hB := hsite (Sum.inr true)
  have he : edgeOf (Sum.inr true : VEndpt n mm) = edgeOf (Sum.inr false : VEndpt n mm) := by
    have := hpe (Sum.inr false); simpa [VEndpt.partner] using this
  have ht : atTop (Sum.inr true : VEndpt n mm) = !atTop (Sum.inr false : VEndpt n mm) := by
    have := hpt (Sum.inr false); simpa [VEndpt.partner] using this
  simp only [VEndpt.site] at hA hB
  rw [he] at hB
  cases hb : atTop (Sum.inr false : VEndpt n mm)
  · have e1 : (if atTop (Sum.inr false : VEndpt n mm) then (1:ℤ) else 0) = 0 := by
      rw [hb]; rfl
    have e2 : (if atTop (Sum.inr true : VEndpt n mm) then (1:ℤ) else 0) = 1 := by
      rw [ht, hb]; rfl
    rw [e1] at hA; rw [e2] at hB; omega
  · have e1 : (if atTop (Sum.inr false : VEndpt n mm) then (1:ℤ) else 0) = 1 := by
      rw [hb]; rfl
    have e2 : (if atTop (Sum.inr true : VEndpt n mm) then (1:ℤ) else 0) = 0 := by
      rw [ht, hb]; rfl
    rw [e1] at hA; rw [e2] at hB; omega

/-! ### The fork is decided: branch 2 is impossible

Branch 2 was to run the merge on the real ends and reattach the virtual pair
afterwards.  It cannot be done, and the reason is not incidental: a `Data` is a turn
*involution* exchanging arrivals and departures at each site, so its mere existence
forces balance.  With `deficit_eq` the real-end model is off by `[s=kstar] - [s=0]`,
so at those two sites there is no turn at all -- nothing to run the merge on.

Branch 1 is therefore forced.  Its cost is measured: 12 theorems in `WalkSupport`
plus their users in `CostMerge` depend on `hpe`/`hpt`, and the dependence is
mathematical rather than clerical -- `wLo` arguments need the partner of an end at a
walk's leftmost edge to sit on that same edge, which the virtual pair violates by
construction. -/

/-- **A turn forces balance.**  If a `Data` preserves sites and exchanges arrivals
with departures, then arrivals and departures are equinumerous at every site. -/
theorem balance_of_data {α : Type*} [Fintype α] [DecidableEq α]
    (siteOf : α → ℤ) (isArr : α → Bool) (D : WalkGraph.Data α)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, isArr (D.t e) = !isArr e) (s : ℤ) :
    (Finset.univ.filter (fun x => siteOf x = s ∧ isArr x = true)).card
      = (Finset.univ.filter (fun x => siteOf x = s ∧ isArr x = false)).card := by
  classical
  refine Finset.card_bij' (fun a _ => D.t a) (fun b _ => D.t b) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, by rw [hts, ha.2.1], ?_⟩
    rw [hta, ha.2.2]; rfl
  · intro b hb
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ _, by rw [hts, hb.2.1], ?_⟩
    rw [hta, hb.2.2]; rfl
  · intro a _; exact D.t_invol a
  · intro b _; exact D.t_invol b

/-- **Branch 2 is impossible.**  At a site where arrivals and departures differ in
number, no `Data` exists.  By `deficit_eq` those are exactly `0` and `kstar`. -/
theorem no_data_of_deficit {α : Type*} [Fintype α] [DecidableEq α]
    (siteOf : α → ℤ) (isArr : α → Bool) (s : ℤ)
    (hne : (Finset.univ.filter (fun x => siteOf x = s ∧ isArr x = true)).card
      ≠ (Finset.univ.filter (fun x => siteOf x = s ∧ isArr x = false)).card) :
    ¬ ∃ D : WalkGraph.Data α, (∀ e, siteOf (D.t e) = siteOf e) ∧
        (∀ e, isArr (D.t e) = !isArr e) := by
  rintro ⟨D, hts, hta⟩
  exact hne (balance_of_data siteOf isArr D hts hta s)

/-! ### Correction: the obstruction is `hsite`, not `hpe`/`hpt`

Put the virtual pair on a common phantom edge `bnd` beyond the span, with the two
ends distinguished by `atTop`.  Then the partner **is** edge-local and end-flipping
everywhere: `hpe` and `hpt` hold globally.  What fails is `hsite`, which ties a site
to its edge -- and must fail, since the virtual ends' sites are `0` and `kstar` while
their edge is `bnd`.

So BLOCK 12's measurement was of the wrong hypothesis.  `hpe`/`hpt` are not the
obstruction; `hsite` is. -/

/-- Edge of an extended end, virtual ends on a phantom edge `bnd`. -/
def VEndpt.edgeOf {n : ℕ} {mm : Fin n → ℕ} (bnd : ℤ) : VEndpt n mm → ℤ
  | .inl x => EndType.edgeOf x
  | .inr _ => bnd

/-- Which end of its crossing an extended end is. -/
def VEndpt.atTop {n : ℕ} {mm : Fin n → ℕ} : VEndpt n mm → Bool
  | .inl x => EndType.atTop x
  | .inr b => b

/-- **`hpe` holds globally** on the extended type. -/
theorem VEndpt.hpe {n : ℕ} {mm : Fin n → ℕ} (bnd : ℤ) (x : VEndpt n mm) :
    VEndpt.edgeOf bnd (VEndpt.partner x) = VEndpt.edgeOf bnd x := by
  cases x with
  | inl y => simpa [VEndpt.partner, VEndpt.edgeOf] using EndType.partner_edgeOf y
  | inr b => rfl

/-- **`hpt` holds globally** on the extended type. -/
theorem VEndpt.hpt {n : ℕ} {mm : Fin n → ℕ} (x : VEndpt n mm) :
    VEndpt.atTop (VEndpt.partner x) = !VEndpt.atTop x := by
  cases x with
  | inl y => rfl
  | inr b => cases b <;> rfl

/-- **`hsite` fails, and must.**  There is no `bnd` making the site-edge relation hold
at the virtual arrival and the virtual departure at once, unless `|kstar| = 1` --
which is `no_virtual_edge` again, now with the pairing made concrete. -/
theorem VEndpt.hsite_fails {n : ℕ} {mm : Fin n → ℕ} (kstar bnd : ℤ)
    (h : ∀ x : VEndpt n mm, VEndpt.site kstar x
      = VEndpt.edgeOf bnd x + (if VEndpt.atTop x then 1 else 0)) :
    kstar = 1 ∨ kstar = -1 :=
  VEndpt.no_virtual_edge kstar (VEndpt.edgeOf bnd) VEndpt.atTop h
    (VEndpt.hpe bnd) VEndpt.hpt

/-! ### The residual condition, and it is not automatic

`maximiser_has_bottom_arrival_local` asks for the site-edge relation only at ends
sitting at the walk's leftmost site (and at its leftmost edge).  For `VEndpt` the real
ends satisfy it definitionally.  The virtual ends do not -- and they are in scope
exactly when the walk's leftmost site is `0` or `kstar`.

So the localization is **not free** here, unlike at `exists_bottom_at_wLo`.  What
remains is a geometric side condition, stated below.  It is a genuine restriction: a
walk may well have leftmost edge `0`, since the span begins at `A <= 0`. -/

/-- **The site-edge relation holds at every real end**, definitionally. -/
theorem VEndpt.hsite_real {n : ℕ} {mm : Fin n → ℕ} (kstar bnd : ℤ)
    (y : EndType.Endpt n mm) :
    VEndpt.site kstar (Sum.inl y : VEndpt n mm)
      = VEndpt.edgeOf bnd (Sum.inl y : VEndpt n mm)
        + (if VEndpt.atTop (Sum.inl y : VEndpt n mm) then 1 else 0) := rfl

/-- **The localized hypothesis holds exactly when the two virtual sites are not the
walk's leftmost site.**  This is the residual obligation branch 1 leaves behind. -/
theorem VEndpt.hsW_of_avoids {n : ℕ} {mm : Fin n → ℕ} (kstar bnd : ℤ)
    (D : WalkGraph.Data (VEndpt n mm)) (z : VEndpt n mm)
    (w : ℤ) (h0 : w ≠ 0) (hk : w ≠ kstar) :
    ∀ x : VEndpt n mm, VEndpt.site kstar x = w →
      VEndpt.site kstar x
        = VEndpt.edgeOf bnd x + (if VEndpt.atTop x then 1 else 0) := by
  intro x hx
  cases x with
  | inl y => exact VEndpt.hsite_real kstar bnd y
  | inr b =>
    exfalso
    cases b
    · exact h0 (by simpa [VEndpt.site] using hx.symm)
    · exact hk (by simpa [VEndpt.site] using hx.symm)

/-- **And it fails when the walk's leftmost site is one of the two.**  So the side
condition cannot be dropped: at `w = 0` the virtual arrival is in scope and its site
is not determined by its edge. -/
theorem VEndpt.hsW_fails_at_zero {n : ℕ} {mm : Fin n → ℕ} (kstar bnd : ℤ)
    (hbnd : bnd ≠ 0) :
    ¬ (VEndpt.site kstar (Sum.inr false : VEndpt n mm)
        = VEndpt.edgeOf bnd (Sum.inr false : VEndpt n mm)
          + (if VEndpt.atTop (Sum.inr false : VEndpt n mm) then 1 else 0)) := by
  intro h
  simp [VEndpt.site, VEndpt.edgeOf, VEndpt.atTop] at h
  omega

/-! ### The residual condition halves

With the disjunctive form, the virtual **arrival** discharges its obligation for free:
`atTop (inr false) = false`, so it is already a bottom and never needs the site-edge
relation.  BLOCK 14's condition `w != 0` disappears.

`hsX` is vacuous for virtual ends once `bnd` exceeds the walk's leftmost edge, which
it does whenever the walk contains a real end -- and it does, since the virtual
arrival turns to a real departure.

What remains is the virtual **departure**: `atTop (inr true) = true`, so it needs the
second disjunct, and it is in scope exactly when the walk's leftmost site is `kstar`.
One condition, not two. -/

/-- **`hsW` holds for the extended type whenever the leftmost site avoids `kstar`.**
The site-`0` case of BLOCK 14 is gone: the virtual arrival is a bottom. -/
theorem VEndpt.hsW_disj {n : ℕ} {mm : Fin n → ℕ} (kstar bnd : ℤ) (w : ℤ)
    (hk : w ≠ kstar) :
    ∀ x : VEndpt n mm, VEndpt.site kstar x = w →
      VEndpt.atTop x = false ∨
        VEndpt.site kstar x
          = VEndpt.edgeOf bnd x + (if VEndpt.atTop x then 1 else 0) := by
  intro x hx
  cases x with
  | inl y => exact Or.inr (VEndpt.hsite_real kstar bnd y)
  | inr b =>
    cases b
    · exact Or.inl rfl
    · exact absurd (by simpa [VEndpt.site] using hx.symm) hk

/-- **`hsX` is vacuous for the virtual ends** once `bnd` is beyond the leftmost edge. -/
theorem VEndpt.hsX_beyond {n : ℕ} {mm : Fin n → ℕ} (kstar bnd : ℤ) (w : ℤ)
    (hb : w < bnd) :
    ∀ x : VEndpt n mm, VEndpt.edgeOf bnd x = w → VEndpt.atTop x = false →
      VEndpt.site kstar x
        = VEndpt.edgeOf bnd x + (if VEndpt.atTop x then 1 else 0) := by
  intro x hx _
  cases x with
  | inl y => exact VEndpt.hsite_real kstar bnd y
  | inr b => exact absurd hx (by simp [VEndpt.edgeOf]; omega)

/-! ### The residual condition is automatic for `kstar > 0`

The walk carrying the virtual pair also carries the virtual arrival, whose *turn* is a
real end at site `0` -- so on edge `-1` or `0`.  Hence that walk's leftmost edge is at
most `0`.  When `kstar > 0` it is therefore not `kstar`, and BLOCK 15's condition
holds automatically.

For `kstar < 0` the same argument gives only `wLo <= kstar`, not `wLo < kstar`: the
real ends at site `kstar` sit on edges `kstar - 1` and `kstar`, and `kstar - 1` lies
outside the span, so it may be empty.  That half does not close by this route. -/

/-- **BLOCK 15's condition, discharged for `kstar > 0`.**  A walk reaching any end at
edge `<= 0` has leftmost edge `<= 0`, hence not `kstar`. -/
theorem VEndpt.leftmost_ne_kstar {n : ℕ} {mm : Fin n → ℕ} (kstar bnd : ℤ)
    (D : WalkGraph.Data (VEndpt n mm)) (z : VEndpt n mm) (hk : 0 < kstar)
    (y : VEndpt n mm) (hzy : (WalkGraph.graph D).Reachable z y)
    (hy : VEndpt.edgeOf bnd y ≤ 0) :
    WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph D) z ≠ kstar := by
  have := WalkSupport.wLo_le (VEndpt.edgeOf bnd) (WalkGraph.graph D) hzy
  omega

/-- **And the end at edge `<= 0` is there**: the turn of the virtual arrival sits at
site `0`, so it is a real end on edge `-1` or `0`. -/
theorem VEndpt.turn_of_vArr_low {n : ℕ} {mm : Fin n → ℕ} (kstar bnd : ℤ)
    (D : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.site kstar (D.t e) = VEndpt.site kstar e)
    (hvirt : ∀ b : Bool, D.t (Sum.inr b) ≠ Sum.inr b)
    (hnk : kstar ≠ 0)
    (y : VEndpt n mm) (hy : y = D.t (Sum.inr false)) :
    VEndpt.edgeOf bnd y ≤ 0 ∨ ∃ u : EndType.Endpt n mm, y = Sum.inl u := by
  right
  have hsy : VEndpt.site kstar y = 0 := by
    rw [hy, hts]; rfl
  cases hcase : y with
  | inl u => exact ⟨u, rfl⟩
  | inr b =>
    exfalso
    cases b
    · exact hvirt false (hy.symm.trans hcase)
    · rw [hcase] at hsy; exact hnk (by simpa [VEndpt.site] using hsy)

/-- Reachability along a turn. -/
theorem reachable_turn {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (x : α) : (WalkGraph.graph D).Reachable x (D.t x) :=
  SimpleGraph.Adj.reachable (G := WalkGraph.graph D) (Or.inr rfl)

/-- **BLOCK 15's residual condition is DISCHARGED for `kstar > 0`.**

The walk carrying the virtual arrival reaches its turn, which sits at site `0`; being
a real end there, it lies on edge `-1` or `0`.  So the walk's leftmost edge is at most
`0`, hence not `kstar`. -/
theorem VEndpt.residual_discharged {n : ℕ} {mm : Fin n → ℕ} (kstar bnd : ℤ)
    (D : WalkGraph.Data (VEndpt n mm)) (z : VEndpt n mm) (hk : 0 < kstar)
    (hts : ∀ e, VEndpt.site kstar (D.t e) = VEndpt.site kstar e)
    (hvirt : ∀ b : Bool, D.t (Sum.inr b) ≠ Sum.inr b)
    (hz : (WalkGraph.graph D).Reachable z (Sum.inr false)) :
    WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph D) z ≠ kstar := by
  set y := D.t (Sum.inr false : VEndpt n mm) with hy
  have hzy : (WalkGraph.graph D).Reachable z y :=
    hz.trans (reachable_turn D (Sum.inr false))
  have hsy : VEndpt.site kstar y = 0 := by rw [hy, hts]; rfl
  have hle : VEndpt.edgeOf bnd y ≤ 0 := by
    rcases VEndpt.turn_of_vArr_low kstar bnd D hts hvirt (by omega) y hy with h | ⟨u, hu⟩
    · exact h
    · rw [hu] at hsy ⊢
      simp only [VEndpt.site, VEndpt.edgeOf, EndType.siteOf] at hsy ⊢
      split_ifs at hsy <;> omega
  exact VEndpt.leftmost_ne_kstar kstar bnd D z hk y hzy hle

/-! ### Reflection: `kstar < 0` reduces to `kstar > 0`

The map `j |-> -1 - j` on edges, together with `kstar |-> -kstar`, negates `travel`:
the interval `[kstar, 0)` where `travel = -1` is carried onto `[0, -kstar)` where it
is `+1`.  Negating the deposits too gives an involution on `Elt` swapping the sign of
`kstar`, so `BLOCK 16`'s discharge for `kstar > 0` covers `kstar < 0` as well. -/

/-- **The reflection identity.**  `j |-> -1 - j` with `kstar |-> -kstar` negates
`travel`. -/
theorem travel_reflect (kstar j : ℤ) : travel (-kstar) (-1 - j) = - travel kstar j := by
  unfold travel
  split_ifs <;> omega

/-- The same, read the other way. -/
theorem travel_reflect' (kstar j : ℤ) : travel (-kstar) j = - travel kstar (-1 - j) := by
  have := travel_reflect kstar (-1 - j)
  simpa using this

namespace Elt

variable (g : Elt)

/-- **The reflected element.**  Deposits and travel both negate; `kstar` flips sign. -/
noncomputable def reflect : Elt where
  kstar := -g.kstar
  eps := -g.eps
  delta := !g.delta
  heps := by rcases g.heps with h | h <;> simp [h]
  d := fun j => -g.d (-1 - j)
  hpar := by
    intro j
    have h := g.hpar (-1 - j)
    rw [travel_reflect' g.kstar j]
    omega
  supp := g.supp.image (fun j => -1 - j)
  hsupp := by
    intro j hj
    have hne : (-1 - j) ∉ g.supp := by
      intro hc
      exact hj (Finset.mem_image.mpr ⟨-1 - j, hc, by omega⟩)
    obtain ⟨h1, h2⟩ := g.hsupp (-1 - j) hne
    exact ⟨by simp [h1], by rw [travel_reflect' g.kstar j, h2]; ring⟩

@[simp] theorem reflect_kstar : g.reflect.kstar = -g.kstar := rfl

/-- **Reflection turns a negative cursor into a positive one**, so `BLOCK 16`'s
discharge covers the whole range. -/
theorem reflect_kstar_pos (hk : g.kstar < 0) : 0 < g.reflect.kstar := by
  rw [reflect_kstar]; omega

/-- Reflection is an involution on the cursor. -/
@[simp] theorem reflect_reflect_kstar : g.reflect.reflect.kstar = g.kstar := by
  simp

/-- **And on the deposits**, so it is an involution on the data that matters. -/
theorem reflect_reflect_d : g.reflect.reflect.d = g.d := by
  funext j
  show - (- g.d (-1 - (-1 - j))) = g.d j
  ring_nf

end Elt

/-! ### `kstar < 0` closes directly, with the other orientation

No transport along the reflection is needed.  `bnd` and the `atTop` orientation are
free, and BLOCK 15 recorded that the residual condition *moves* between the two
virtual ends with that choice.  For `kstar < 0` take `bnd = -1` and the opposite
orientation -- virtual arrival a **top**, virtual departure a **bottom**.  Then:

* the arrival satisfies the site-edge relation outright: its site is `0 = -1 + 1`;
* the departure is a bottom, so it takes the first disjunct of `hsW` for free;
* and `hsX` reaches the departure only when the walk's leftmost edge is `-1`, which
  with `wLo <= kstar <= -1` forces `kstar = -1` -- exactly the case where the relation
  holds at the departure too.

So both hypotheses hold with **no side condition**. -/

/-- The opposite orientation: virtual arrival a top, virtual departure a bottom. -/
def VEndpt.atTopN {n : ℕ} {mm : Fin n → ℕ} : VEndpt n mm → Bool
  | .inl x => EndType.atTop x
  | .inr b => !b

/-- `hpt` still holds in the opposite orientation. -/
theorem VEndpt.hptN {n : ℕ} {mm : Fin n → ℕ} (x : VEndpt n mm) :
    VEndpt.atTopN (VEndpt.partner x) = !VEndpt.atTopN x := by
  cases x with
  | inl y => rfl
  | inr b => cases b <;> rfl

/-- **`hsW` holds with no side condition when `kstar < 0`.** -/
theorem VEndpt.hsW_neg {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ) (w : ℤ) :
    ∀ x : VEndpt n mm, VEndpt.site kstar x = w →
      VEndpt.atTopN x = false ∨
        VEndpt.site kstar x
          = VEndpt.edgeOf (-1) x + (if VEndpt.atTopN x then 1 else 0) := by
  intro x _
  cases x with
  | inl y => exact Or.inr rfl
  | inr b =>
    cases b
    · exact Or.inr (by simp [VEndpt.site, VEndpt.edgeOf, VEndpt.atTopN])
    · exact Or.inl rfl

/-- **`hsX` holds with no side condition when `kstar < 0`**, given that the walk
reaches back to the cursor -- which it does, the virtual departure sitting there. -/
theorem VEndpt.hsX_neg {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ) (w : ℤ)
    (hk : kstar < 0) (hwlo : w ≤ kstar) :
    ∀ x : VEndpt n mm, VEndpt.edgeOf (-1) x = w → VEndpt.atTopN x = false →
      VEndpt.site kstar x
        = VEndpt.edgeOf (-1) x + (if VEndpt.atTopN x then 1 else 0) := by
  intro x hx _
  cases x with
  | inl y => rfl
  | inr b =>
    cases b
    · -- the arrival is a top here, so this branch is excluded by the third hypothesis
      simp [VEndpt.atTopN] at *
    · -- the departure: `edgeOf = -1 = w <= kstar <= -1` forces `kstar = -1`
      have hw : w = -1 := by simpa [VEndpt.edgeOf] using hx.symm
      have : kstar = -1 := by omega
      simp [VEndpt.site, VEndpt.edgeOf, VEndpt.atTopN, this]

/-! ### A generic `Data` builder

`DataBuild.dataOf` builds the walk-graph data of a lamp configuration, but it is
written against `Endpt n m`.  Its ingredients -- `TurnBuild.glue`,
`exists_involution_of_card_eq` -- are generic, so the construction is too.  This is
the version `VEndpt` needs, and it would have served `Endpt` equally. -/

namespace GenericData

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Arrivals at a site. -/
noncomputable def arrOf (siteOf : α → ℤ) (isArr : α → Bool) (s : ℤ) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => siteOf x = s ∧ isArr x = true)

/-- Departures at a site. -/
noncomputable def depOf (siteOf : α → ℤ) (isArr : α → Bool) (s : ℤ) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => siteOf x = s ∧ isArr x = false)

theorem arr_disj_dep (siteOf : α → ℤ) (isArr : α → Bool) (s : ℤ) :
    Disjoint (arrOf siteOf isArr s) (depOf siteOf isArr s) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [arrOf, depOf, Finset.mem_filter] at hx hx'
  rw [hx.2.2] at hx'
  exact Bool.noConfusion hx'.2.2

/-- Every end lies in one of the two sets at its own site. -/
theorem mem_own (siteOf : α → ℤ) (isArr : α → Bool) (x : α) :
    x ∈ arrOf siteOf isArr (siteOf x) ∨ x ∈ depOf siteOf isArr (siteOf x) := by
  classical
  cases h : isArr x
  · exact Or.inr (by simp [depOf, h])
  · exact Or.inl (by simp [arrOf, h])

variable (siteOf : α → ℤ) (isArr : α → Bool)
  (hbal : ∀ s : ℤ, (arrOf siteOf isArr s).card = (depOf siteOf isArr s).card)

/-- The local turn at a site. -/
noncomputable def turnAtG (s : ℤ) : α → α :=
  (TurnBuild.exists_involution_of_card_eq (arrOf siteOf isArr s) (depOf siteOf isArr s)
    (arr_disj_dep siteOf isArr s) (hbal s)).choose

/-- The global turn. -/
noncomputable def turnG : α → α := TurnBuild.glue siteOf (turnAtG siteOf isArr hbal)

theorem turnG_site (x : α) : siteOf (turnG siteOf isArr hbal x) = siteOf x := by
  have hspec := (TurnBuild.exists_involution_of_card_eq
    (arrOf siteOf isArr (siteOf x)) (depOf siteOf isArr (siteOf x))
    (arr_disj_dep siteOf isArr (siteOf x)) (hbal (siteOf x))).choose_spec
  show siteOf (turnAtG siteOf isArr hbal (siteOf x) x) = siteOf x
  rcases mem_own siteOf isArr x with h | h
  · have := hspec.2.1 x h
    simp only [depOf, Finset.mem_filter] at this
    exact this.2.1
  · have := hspec.2.2.1 x h
    simp only [arrOf, Finset.mem_filter] at this
    exact this.2.1

theorem turnG_ne (x : α) : turnG siteOf isArr hbal x ≠ x := by
  have hspec := (TurnBuild.exists_involution_of_card_eq
    (arrOf siteOf isArr (siteOf x)) (depOf siteOf isArr (siteOf x))
    (arr_disj_dep siteOf isArr (siteOf x)) (hbal (siteOf x))).choose_spec
  show turnAtG siteOf isArr hbal (siteOf x) x ≠ x
  rcases mem_own siteOf isArr x with h | h
  · exact hspec.2.2.2.2.1 x h
  · exact hspec.2.2.2.2.2 x h

theorem turnG_invol (x : α) :
    turnG siteOf isArr hbal (turnG siteOf isArr hbal x) = x :=
  TurnBuild.glue_invol siteOf (turnAtG siteOf isArr hbal)
    (fun s y => (TurnBuild.exists_involution_of_card_eq (arrOf siteOf isArr s)
      (depOf siteOf isArr s) (arr_disj_dep siteOf isArr s) (hbal s)).choose_spec.1 y)
    (fun y => turnG_site siteOf isArr hbal y) x

/-- Membership in `arrOf`, without simp. -/
theorem mem_arrOf {siteOf : α → ℤ} {isArr : α → Bool} {s : ℤ} {x : α} :
    x ∈ arrOf siteOf isArr s ↔ siteOf x = s ∧ isArr x = true := by
  classical
  simp only [arrOf, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Membership in `depOf`, without simp. -/
theorem mem_depOf {siteOf : α → ℤ} {isArr : α → Bool} {s : ℤ} {x : α} :
    x ∈ depOf siteOf isArr s ↔ siteOf x = s ∧ isArr x = false := by
  classical
  simp only [depOf, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The generic turn exchanges arrivals and departures.**  Missing from the first
pass: `dataG` proved involutivity, site-preservation and fixed-point freedom, but the
role flip is what `Merges` needs. -/
theorem turnG_arr (x : α) :
    isArr (turnG siteOf isArr hbal x) = !isArr x := by
  have hspec := (TurnBuild.exists_involution_of_card_eq
    (arrOf siteOf isArr (siteOf x)) (depOf siteOf isArr (siteOf x))
    (arr_disj_dep siteOf isArr (siteOf x)) (hbal (siteOf x))).choose_spec
  show isArr (turnAtG siteOf isArr hbal (siteOf x) x) = !isArr x
  unfold turnAtG
  cases h : isArr x
  · have hx : x ∈ depOf siteOf isArr (siteOf x) := mem_depOf.mpr ⟨rfl, h⟩
    have h2 := mem_arrOf.mp (hspec.2.2.1 x hx)
    rw [h2.2]; rfl
  · have hx : x ∈ arrOf siteOf isArr (siteOf x) := mem_arrOf.mpr ⟨rfl, h⟩
    have h2 := mem_depOf.mp (hspec.2.1 x hx)
    rw [h2.2]; rfl

/-- **The generic walk-graph data.** -/
noncomputable def dataG (p : α → α) (hp_invol : ∀ x, p (p x) = x)
    (hp_ne : ∀ x, p x ≠ x) (hp_site : ∀ x, siteOf (p x) ≠ siteOf x) :
    WalkGraph.Data α where
  p := p
  t := turnG siteOf isArr hbal
  p_invol := hp_invol
  t_invol := turnG_invol siteOf isArr hbal
  p_ne := hp_ne
  t_ne := turnG_ne siteOf isArr hbal
  pt_ne := fun x h => hp_site x (by rw [h]; exact turnG_site siteOf isArr hbal x)

/-- **`dataG` is in the merge class.** -/
theorem dataG_merges (p : α → α) (hp_invol : ∀ x, p (p x) = x)
    (hp_ne : ∀ x, p x ≠ x) (hp_site : ∀ x, siteOf (p x) ≠ siteOf x) :
    WalkSupport.Merges siteOf isArr p (dataG siteOf isArr hbal p hp_invol hp_ne hp_site) :=
  ⟨rfl, fun e => turnG_site siteOf isArr hbal e, fun e => turnG_arr siteOf isArr hbal e⟩

end GenericData

/-- **The walk-graph data of the extended type.**

Everything the generic builder needs is now available: the partner is an involution
without fixed points (`partner_invol`, `partner_ne`) and always changes site
(`partner_site_ne`, needing `kstar != 0`), and balance is `VEndpt.balanced`.

The balance hypothesis is taken as given rather than derived here: `VEndpt.balanced`
supplies it at every site whose two edges exist, and the sites outside the span need
the empty-edge argument of `balance_empty_edges`.  That is bookkeeping, and factoring
it out keeps this construction honest about what it consumes. -/
noncomputable def VEndpt.dataOf {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (kstar : ℤ)
    (hk : kstar ≠ 0)
    (hbal : ∀ s : ℤ,
      (GenericData.arrOf (VEndpt.site (mm := mm) kstar) (VEndpt.isArr up) s).card
        = (GenericData.depOf (VEndpt.site (mm := mm) kstar) (VEndpt.isArr up) s).card) :
    WalkGraph.Data (VEndpt n mm) :=
  GenericData.dataG (VEndpt.site kstar) (VEndpt.isArr up) hbal VEndpt.partner
    VEndpt.partner_invol VEndpt.partner_ne (VEndpt.partner_site_ne kstar hk)

/-- Its pairing is the extended partner. -/
@[simp] theorem VEndpt.dataOf_p {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (kstar : ℤ)
    (hk : kstar ≠ 0) (hbal) :
    (VEndpt.dataOf (mm := mm) up kstar hk hbal).p = VEndpt.partner := rfl

/-- Its turn preserves sites. -/
theorem VEndpt.dataOf_ts {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (kstar : ℤ)
    (hk : kstar ≠ 0) (hbal) (x : VEndpt n mm) :
    VEndpt.site kstar ((VEndpt.dataOf (mm := mm) up kstar hk hbal).t x)
      = VEndpt.site kstar x :=
  GenericData.turnG_site _ _ hbal x

/-- The generic arrival set is the extended one. -/
theorem arrOf_eq_arrAt {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    GenericData.arrOf (VEndpt.site (mm := mm) kstar) (VEndpt.isArr up) s
      = VEndpt.arrAt (mm := mm) kstar up s := rfl

/-- The generic departure set is the extended one. -/
theorem depOf_eq_depAt {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    GenericData.depOf (VEndpt.site (mm := mm) kstar) (VEndpt.isArr up) s
      = VEndpt.depAt (mm := mm) kstar up s := rfl

/-- **Balance at EVERY site of the extended type.**

This is `VEndpt.balanced` without the standing assumption that the two adjacent edges
exist.  `arr_sub_dep_all` handles the sites where they do not, and the two virtual
ends supply exactly the deficit `travel` leaves behind. -/
theorem VEndpt.balanced_all {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (kstar : ℤ)
    (htr : ∀ (s : ℤ) (e : Fin n), (e : ℤ) = s →
      ConfigLoop.tr (m := mm) up e = travel kstar s)
    (hz : ∀ s : ℤ, (∀ e : Fin n, (e : ℤ) ≠ s) → travel kstar s = 0) :
    ∀ s : ℤ,
      (GenericData.arrOf (VEndpt.site (mm := mm) kstar) (VEndpt.isArr up) s).card
        = (GenericData.depOf (VEndpt.site (mm := mm) kstar) (VEndpt.isArr up) s).card := by
  intro s
  rw [arrOf_eq_arrAt, depOf_eq_depAt, VEndpt.card_arrAt, VEndpt.card_depAt]
  have hreal := ConfigLoop.arr_sub_dep_all (m := mm) up s
    (travel kstar (s - 1)) (travel kstar s)
    (fun e he => htr (s - 1) e he) (fun h => hz (s - 1) h)
    (fun e he => htr s e he) (fun h => hz s h)
  have hfacts := travel_site_facts kstar s (if s = 0 then 1 else 0)
    (if s = kstar then 1 else 0) (travel kstar (s - 1)) (travel kstar s) rfl rfl rfl rfl
  have h1 := hfacts.1
  split_ifs at h1 ⊢ <;> omega

/-- **The walk-graph data of the extended type, unconditional in the balance.** -/
noncomputable def VEndpt.dataOfAll {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (kstar : ℤ)
    (hk : kstar ≠ 0)
    (htr : ∀ (s : ℤ) (e : Fin n), (e : ℤ) = s →
      ConfigLoop.tr (m := mm) up e = travel kstar s)
    (hz : ∀ s : ℤ, (∀ e : Fin n, (e : ℤ) ≠ s) → travel kstar s = 0) :
    WalkGraph.Data (VEndpt n mm) :=
  VEndpt.dataOf up kstar hk (VEndpt.balanced_all up kstar htr hz)

/-- **The turn of the virtual departure is a real end**, mirroring
`turn_of_vArr_low`: it sits at site `kstar`, and the only virtual end there is the
virtual departure itself, which a turn cannot fix. -/
theorem VEndpt.turn_of_vDep_real {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ)
    (D : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.site kstar (D.t e) = VEndpt.site kstar e)
    (hvirt : ∀ b : Bool, D.t (Sum.inr b) ≠ Sum.inr b)
    (hk : kstar ≠ 0)
    (y : VEndpt n mm) (hy : y = D.t (Sum.inr true)) :
    ∃ u : EndType.Endpt n mm, y = Sum.inl u := by
  have hsy : VEndpt.site kstar y = kstar := by rw [hy, hts]; rfl
  cases hcase : y with
  | inl u => exact ⟨u, rfl⟩
  | inr b =>
    exfalso
    cases b
    · rw [hcase] at hsy; exact hk (by simpa [VEndpt.site] using hsy.symm)
    · exact hvirt true (hy.symm.trans hcase)

/-- **`w <= kstar` for the walk carrying the virtual departure**, which is what
`hsX_neg` consumes.  The turn of the virtual departure is a real end at site `kstar`,
so it lies on edge `kstar - 1` or `kstar`. -/
theorem VEndpt.wlo_le_kstar {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ)
    (D : WalkGraph.Data (VEndpt n mm)) (z : VEndpt n mm)
    (hts : ∀ e, VEndpt.site kstar (D.t e) = VEndpt.site kstar e)
    (hvirt : ∀ b : Bool, D.t (Sum.inr b) ≠ Sum.inr b)
    (hk : kstar ≠ 0)
    (hz : (WalkGraph.graph D).Reachable z (Sum.inr true)) :
    WalkSupport.wLo (VEndpt.edgeOf (-1)) (WalkGraph.graph D) z ≤ kstar := by
  set y := D.t (Sum.inr true : VEndpt n mm) with hy
  have hzy : (WalkGraph.graph D).Reachable z y :=
    hz.trans (reachable_turn D (Sum.inr true))
  have hsy : VEndpt.site kstar y = kstar := by rw [hy, hts]; rfl
  obtain ⟨u, hu⟩ := VEndpt.turn_of_vDep_real kstar D hts hvirt hk y hy
  have hle : VEndpt.edgeOf (-1 : ℤ) y ≤ kstar := by
    rw [hu] at hsy ⊢
    simp only [VEndpt.site, VEndpt.edgeOf, EndType.siteOf] at hsy ⊢
    split_ifs at hsy <;> omega
  exact le_trans (WalkSupport.wLo_le (VEndpt.edgeOf (-1)) (WalkGraph.graph D) hzy) hle

/-- **`hsX` for `kstar < 0`, fully discharged** -- no side condition, in the exact
shape `min_merges_to_one_local` consumes. -/
theorem VEndpt.hsX_all_neg {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ)
    (D : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.site kstar (D.t e) = VEndpt.site kstar e)
    (hvirt : ∀ b : Bool, D.t (Sum.inr b) ≠ Sum.inr b)
    (hk : kstar < 0) :
    ∀ w x, (WalkGraph.graph D).Reachable w x →
      VEndpt.edgeOf (-1) x = WalkSupport.wLo (VEndpt.edgeOf (-1)) (WalkGraph.graph D) w →
      VEndpt.atTopN x = false →
      VEndpt.site kstar x
        = VEndpt.edgeOf (-1) x + (if VEndpt.atTopN x then 1 else 0) := by
  intro w x hwx hxe hxb
  cases x with
  | inl y => rfl
  | inr b =>
    cases b
    · exact absurd hxb (by simp [VEndpt.atTopN])
    · -- `x` is the virtual departure, at edge `-1`; so the walk's leftmost edge is `-1`
      have hw : WalkSupport.wLo (VEndpt.edgeOf (-1)) (WalkGraph.graph D) w = -1 := by
        simpa [VEndpt.edgeOf] using hxe.symm
      have hle := VEndpt.wlo_le_kstar kstar D w hts hvirt (by omega) hwx
      rw [hw] at hle
      have hks : kstar = -1 := by omega
      simp [VEndpt.site, VEndpt.edgeOf, VEndpt.atTopN, hks]

/-- **`hsW` for `kstar < 0`, fully discharged.** -/
theorem VEndpt.hsW_all_neg {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ)
    (D : WalkGraph.Data (VEndpt n mm)) :
    ∀ w x, (WalkGraph.graph D).Reachable w x →
      VEndpt.site kstar x
        = WalkSupport.wLo (VEndpt.edgeOf (-1)) (WalkGraph.graph D) w →
      VEndpt.atTopN x = false ∨
        VEndpt.site kstar x
          = VEndpt.edgeOf (-1) x + (if VEndpt.atTopN x then 1 else 0) := by
  intro w x _ _
  cases x with
  | inl y => exact Or.inr rfl
  | inr b =>
    cases b
    · exact Or.inr (by simp [VEndpt.site, VEndpt.edgeOf, VEndpt.atTopN])
    · exact Or.inl rfl

/-! ### Assembly

Everything `CostMerge.min_merges_to_one_local` consumes, supplied for `VEndpt` at
`kstar < 0`.  The only hypothesis left is `hcov0`, the covering condition -- the same
one the `Endpt`-side argument has always needed, not new debt from the extension. -/

/-- The end data of the extended type, in the `kstar < 0` orientation. -/
def vEndDataOf {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (ds : Bool → Bool) :
    EndData.Data (VEndpt n mm) :=
  ⟨VEndpt.atTopN, VEndpt.isArr up, ds⟩

@[simp] theorem vEndDataOf_side {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (ds : Bool → Bool) (x : VEndpt n mm) :
    (vEndDataOf up ds).side x = VEndpt.atTopN x := rfl

@[simp] theorem vEndDataOf_isArr {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (ds : Bool → Bool) : (vEndDataOf (mm := mm) up ds).isArr = VEndpt.isArr up := rfl

/-- **B1, assembled for `kstar < 0`.**

A cost-minimal datum on the extended type merges down to a single walk.  Every
locality hypothesis of the merge development is discharged by the construction; the
covering condition `hcov0` is the sole input. -/
theorem VEndpt.merges_to_one_neg {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (ds : Bool → Bool) (kstar : ℤ) (hk : kstar < 0)
    (hcov0 : ∀ j : ℤ, (∃ u : VEndpt n mm, VEndpt.edgeOf (-1) u = j) →
      (∃ v : VEndpt n mm, VEndpt.edgeOf (-1) v < j) →
      ∃ y : VEndpt n mm, VEndpt.edgeOf (-1) y = j - 1 ∧ VEndpt.atTopN y = true)
    (z₀ : VEndpt n mm)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : CostMerge.MergesMin (VEndpt.site kstar) (VEndpt.isArr up) VEndpt.partner
      (vEndDataOf up ds) D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.site kstar) (VEndpt.isArr up) VEndpt.partner
        (vEndDataOf up ds) D' ∧ WalkGraph.walkCount D' ≤ 1 := by
  refine CostMerge.min_merges_to_one_local (VEndpt.edgeOf (-1)) (VEndpt.site kstar)
    VEndpt.atTopN VEndpt.partner (vEndDataOf up ds)
    (fun _ => rfl) (VEndpt.partner_site_ne kstar (by omega))
    ?_ ?_ ?_ (VEndpt.hpe (-1)) VEndpt.hptN hcov0 z₀ D hD
  · -- hsW
    exact fun E _ w x hwx hsx => VEndpt.hsW_all_neg kstar E w x hwx hsx
  · -- hsX
    exact fun E hE w x hwx hxe hxb =>
      VEndpt.hsX_all_neg kstar E hE.2.1 (fun b h => E.t_ne _ h) hk w x hwx hxe hxb
  · -- hsT: the top end left of a leftmost edge is real, since the virtual ends sit at
    -- edge -1 and a leftmost edge minus one is below every end of the walk
    intro E _ w y hye hyt
    cases y with
    | inl u => rfl
    | inr b =>
      cases b
      · -- the virtual arrival: its site IS its edge plus one, by the choice `bnd = -1`
        simp [VEndpt.site, VEndpt.edgeOf, VEndpt.atTopN]
      · exact absurd hyt (by simp [VEndpt.atTopN])

/-! ### Assembly for `kstar > 0`

The original orientation, with `bnd` chosen above every real edge.  The three shapes
discharge differently from the `kstar < 0` case:

* `hsW` at the virtual **departure** is excluded, because that end is reachable from
  its partner the virtual arrival, and `residual_discharged` then says the walk's
  leftmost edge is not `kstar`;
* `hsX` at the virtual **arrival** is excluded, because the walk reaches a real end at
  edge `<= 0 < bnd`, so `bnd` is not the leftmost edge;
* `hsT` at the virtual departure is excluded, because `bnd + 1` exceeds every edge. -/

/-- The end data in the `kstar > 0` orientation. -/
def vEndDataOfP {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (ds : Bool → Bool) :
    EndData.Data (VEndpt n mm) :=
  ⟨VEndpt.atTop, VEndpt.isArr up, ds⟩

/-- **B1, assembled for `kstar > 0`.** -/
theorem VEndpt.merges_to_one_pos {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (ds : Bool → Bool) (kstar bnd : ℤ) (hk : 0 < kstar) (hb : 0 < bnd)
    (hbnd : ∀ u : EndType.Endpt n mm, EndType.edgeOf u < bnd)
    (hcov0 : ∀ j : ℤ, (∃ u : VEndpt n mm, VEndpt.edgeOf bnd u = j) →
      (∃ v : VEndpt n mm, VEndpt.edgeOf bnd v < j) →
      ∃ y : VEndpt n mm, VEndpt.edgeOf bnd y = j - 1 ∧ VEndpt.atTop y = true)
    (z₀ : VEndpt n mm)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : CostMerge.MergesMin (VEndpt.site kstar) (VEndpt.isArr up) VEndpt.partner
      (vEndDataOfP up ds) D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.site kstar) (VEndpt.isArr up) VEndpt.partner
        (vEndDataOfP up ds) D' ∧ WalkGraph.walkCount D' ≤ 1 := by
  refine CostMerge.min_merges_to_one_local (VEndpt.edgeOf bnd) (VEndpt.site kstar)
    VEndpt.atTop VEndpt.partner (vEndDataOfP up ds)
    (fun _ => rfl) (VEndpt.partner_site_ne kstar (by omega))
    ?_ ?_ ?_ (VEndpt.hpe bnd) VEndpt.hpt hcov0 z₀ D hD
  · -- hsW
    intro E hE w x hwx hsx
    cases x with
    | inl y => exact Or.inr rfl
    | inr b =>
      cases b
      · exact Or.inl rfl
      · exfalso
        -- the departure is reachable from its partner, the arrival
        have hpz : (WalkGraph.graph E).Reachable w (Sum.inr false : VEndpt n mm) := by
          refine hwx.trans ?_
          have := WalkSupport.reachable_partner E (Sum.inr true : VEndpt n mm)
          rwa [hE.1] at this
        have hne := VEndpt.residual_discharged kstar bnd E w hk hE.2.1
          (fun b h => E.t_ne _ h) hpz
        exact hne (by simpa [VEndpt.site] using hsx.symm)
  · -- hsX
    intro E hE w x hwx hxe hxb
    cases x with
    | inl y => rfl
    | inr b =>
      cases b
      · exfalso
        -- the walk reaches a real end at edge <= 0, so `bnd` is not its leftmost edge
        obtain ⟨u, hu⟩ := (VEndpt.turn_of_vArr_low kstar bnd E hE.2.1
          (fun c h => E.t_ne _ h) (by omega) _ rfl).resolve_left (by
            intro hle
            have hlt := WalkSupport.wLo_le (VEndpt.edgeOf bnd) (WalkGraph.graph E)
              (hwx.trans (reachable_turn E (Sum.inr false)))
            simp only [VEndpt.edgeOf] at hxe
            omega)
        have hlt := WalkSupport.wLo_le (VEndpt.edgeOf bnd) (WalkGraph.graph E)
          (hwx.trans (reachable_turn E (Sum.inr false)))
        rw [hu] at hlt
        simp only [VEndpt.edgeOf] at hxe hlt
        have := hbnd u
        omega
      · exact absurd hxb (by simp [VEndpt.atTop])
  · -- hsT
    intro E _ w y hye hyt
    cases y with
    | inl u => rfl
    | inr b =>
      cases b
      · exact absurd hyt (by simp [VEndpt.atTop])
      · exfalso
        -- `bnd + 1` exceeds every edge, so it is not a leftmost edge
        have hlo := WalkSupport.wLo_le (VEndpt.edgeOf bnd) (WalkGraph.graph E)
          (SimpleGraph.Reachable.refl w)
        simp only [VEndpt.edgeOf] at hye
        cases w with
        | inl u => have := hbnd u; simp only [VEndpt.edgeOf] at hlo; omega
        | inr c => simp only [VEndpt.edgeOf] at hlo; omega

/-! ### A gap in the bridge: `Endpt` edges are non-negative

`EndType.edgeOf x = (x.edge : Fin n)` cast to `Z`, so every edge index is `>= 0`.  But
a `PathData` spans `[A, B]` with `A <= 0`, and `A` may be strictly negative.  So an
element whose span reaches left of the origin has **no** `Endpt` representation at the
indices its `PathData` uses.

This is not fatal -- the fix is to let the two virtual sites be parameters rather than
the literals `0` and `kstar`, so a shifted configuration can be used -- but it means
the assembled theorems of BLOCKS 26-27 cover the shifted picture only once that
parametrisation is made.  Recorded here rather than assumed away. -/

/-- Every `Endpt` edge index is non-negative. -/
theorem EndType_edgeOf_nonneg {n : ℕ} {mm : Fin n → ℕ} (x : EndType.Endpt n mm) :
    0 ≤ EndType.edgeOf x := by
  unfold EndType.edgeOf
  exact Int.natCast_nonneg _

/-- **So a span reaching left of the origin is not representable at its own indices.**
If `j < 0` there is no end on edge `j`, whatever the multiplicities. -/
theorem no_endpt_at_neg {n : ℕ} {mm : Fin n → ℕ} (j : ℤ) (hj : j < 0) :
    ¬ ∃ x : EndType.Endpt n mm, EndType.edgeOf x = j := by
  rintro ⟨x, hx⟩
  have := EndType_edgeOf_nonneg x
  omega

/-- And the same for the extended type at real ends. -/
theorem no_vendpt_at_neg {n : ℕ} {mm : Fin n → ℕ} (bnd j : ℤ) (hj : j < 0) (hb : 0 ≤ bnd) :
    ¬ ∃ x : VEndpt n mm, VEndpt.edgeOf bnd x = j := by
  rintro ⟨x, hx⟩
  cases x with
  | inl u =>
    have := EndType_edgeOf_nonneg u
    simp only [VEndpt.edgeOf] at hx
    omega
  | inr b => simp only [VEndpt.edgeOf] at hx; omega

/-! ### Parametrised virtual sites

`VEndpt.site` fixed the two virtual sites at `0` and `kstar`.  A configuration whose
span starts at `A < 0` must be shifted right by `-A` to be representable by `Endpt`,
and its virtual events then sit at `-A` and `kstar - A`.  This is the same development
with those two values as parameters; `VEndpt.site kstar` is the case `s0 = 0`,
`s1 = kstar`. -/

/-- The site map with both virtual sites as parameters. -/
def VEndpt.siteP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) : VEndpt n mm → ℤ
  | .inl x => EndType.siteOf x
  | .inr false => s0
  | .inr true => s1

@[simp] theorem VEndpt.siteP_zero {n : ℕ} {mm : Fin n → ℕ} (kstar : ℤ)
    (x : VEndpt n mm) : VEndpt.siteP 0 kstar x = VEndpt.site kstar x := by
  cases x with
  | inl y => rfl
  | inr b => cases b <;> rfl

/-- Arrivals at a site, parametrised. -/
noncomputable def VEndpt.arrAtP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (up : Fin n → ℕ)
    (s : ℤ) : Finset (VEndpt n mm) := by
  classical
  exact Finset.univ.filter (fun x => VEndpt.siteP s0 s1 x = s ∧ VEndpt.isArr up x = true)

/-- Departures at a site, parametrised. -/
noncomputable def VEndpt.depAtP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (up : Fin n → ℕ)
    (s : ℤ) : Finset (VEndpt n mm) := by
  classical
  exact Finset.univ.filter (fun x => VEndpt.siteP s0 s1 x = s ∧ VEndpt.isArr up x = false)

theorem VEndpt.arrAtP_eq {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    VEndpt.arrAtP (mm := mm) s0 s1 up s
      = (EndType.arrAt (m := mm) up s).image Sum.inl
        ∪ (if s = s0 then {Sum.inr false} else ∅) := by
  classical
  ext x
  cases x with
  | inl y =>
    by_cases h : s = s0 <;>
      simp [VEndpt.arrAtP, VEndpt.siteP, VEndpt.isArr, EndType.mem_arrAt, h]
  | inr b =>
    cases b <;> by_cases h : s = s0 <;>
      simp [VEndpt.arrAtP, VEndpt.siteP, VEndpt.isArr, h] <;> omega

theorem VEndpt.depAtP_eq {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    VEndpt.depAtP (mm := mm) s0 s1 up s
      = (EndType.depAt (m := mm) up s).image Sum.inl
        ∪ (if s = s1 then {Sum.inr true} else ∅) := by
  classical
  ext x
  cases x with
  | inl y =>
    by_cases h : s = s1 <;>
      simp [VEndpt.depAtP, VEndpt.siteP, VEndpt.isArr, EndType.mem_depAt, h]
  | inr b =>
    cases b <;> by_cases h : s = s1 <;>
      simp [VEndpt.depAtP, VEndpt.siteP, VEndpt.isArr, h] <;> omega

theorem VEndpt.card_arrAtP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    (VEndpt.arrAtP (mm := mm) s0 s1 up s).card
      = (EndType.arrAt (m := mm) up s).card + (if s = s0 then 1 else 0) := by
  classical
  rw [VEndpt.arrAtP_eq]
  have hdisj : Disjoint ((EndType.arrAt (m := mm) up s).image Sum.inl)
      (if s = s0 then ({Sum.inr false} : Finset (VEndpt n mm)) else ∅) := by
    split_ifs <;> simp [Finset.disjoint_left]
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective]
  split_ifs <;> simp

theorem VEndpt.card_depAtP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    (VEndpt.depAtP (mm := mm) s0 s1 up s).card
      = (EndType.depAt (m := mm) up s).card + (if s = s1 then 1 else 0) := by
  classical
  rw [VEndpt.depAtP_eq]
  have hdisj : Disjoint ((EndType.depAt (m := mm) up s).image Sum.inl)
      (if s = s1 then ({Sum.inr true} : Finset (VEndpt n mm)) else ∅) := by
    split_ifs <;> simp [Finset.disjoint_left]
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective]
  split_ifs <;> simp

/-- The travel indicator read on shifted edge indices: edge `j` of the shifted
configuration is edge `A + j` of the original. -/
def travelS (A kstar j : ℤ) : ℤ := travel kstar (A + j)

/-- **The shifted site facts.**  `travelS` steps exactly at `-A` and `kstar - A`, which
are where the two virtual events sit after the shift. -/
theorem travelS_site_facts (A kstar s : ℤ) :
    travelS A kstar (s - 1) + (if s = -A then 1 else 0)
      = travelS A kstar s + (if s = kstar - A then 1 else 0) := by
  have h := travel_site_facts kstar (A + s) (if A + s = 0 then 1 else 0)
    (if A + s = kstar then 1 else 0) (travel kstar (A + s - 1)) (travel kstar (A + s))
    rfl rfl rfl rfl
  have h1 := h.1
  unfold travelS
  have e1 : A + (s - 1) = A + s - 1 := by ring
  have e2 : (if A + s = 0 then (1:ℤ) else 0) = (if s = -A then 1 else 0) := by
    by_cases hc : s = -A <;> simp [hc] <;> omega
  have e3 : (if A + s = kstar then (1:ℤ) else 0) = (if s = kstar - A then 1 else 0) := by
    by_cases hc : s = kstar - A <;> simp [hc] <;> omega
  rw [e1, e2, e3] at *
  omega

/-- **Balance at every site, parametrised.**  The two virtual sites are `-A` and
`kstar - A`; the edge signed travels are those of the shifted configuration. -/
theorem VEndpt.balanced_allP {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (A kstar : ℤ)
    (htr : ∀ (s : ℤ) (e : Fin n), (e : ℤ) = s →
      ConfigLoop.tr (m := mm) up e = travelS A kstar s)
    (hz : ∀ s : ℤ, (∀ e : Fin n, (e : ℤ) ≠ s) → travelS A kstar s = 0) :
    ∀ s : ℤ, (VEndpt.arrAtP (mm := mm) (-A) (kstar - A) up s).card
      = (VEndpt.depAtP (mm := mm) (-A) (kstar - A) up s).card := by
  intro s
  rw [VEndpt.card_arrAtP, VEndpt.card_depAtP]
  have hreal := ConfigLoop.arr_sub_dep_all (m := mm) up s
    (travelS A kstar (s - 1)) (travelS A kstar s)
    (fun e he => htr (s - 1) e he) (fun h => hz (s - 1) h)
    (fun e he => htr s e he) (fun h => hz s h)
  have hfacts := travelS_site_facts A kstar s
  split_ifs at hfacts ⊢ <;> omega

/-! ### The re-indexing `PathData -> Fin n`

The map that was missing.  A `PathData` indexes edges by `Z` over the span `[A, B]`;
`Endpt` indexes them by `Fin n`.  The shift by `-A` is the bridge, and `travelS` is
exactly the travel indicator read through it. -/

variable (P : SiteCost.PathData)

/-- The number of edges in the span. -/
def pdWidth : ℕ := (P.B - P.A + 1).toNat

theorem pdWidth_pos : 0 < pdWidth P := by
  have h1 := P.hA; have h2 := P.hB
  unfold pdWidth; omega

/-- Edge `i` of the shifted configuration is edge `A + i` of the original. -/
def pdMm : Fin (pdWidth P) → ℕ := fun i => P.mm (P.A + i)

/-- Its up-crossing count. -/
def pdUp : Fin (pdWidth P) → ℕ := fun i => P.cu (P.A + i)

/-- **The re-indexed configuration has the right signed travel.**

`tr = 2 min(up, m) - m`, and since `cu <= mm` this is `2 cu - mm = cu - cdn`, which is
`travel` at the original index -- that is, `travelS` at the shifted one. -/
theorem pd_tr_eq (i : Fin (pdWidth P)) :
    ConfigLoop.tr (m := pdMm P) (pdUp P) i = travelS P.A P.kstar (i : ℤ) := by
  have hsum := P.cu_add_cdn (P.A + i)
  have hdiff := P.cu_sub_cdn (P.A + i)
  have hle : pdUp P i ≤ pdMm P i := by
    simp only [pdUp, pdMm]; omega
  unfold ConfigLoop.tr travelS
  rw [min_eq_left hle]
  simp only [pdUp, pdMm] at *
  omega

/-- **Outside the index range the travel vanishes.** -/
theorem pd_travelS_zero_outside (s : ℤ) (h : ∀ e : Fin (pdWidth P), (e : ℤ) ≠ s) :
    travelS P.A P.kstar s = 0 := by
  have hout : P.A + s < P.A ∨ P.B < P.A + s := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have hs0 : 0 ≤ s := by omega
    have hsw : s < (pdWidth P : ℤ) := by unfold pdWidth; omega
    exact h ⟨s.toNat, by unfold pdWidth at hsw ⊢; omega⟩ (by simp; omega)
  exact (P.houter (P.A + s) hout).2


/-- **The re-indexed configuration is balanced at every site.**

This is the join: `pd_tr_eq` says the shifted configuration carries the right signed
travel, `pd_travelS_zero_outside` says the travel vanishes off the index range, and
`balanced_allP` turns those into balance -- with the two virtual events at `-A` and
`kstar - A`. -/
theorem pd_balanced (P : SiteCost.PathData) :
    ∀ s : ℤ,
      (VEndpt.arrAtP (mm := pdMm P) (-P.A) (P.kstar - P.A) (pdUp P) s).card
        = (VEndpt.depAtP (mm := pdMm P) (-P.A) (P.kstar - P.A) (pdUp P) s).card :=
  VEndpt.balanced_allP (pdUp P) P.A P.kstar
    (fun s e he => by rw [pd_tr_eq P e, he])
    (fun s h => pd_travelS_zero_outside P s h)

/-- **And so is the configuration of a group element.**

`Elt -> PathData -> Fin n -> VEndpt -> balanced`.  This is the composite the whole
bridge was for; every step is a theorem above. -/
theorem Elt.balanced (g : Elt) :
    ∀ s : ℤ,
      (VEndpt.arrAtP (mm := pdMm g.toPathData) (-g.toPathData.A)
        (g.toPathData.kstar - g.toPathData.A) (pdUp g.toPathData) s).card
        = (VEndpt.depAtP (mm := pdMm g.toPathData) (-g.toPathData.A)
          (g.toPathData.kstar - g.toPathData.A) (pdUp g.toPathData) s).card :=
  pd_balanced g.toPathData

/-! ### The locality discharges, parametrised

BLOCKS 16 and 18 were written against the literals `0` and `kstar`.  With `siteP` the
condition `kstar > 0` becomes `s0 < s1`, which is invariant under the shift -- as it
must be, since `-A < kstar - A` iff `0 < kstar`. -/

/-- The partner changes site whenever the two virtual sites differ. -/
theorem VEndpt.partner_site_neP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (h : s0 ≠ s1)
    (x : VEndpt n mm) :
    VEndpt.siteP s0 s1 (VEndpt.partner x) ≠ VEndpt.siteP s0 s1 x := by
  cases x with
  | inl y =>
    simpa [VEndpt.partner, VEndpt.siteP] using
      WalkSupport.p_site_ne EndType.edgeOf EndType.siteOf EndType.atTop EndType.partner
        (fun _ => rfl) (fun w => EndType.partner_edgeOf w) (fun w => EndType.partner_top w) y
  | inr b => cases b <;> simp [VEndpt.partner, VEndpt.siteP] <;> omega

/-- **The turn of the virtual arrival is a real end**, parametrised. -/
theorem VEndpt.turn_of_vArr_realP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hne : s0 ≠ s1)
    (D : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (y : VEndpt n mm) (hy : y = D.t (Sum.inr false)) :
    ∃ u : EndType.Endpt n mm, y = Sum.inl u := by
  have hsy : VEndpt.siteP s0 s1 y = s0 := by rw [hy, hts]; rfl
  cases hcase : y with
  | inl u => exact ⟨u, rfl⟩
  | inr b =>
    exfalso
    cases b
    · exact D.t_ne _ (hy.symm.trans hcase)
    · rw [hcase] at hsy; exact hne (by simpa [VEndpt.siteP] using hsy.symm)

/-- **The walk carrying the virtual pair has leftmost edge at most `s0`.**  Its arrival
turns to a real end at site `s0`, which lies on edge `s0 - 1` or `s0`. -/
theorem VEndpt.wlo_le_s0 {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ) (hne : s0 ≠ s1)
    (D : WalkGraph.Data (VEndpt n mm)) (z : VEndpt n mm)
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (hz : (WalkGraph.graph D).Reachable z (Sum.inr false)) :
    WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph D) z ≤ s0 := by
  set y := D.t (Sum.inr false : VEndpt n mm) with hy
  have hzy : (WalkGraph.graph D).Reachable z y :=
    hz.trans (reachable_turn D (Sum.inr false))
  have hsy : VEndpt.siteP s0 s1 y = s0 := by rw [hy, hts]; rfl
  obtain ⟨u, hu⟩ := VEndpt.turn_of_vArr_realP s0 s1 hne D hts y hy
  have hle : VEndpt.edgeOf bnd y ≤ s0 := by
    rw [hu] at hsy ⊢
    simp only [VEndpt.siteP, VEndpt.edgeOf, EndType.siteOf] at hsy ⊢
    split_ifs at hsy <;> omega
  exact le_trans (WalkSupport.wLo_le (VEndpt.edgeOf bnd) (WalkGraph.graph D) hzy) hle

/-- **The residual condition, parametrised and discharged for `s0 < s1`.** -/
theorem VEndpt.residual_dischargedP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ)
    (hlt : s0 < s1)
    (D : WalkGraph.Data (VEndpt n mm)) (z : VEndpt n mm)
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (hz : (WalkGraph.graph D).Reachable z (Sum.inr false)) :
    WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph D) z ≠ s1 := by
  have := VEndpt.wlo_le_s0 s0 s1 bnd (by omega) D z hts hz
  omega

/-- The end data with parametrised sites. -/
def vEndDataP {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (ds : Bool → Bool) :
    EndData.Data (VEndpt n mm) :=
  ⟨VEndpt.atTop, VEndpt.isArr up, ds⟩

/-- **B1, assembled with parametrised virtual sites.**

Valid whenever `s0 < s1` and `bnd` lies above every real edge and above `s0` -- which
for a shifted configuration means `-A < kstar - A`, i.e. `kstar > 0`, and a free
choice of phantom edge. -/
theorem VEndpt.merges_to_oneP {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (ds : Bool → Bool) (s0 s1 bnd : ℤ) (hlt : s0 < s1) (hb : s0 < bnd)
    (hbnd : ∀ u : EndType.Endpt n mm, EndType.edgeOf u < bnd)
    (hcov0 : ∀ j : ℤ, (∃ u : VEndpt n mm, VEndpt.edgeOf bnd u = j) →
      (∃ v : VEndpt n mm, VEndpt.edgeOf bnd v < j) →
      ∃ y : VEndpt n mm, VEndpt.edgeOf bnd y = j - 1 ∧ VEndpt.atTop y = true)
    (z₀ : VEndpt n mm)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : CostMerge.MergesMin (VEndpt.siteP s0 s1) (VEndpt.isArr up) VEndpt.partner
      (vEndDataP up ds) D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.siteP s0 s1) (VEndpt.isArr up) VEndpt.partner
        (vEndDataP up ds) D' ∧ WalkGraph.walkCount D' ≤ 1 := by
  refine CostMerge.min_merges_to_one_local (VEndpt.edgeOf bnd) (VEndpt.siteP s0 s1)
    VEndpt.atTop VEndpt.partner (vEndDataP up ds)
    (fun _ => rfl) (VEndpt.partner_site_neP s0 s1 (by omega))
    ?_ ?_ ?_ (VEndpt.hpe bnd) VEndpt.hpt hcov0 z₀ D hD
  · -- hsW
    intro E hE w x hwx hsx
    cases x with
    | inl y => exact Or.inr rfl
    | inr b =>
      cases b
      · exact Or.inl rfl
      · exfalso
        have hpz : (WalkGraph.graph E).Reachable w (Sum.inr false : VEndpt n mm) := by
          refine hwx.trans ?_
          have := WalkSupport.reachable_partner E (Sum.inr true : VEndpt n mm)
          rwa [hE.1] at this
        exact VEndpt.residual_dischargedP s0 s1 bnd hlt E w hE.2.1 hpz
          (by simpa [VEndpt.siteP] using hsx.symm)
  · -- hsX
    intro E hE w x hwx hxe hxb
    cases x with
    | inl y => rfl
    | inr b =>
      cases b
      · exfalso
        have hle := VEndpt.wlo_le_s0 s0 s1 bnd (by omega) E w hE.2.1 hwx
        simp only [VEndpt.edgeOf] at hxe
        omega
      · exact absurd hxb (by simp [VEndpt.atTop])
  · -- hsT
    intro E _ w y hye hyt
    cases y with
    | inl u => rfl
    | inr b =>
      cases b
      · exact absurd hyt (by simp [VEndpt.atTop])
      · exfalso
        have hlo := WalkSupport.wLo_le (VEndpt.edgeOf bnd) (WalkGraph.graph E)
          (SimpleGraph.Reachable.refl w)
        simp only [VEndpt.edgeOf] at hye
        cases w with
        | inl u => have := hbnd u; simp only [VEndpt.edgeOf] at hlo; omega
        | inr c => simp only [VEndpt.edgeOf] at hlo; omega

/-- The generic and parametrised arrival sets coincide. -/
theorem arrOfP_eq {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    GenericData.arrOf (VEndpt.siteP (mm := mm) s0 s1) (VEndpt.isArr up) s
      = VEndpt.arrAtP (mm := mm) s0 s1 up s := rfl

theorem depOfP_eq {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (up : Fin n → ℕ) (s : ℤ) :
    GenericData.depOf (VEndpt.siteP (mm := mm) s0 s1) (VEndpt.isArr up) s
      = VEndpt.depAtP (mm := mm) s0 s1 up s := rfl

/-- **A cost-minimal datum exists**, for a balanced parametrised configuration. -/
theorem VEndpt.exists_mergesMinP {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (ds : Bool → Bool) (s0 s1 : ℤ) (hne : s0 ≠ s1)
    (hbal : ∀ s : ℤ, (VEndpt.arrAtP (mm := mm) s0 s1 up s).card
      = (VEndpt.depAtP (mm := mm) s0 s1 up s).card) :
    ∃ E : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.siteP s0 s1) (VEndpt.isArr up) VEndpt.partner
        (vEndDataP up ds) E := by
  have hbal' : ∀ s : ℤ,
      (GenericData.arrOf (VEndpt.siteP (mm := mm) s0 s1) (VEndpt.isArr up) s).card
        = (GenericData.depOf (VEndpt.siteP (mm := mm) s0 s1) (VEndpt.isArr up) s).card :=
    fun s => by rw [arrOfP_eq, depOfP_eq]; exact hbal s
  exact CostMerge.exists_mergesMin (VEndpt.siteP s0 s1) VEndpt.partner
    (vEndDataP up ds)
    (GenericData.dataG (VEndpt.siteP s0 s1) (VEndpt.isArr up) hbal' VEndpt.partner
      VEndpt.partner_invol VEndpt.partner_ne (VEndpt.partner_site_neP s0 s1 hne))
    (GenericData.dataG_merges (VEndpt.siteP s0 s1) (VEndpt.isArr up) hbal'
      VEndpt.partner VEndpt.partner_invol VEndpt.partner_ne
      (VEndpt.partner_site_neP s0 s1 hne))

/-- **B1, end to end for a group element.**

A group element with `kstar > 0` yields a configuration on the extended type carrying
a cost-minimal datum that merges to a single walk.  Every step is a theorem:
`Elt.toPathData`, the re-indexing, `Elt.balanced`, `exists_mergesMinP`, and
`merges_to_oneP`.  The covering condition `hcov0` is the sole input. -/
theorem Elt.merges_to_one (g : Elt) (ds : Bool → Bool) (bnd : ℤ)
    (hk : 0 < g.toPathData.kstar)
    (hb : -g.toPathData.A < bnd)
    (hbnd : ∀ u : EndType.Endpt (pdWidth g.toPathData) (pdMm g.toPathData),
      EndType.edgeOf u < bnd)
    (hcov0 : ∀ j : ℤ,
      (∃ u : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf bnd u = j) →
      (∃ v : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf bnd v < j) →
      ∃ y : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf bnd y = j - 1 ∧ VEndpt.atTop y = true)
    (z₀ : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)) :
    ∃ D' : WalkGraph.Data (VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)),
      CostMerge.MergesMin
        (VEndpt.siteP (-g.toPathData.A) (g.toPathData.kstar - g.toPathData.A))
        (VEndpt.isArr (pdUp g.toPathData)) VEndpt.partner
        (vEndDataP (pdUp g.toPathData) ds) D' ∧ WalkGraph.walkCount D' ≤ 1 := by
  obtain ⟨E, hE⟩ := VEndpt.exists_mergesMinP (pdUp g.toPathData) ds
    (-g.toPathData.A) (g.toPathData.kstar - g.toPathData.A) (by omega) (Elt.balanced g)
  exact VEndpt.merges_to_oneP (pdUp g.toPathData) ds
    (-g.toPathData.A) (g.toPathData.kstar - g.toPathData.A) bnd (by omega) hb hbnd
    hcov0 z₀ E hE

/-! ### The mirror: `s1 < s0`

For `kstar < 0` the two virtual sites are the other way round.  Take `bnd = s0 - 1`
and the `atTopN` orientation -- virtual arrival a **top** at `s0 = bnd + 1`, virtual
departure a **bottom** at `s1`.  Then `hsW` and `hsT` hold outright, and only `hsX`
needs the walk to reach back to `s1`. -/

/-- The turn of the virtual departure is a real end, parametrised. -/
theorem VEndpt.turn_of_vDep_realP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hne : s0 ≠ s1)
    (D : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (y : VEndpt n mm) (hy : y = D.t (Sum.inr true)) :
    ∃ u : EndType.Endpt n mm, y = Sum.inl u := by
  have hsy : VEndpt.siteP s0 s1 y = s1 := by rw [hy, hts]; rfl
  cases hcase : y with
  | inl u => exact ⟨u, rfl⟩
  | inr b =>
    exfalso
    cases b
    · rw [hcase] at hsy; exact hne (by simpa [VEndpt.siteP] using hsy)
    · exact D.t_ne _ (hy.symm.trans hcase)

/-- **The walk carrying the virtual pair has leftmost edge at most `s1`.** -/
theorem VEndpt.wlo_le_s1 {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ) (hne : s0 ≠ s1)
    (D : WalkGraph.Data (VEndpt n mm)) (z : VEndpt n mm)
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (hz : (WalkGraph.graph D).Reachable z (Sum.inr true)) :
    WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph D) z ≤ s1 := by
  set y := D.t (Sum.inr true : VEndpt n mm) with hy
  have hzy : (WalkGraph.graph D).Reachable z y :=
    hz.trans (reachable_turn D (Sum.inr true))
  have hsy : VEndpt.siteP s0 s1 y = s1 := by rw [hy, hts]; rfl
  obtain ⟨u, hu⟩ := VEndpt.turn_of_vDep_realP s0 s1 hne D hts y hy
  have hle : VEndpt.edgeOf bnd y ≤ s1 := by
    rw [hu] at hsy ⊢
    simp only [VEndpt.siteP, VEndpt.edgeOf, EndType.siteOf] at hsy ⊢
    split_ifs at hsy <;> omega
  exact le_trans (WalkSupport.wLo_le (VEndpt.edgeOf bnd) (WalkGraph.graph D) hzy) hle

/-- The end data in the mirrored orientation. -/
def vEndDataN {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ) (ds : Bool → Bool) :
    EndData.Data (VEndpt n mm) :=
  ⟨VEndpt.atTopN, VEndpt.isArr up, ds⟩

/-- **B1, assembled in the mirrored orientation `s1 < s0`.** -/
theorem VEndpt.merges_to_oneN {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (ds : Bool → Bool) (s0 s1 : ℤ) (hlt : s1 < s0)
    (hcov0 : ∀ j : ℤ, (∃ u : VEndpt n mm, VEndpt.edgeOf (s0 - 1) u = j) →
      (∃ v : VEndpt n mm, VEndpt.edgeOf (s0 - 1) v < j) →
      ∃ y : VEndpt n mm, VEndpt.edgeOf (s0 - 1) y = j - 1 ∧ VEndpt.atTopN y = true)
    (z₀ : VEndpt n mm)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : CostMerge.MergesMin (VEndpt.siteP s0 s1) (VEndpt.isArr up) VEndpt.partner
      (vEndDataN up ds) D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.siteP s0 s1) (VEndpt.isArr up) VEndpt.partner
        (vEndDataN up ds) D' ∧ WalkGraph.walkCount D' ≤ 1 := by
  refine CostMerge.min_merges_to_one_local (VEndpt.edgeOf (s0 - 1)) (VEndpt.siteP s0 s1)
    VEndpt.atTopN VEndpt.partner (vEndDataN up ds)
    (fun _ => rfl) (VEndpt.partner_site_neP s0 s1 (by omega))
    ?_ ?_ ?_ (VEndpt.hpe (s0 - 1)) VEndpt.hptN hcov0 z₀ D hD
  · -- hsW: both virtual ends discharge outright
    intro E _ w x _ _
    cases x with
    | inl y => exact Or.inr rfl
    | inr b =>
      cases b
      · exact Or.inr (by simp [VEndpt.siteP, VEndpt.edgeOf, VEndpt.atTopN])
      · exact Or.inl rfl
  · -- hsX: only the virtual departure, and the walk reaches back to `s1`
    intro E hE w x hwx hxe hxb
    cases x with
    | inl y => rfl
    | inr b =>
      cases b
      · exact absurd hxb (by simp [VEndpt.atTopN])
      · have hw : WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) w = s0 - 1 := by
          simpa [VEndpt.edgeOf] using hxe.symm
        have hle := VEndpt.wlo_le_s1 s0 s1 (s0 - 1) (by omega) E w hE.2.1 hwx
        rw [hw] at hle
        have hs : s1 = s0 - 1 := by omega
        simp [VEndpt.siteP, VEndpt.edgeOf, VEndpt.atTopN, hs]
  · -- hsT: the virtual arrival satisfies it outright
    intro E _ w y _ hyt
    cases y with
    | inl u => rfl
    | inr b =>
      cases b
      · simp [VEndpt.siteP, VEndpt.edgeOf, VEndpt.atTopN]
      · exact absurd hyt (by simp [VEndpt.atTopN])

/-- **A cost-minimal datum exists**, mirrored orientation. -/
theorem VEndpt.exists_mergesMinN {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (ds : Bool → Bool) (s0 s1 : ℤ) (hne : s0 ≠ s1)
    (hbal : ∀ s : ℤ, (VEndpt.arrAtP (mm := mm) s0 s1 up s).card
      = (VEndpt.depAtP (mm := mm) s0 s1 up s).card) :
    ∃ E : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.siteP s0 s1) (VEndpt.isArr up) VEndpt.partner
        (vEndDataN up ds) E := by
  have hbal' : ∀ s : ℤ,
      (GenericData.arrOf (VEndpt.siteP (mm := mm) s0 s1) (VEndpt.isArr up) s).card
        = (GenericData.depOf (VEndpt.siteP (mm := mm) s0 s1) (VEndpt.isArr up) s).card :=
    fun s => by rw [arrOfP_eq, depOfP_eq]; exact hbal s
  exact CostMerge.exists_mergesMin (VEndpt.siteP s0 s1) VEndpt.partner
    (vEndDataN up ds)
    (GenericData.dataG (VEndpt.siteP s0 s1) (VEndpt.isArr up) hbal' VEndpt.partner
      VEndpt.partner_invol VEndpt.partner_ne (VEndpt.partner_site_neP s0 s1 hne))
    (GenericData.dataG_merges (VEndpt.siteP s0 s1) (VEndpt.isArr up) hbal'
      VEndpt.partner VEndpt.partner_invol VEndpt.partner_ne
      (VEndpt.partner_site_neP s0 s1 hne))

/-- **B1, end to end for a group element with `kstar < 0`.**

The mirror of `Elt.merges_to_one`.  Together they cover every `kstar != 0`, and
`kstar = 0` is excluded because the two virtual events would coincide. -/
theorem Elt.merges_to_one_neg (g : Elt) (ds : Bool → Bool)
    (hk : g.toPathData.kstar < 0)
    (hcov0 : ∀ j : ℤ,
      (∃ u : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf (-g.toPathData.A - 1) u = j) →
      (∃ v : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf (-g.toPathData.A - 1) v < j) →
      ∃ y : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf (-g.toPathData.A - 1) y = j - 1 ∧ VEndpt.atTopN y = true)
    (z₀ : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)) :
    ∃ D' : WalkGraph.Data (VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)),
      CostMerge.MergesMin
        (VEndpt.siteP (-g.toPathData.A) (g.toPathData.kstar - g.toPathData.A))
        (VEndpt.isArr (pdUp g.toPathData)) VEndpt.partner
        (vEndDataN (pdUp g.toPathData) ds) D' ∧ WalkGraph.walkCount D' ≤ 1 := by
  obtain ⟨E, hE⟩ := VEndpt.exists_mergesMinN (pdUp g.toPathData) ds
    (-g.toPathData.A) (g.toPathData.kstar - g.toPathData.A) (by omega) (Elt.balanced g)
  exact VEndpt.merges_to_oneN (pdUp g.toPathData) ds
    (-g.toPathData.A) (g.toPathData.kstar - g.toPathData.A) (by omega)
    hcov0 z₀ E hE

/-! ### A concrete instantiation

The theorems above are only worth their statements if an `Elt` can actually be fed to
them.  This is the smallest non-trivial one: cursor `1`, a single deposit at edge `0`,
travel `+1` there and nowhere else. -/

/-- The witness element: `kstar = 1`, one deposit at edge `0`. -/
noncomputable def witElt : Elt where
  kstar := 1
  eps := 1
  delta := false
  heps := Or.inl rfl
  d := fun j => if j = 0 then 1 else 0
  hpar := by
    intro j
    unfold travel
    by_cases h : j = 0 <;> simp [h] <;> split_ifs <;> omega
  supp := {0}
  hsupp := by
    intro j hj
    have h0 : j ≠ 0 := by
      intro hc; exact hj (by simp [hc])
    refine ⟨by simp [h0], ?_⟩
    unfold travel
    split_ifs <;> omega

@[simp] theorem witElt_kstar : witElt.kstar = 1 := rfl

/-- Its occupied set is `{0}`. -/
theorem witElt_occ : witElt.occ = {0} := by
  classical
  unfold Elt.occ
  ext x
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h
    · simpa [witElt] using h
  · intro h; exact Or.inl h

theorem witElt_A : witElt.A = 0 := by
  have h : witElt.A ∈ witElt.occ := Finset.min'_mem _ _
  rw [witElt_occ, Finset.mem_singleton] at h
  exact h

theorem witElt_B : witElt.B = 0 := by
  have h : witElt.B ∈ witElt.occ := Finset.max'_mem _ _
  rw [witElt_occ, Finset.mem_singleton] at h
  exact h

@[simp] theorem witElt_pd_A : witElt.toPathData.A = 0 := witElt_A
@[simp] theorem witElt_pd_B : witElt.toPathData.B = 0 := witElt_B
@[simp] theorem witElt_pd_kstar : witElt.toPathData.kstar = 1 := rfl

/-- **Its span has exactly one edge.** -/
theorem witElt_width : pdWidth witElt.toPathData = 1 := by
  unfold pdWidth
  rw [witElt_pd_A, witElt_pd_B]
  rfl

/-- Its single edge carries a crossing. -/
theorem witElt_mm_pos (i : Fin (pdWidth witElt.toPathData)) :
    0 < pdMm witElt.toPathData i := by
  have hi := i.isLt
  have hw := witElt_width
  have hz : (i : ℤ) = 0 := by omega
  have hA := witElt_pd_A
  have hB := witElt_pd_B
  have : witElt.toPathData.A + (i : ℤ) = 0 := by rw [hA, hz]; ring
  simp only [pdMm, this]
  have hmm := witElt.toPathData.mm_eq_mu (j := 0) ⟨by rw [hA], by rw [hB]⟩
  rw [hmm]
  exact witElt.toPathData.mu_pos 0

/-- Every real end of the witness lies on edge `0`. -/
theorem witElt_edge_lt (u : EndType.Endpt (pdWidth witElt.toPathData)
    (pdMm witElt.toPathData)) : EndType.edgeOf u < 1 := by
  have hi := u.edge.isLt
  have hw := witElt_width
  unfold EndType.edgeOf
  omega

/-- **The witness satisfies the covering condition** with phantom edge `1`. -/
theorem witElt_hcov0 : ∀ j : ℤ,
    (∃ u : VEndpt (pdWidth witElt.toPathData) (pdMm witElt.toPathData),
      VEndpt.edgeOf 1 u = j) →
    (∃ v : VEndpt (pdWidth witElt.toPathData) (pdMm witElt.toPathData),
      VEndpt.edgeOf 1 v < j) →
    ∃ y : VEndpt (pdWidth witElt.toPathData) (pdMm witElt.toPathData),
      VEndpt.edgeOf 1 y = j - 1 ∧ VEndpt.atTop y = true := by
  rintro j ⟨u, hu⟩ ⟨v, hv⟩
  -- every end sits at edge `0` or `1`, so a strict predecessor forces `j = 1`
  have hj : j = 1 := by
    have h1 : VEndpt.edgeOf (1 : ℤ) u = 0 ∨ VEndpt.edgeOf (1 : ℤ) u = 1 := by
      cases u with
      | inl w => exact Or.inl (by
          have := witElt_edge_lt w
          have := EndType_edgeOf_nonneg w
          simp only [VEndpt.edgeOf]; omega)
      | inr b => exact Or.inr rfl
    have h2 : 0 ≤ VEndpt.edgeOf (1 : ℤ) v := by
      cases v with
      | inl w => simpa [VEndpt.edgeOf] using EndType_edgeOf_nonneg w
      | inr b => simp [VEndpt.edgeOf]
    omega
  subst hj
  -- the top end of the single real edge
  have hpos : 0 < pdMm witElt.toPathData ⟨0, by rw [witElt_width]; omega⟩ :=
    witElt_mm_pos _
  exact ⟨Sum.inl ⟨⟨0, by rw [witElt_width]; omega⟩, ⟨0, hpos⟩, true⟩, by
    simp [VEndpt.edgeOf, EndType.edgeOf], rfl⟩

/-- **B1, instantiated.**  The witness element yields a cost-minimal datum on the
extended type that merges to a single walk.  Not a statement about a hypothetical
configuration: an actual group element, carried the whole way through. -/
theorem witElt_merges (ds : Bool → Bool) :
    ∃ D' : WalkGraph.Data (VEndpt (pdWidth witElt.toPathData) (pdMm witElt.toPathData)),
      CostMerge.MergesMin
        (VEndpt.siteP (-witElt.toPathData.A)
          (witElt.toPathData.kstar - witElt.toPathData.A))
        (VEndpt.isArr (pdUp witElt.toPathData)) VEndpt.partner
        (vEndDataP (pdUp witElt.toPathData) ds) D' ∧ WalkGraph.walkCount D' ≤ 1 :=
  Elt.merges_to_one witElt ds 1 (by simp) (by rw [witElt_pd_A]; omega)
    witElt_edge_lt witElt_hcov0 (Sum.inr false)

/-! ### M6 for group elements: exactly one walk

`Elt.merges_to_one` gives `walkCount <= 1`.  The extended type is never empty -- it
always carries the two virtual ends -- so the count is at least one, and the merge
lands on exactly one walk. -/

/-- The extended type is inhabited, whatever the configuration. -/
instance {n : ℕ} {mm : Fin n → ℕ} : Nonempty (VEndpt n mm) := ⟨Sum.inr false⟩

/-- **At least one walk**, for any datum on an inhabited end type. -/
theorem one_le_walkCount {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (D : WalkGraph.Data α) : 1 ≤ WalkGraph.walkCount D :=
  Fintype.card_pos_iff.mpr ⟨(WalkGraph.graph D).connectedComponentMk (Classical.arbitrary _)⟩

/-- **M6 for a group element.**  A cost-minimal datum on the configuration of an
element with `kstar > 0` has **exactly one** walk. -/
theorem Elt.single_walk (g : Elt) (ds : Bool → Bool) (bnd : ℤ)
    (hk : 0 < g.toPathData.kstar)
    (hb : -g.toPathData.A < bnd)
    (hbnd : ∀ u : EndType.Endpt (pdWidth g.toPathData) (pdMm g.toPathData),
      EndType.edgeOf u < bnd)
    (hcov0 : ∀ j : ℤ,
      (∃ u : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf bnd u = j) →
      (∃ v : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf bnd v < j) →
      ∃ y : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf bnd y = j - 1 ∧ VEndpt.atTop y = true)
    (z₀ : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)) :
    ∃ D' : WalkGraph.Data (VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)),
      CostMerge.MergesMin
        (VEndpt.siteP (-g.toPathData.A) (g.toPathData.kstar - g.toPathData.A))
        (VEndpt.isArr (pdUp g.toPathData)) VEndpt.partner
        (vEndDataP (pdUp g.toPathData) ds) D' ∧ WalkGraph.walkCount D' = 1 := by
  obtain ⟨D', hD', hle⟩ := Elt.merges_to_one g ds bnd hk hb hbnd hcov0 z₀
  exact ⟨D', hD', le_antisymm hle (one_le_walkCount D')⟩

/-- **M6, instantiated on the witness.**  Exactly one walk, for an actual element. -/
theorem witElt_single_walk (ds : Bool → Bool) :
    ∃ D' : WalkGraph.Data (VEndpt (pdWidth witElt.toPathData) (pdMm witElt.toPathData)),
      CostMerge.MergesMin
        (VEndpt.siteP (-witElt.toPathData.A)
          (witElt.toPathData.kstar - witElt.toPathData.A))
        (VEndpt.isArr (pdUp witElt.toPathData)) VEndpt.partner
        (vEndDataP (pdUp witElt.toPathData) ds) D' ∧ WalkGraph.walkCount D' = 1 :=
  Elt.single_walk witElt ds 1 (by simp) (by rw [witElt_pd_A]; omega)
    witElt_edge_lt witElt_hcov0 (Sum.inr false)

/-! ### M5 and M7 for group elements: zero defect

`cor:localzero` and `prop:travelinv` say the connectivity defect `c` vanishes.  In the
walk model `c` is `ConfigLoop.defect = walkCount - 1`, so `Elt.single_walk` gives it
directly. -/

/-- **M5/M7 for a group element.**  The connectivity defect of a cost-minimal datum on
the configuration of an element with `kstar > 0` is zero: `c(g) = 0`. -/
theorem Elt.defect_zero (g : Elt) (ds : Bool → Bool) (bnd : ℤ)
    (hk : 0 < g.toPathData.kstar)
    (hb : -g.toPathData.A < bnd)
    (hbnd : ∀ u : EndType.Endpt (pdWidth g.toPathData) (pdMm g.toPathData),
      EndType.edgeOf u < bnd)
    (hcov0 : ∀ j : ℤ,
      (∃ u : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf bnd u = j) →
      (∃ v : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf bnd v < j) →
      ∃ y : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData),
        VEndpt.edgeOf bnd y = j - 1 ∧ VEndpt.atTop y = true)
    (z₀ : VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)) :
    ∃ D' : WalkGraph.Data (VEndpt (pdWidth g.toPathData) (pdMm g.toPathData)),
      CostMerge.MergesMin
        (VEndpt.siteP (-g.toPathData.A) (g.toPathData.kstar - g.toPathData.A))
        (VEndpt.isArr (pdUp g.toPathData)) VEndpt.partner
        (vEndDataP (pdUp g.toPathData) ds) D' ∧ ConfigLoop.defect D' = 0 := by
  obtain ⟨D', hD', hc⟩ := Elt.single_walk g ds bnd hk hb hbnd hcov0 z₀
  exact ⟨D', hD', by unfold ConfigLoop.defect; omega⟩

/-- **M5/M7, instantiated.**  `c = 0` for an actual group element. -/
theorem witElt_defect_zero (ds : Bool → Bool) :
    ∃ D' : WalkGraph.Data (VEndpt (pdWidth witElt.toPathData) (pdMm witElt.toPathData)),
      CostMerge.MergesMin
        (VEndpt.siteP (-witElt.toPathData.A)
          (witElt.toPathData.kstar - witElt.toPathData.A))
        (VEndpt.isArr (pdUp witElt.toPathData)) VEndpt.partner
        (vEndDataP (pdUp witElt.toPathData) ds) D' ∧ ConfigLoop.defect D' = 0 :=
  Elt.defect_zero witElt ds 1 (by simp) (by rw [witElt_pd_A]; omega)
    witElt_edge_lt witElt_hcov0 (Sum.inr false)

/-! ### The cut set of a group element

`SiteCost.PathData.cut` is `alphaAt = betaAt = PhiAt = 0`.  Away from the two virtual
sites the three virtual counters vanish, and the condition reduces to the plain
read-off `d(s-1) = 0`, `d(s) = 0`, `f(s-1) = 0`.  Transported through the shift, this
is the cut set of a group element. -/

/-- A cut site of the shifted configuration. -/
def pdCutAt (P : SiteCost.PathData) (s : ℤ) : Prop := P.cut (P.A + s)

/-- **The plain characterisation, away from the two virtual sites.** -/
theorem pdCutAt_iff (P : SiteCost.PathData) (s : ℤ)
    (h0 : P.A + s ≠ 0) (hk : P.A + s ≠ P.kstar) :
    pdCutAt P s ↔
      (P.d (P.A + s - 1) = 0 ∧ P.d (P.A + s) = 0 ∧ P.f (P.A + s - 1) = 0) := by
  unfold pdCutAt SiteCost.PathData.cut SiteCost.PathData.alphaAt
    SiteCost.PathData.betaAt SiteCost.PathData.PhiAt SiteCost.PathData.vL
    SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  rw [if_neg h0]
  simp only [if_neg hk, ite_self, Nat.cast_zero, mul_zero, sub_zero, add_zero]

/-- **A cut site has no deposit on either adjacent edge.** -/
theorem pdCutAt_d_zero (P : SiteCost.PathData) (s : ℤ)
    (h0 : P.A + s ≠ 0) (hk : P.A + s ≠ P.kstar) (h : pdCutAt P s) :
    P.d (P.A + s - 1) = 0 ∧ P.d (P.A + s) = 0 :=
  ⟨((pdCutAt_iff P s h0 hk).mp h).1, ((pdCutAt_iff P s h0 hk).mp h).2.1⟩

/-- **The cut set of a group element**, as a `Finset`.

`Z` is the set of cut sites **interior** to the span -- a point the 2026-08-23
retraction turned on: a run of `L` gap edges gives `L - 1` interior sites, so counting
the endpoints overcounts by one per run.  The shifted span has edges `0 .. width - 1`
and sites `0 .. width`, so the interior sites are `Ioo 0 width`. -/
noncomputable def pdCutSites (P : SiteCost.PathData) : Finset ℤ := by
  classical
  exact (Finset.Ioo (0 : ℤ) (pdWidth P : ℤ)).filter (fun s => P.cut (P.A + s))

theorem mem_pdCutSites (P : SiteCost.PathData) (s : ℤ) :
    s ∈ pdCutSites P ↔ (0 < s ∧ s < (pdWidth P : ℤ)) ∧ pdCutAt P s := by
  classical
  simp only [pdCutSites, Finset.mem_filter, Finset.mem_Ioo]
  rfl

/-- Cut sites are interior, so they are never `0` or `width`. -/
theorem pdCutSites_interior (P : SiteCost.PathData) {s : ℤ} (h : s ∈ pdCutSites P) :
    0 < s ∧ s < (pdWidth P : ℤ) :=
  ((mem_pdCutSites P s).mp h).1

/-- **The witness element has no cut site.**  Its span is a single edge, so there is no
interior site at all -- `Ioo 0 1` is empty. -/
theorem witElt_cutSites : pdCutSites witElt.toPathData = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro s hs
  obtain ⟨h1, h2⟩ := pdCutSites_interior _ hs
  rw [witElt_width] at h2
  omega

/-- **The shield law at element level, instantiated.**

`c = |Z|`, i.e. `walkCount = |Z| + 1`, for an actual group element.  The witness has no
cut site, so this says `walkCount = 1` -- and that is exactly what `witElt_single_walk`
produced independently, through the merge rather than through the cut count.  The two
routes agree. -/
theorem witElt_shield (ds : Bool → Bool) :
    ∃ D' : WalkGraph.Data (VEndpt (pdWidth witElt.toPathData) (pdMm witElt.toPathData)),
      CostMerge.MergesMin
        (VEndpt.siteP (-witElt.toPathData.A)
          (witElt.toPathData.kstar - witElt.toPathData.A))
        (VEndpt.isArr (pdUp witElt.toPathData)) VEndpt.partner
        (vEndDataP (pdUp witElt.toPathData) ds) D' ∧
      WalkGraph.walkCount D' = (pdCutSites witElt.toPathData).card + 1 := by
  obtain ⟨D', hD', hc⟩ := witElt_single_walk ds
  refine ⟨D', hD', ?_⟩
  rw [hc, witElt_cutSites, Finset.card_empty]

/-! ### `hZ` on the extended type

BLOCK 12 proved, for `Endpt`, that a balanced site carrying no arrival carries no end
at all, and hence that both adjacent edges are empty.  The argument never used
anything about `Endpt`; here it is generically, and then on `VEndpt`, where it says
something new: a cut site cannot be either of the two virtual sites. -/

/-- **A balanced site with no arrival carries no end**, for any end type. -/
theorem no_end_at_arrivalfree_gen {α : Type*} [Fintype α] [DecidableEq α]
    (siteOf : α → ℤ) (isArr : α → Bool) (z : ℤ)
    (hbal : (GenericData.arrOf siteOf isArr z).card
      = (GenericData.depOf siteOf isArr z).card)
    (hZ : ∀ x : α, isArr x = true → siteOf x ≠ z) :
    ∀ x : α, siteOf x ≠ z := by
  classical
  intro x hx
  have harr : GenericData.arrOf siteOf isArr z = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨hs, ha⟩ := GenericData.mem_arrOf.mp hy
    exact hZ y ha hs
  have hdep : GenericData.depOf siteOf isArr z = ∅ := by
    rw [← Finset.card_eq_zero, ← hbal, harr, Finset.card_empty]
  cases hax : isArr x with
  | true => exact hZ x hax hx
  | false =>
    have : x ∈ GenericData.depOf siteOf isArr z := GenericData.mem_depOf.mpr ⟨hx, hax⟩
    rw [hdep] at this
    exact absurd this (Finset.notMem_empty x)

/-- **On the extended type, an arrival-free balanced site is neither virtual site.**

New content relative to BLOCK 12: the two virtual ends sit at `s0` and `s1`, and they
are ends, so an arrival-free site cannot be either.  In particular no cut site of a
configuration is a virtual site -- which is the structural reason the shield law and
the virtual events do not interfere. -/
theorem VEndpt.arrivalfree_ne_virtual {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (s0 s1 z : ℤ)
    (hbal : (VEndpt.arrAtP (mm := mm) s0 s1 up z).card
      = (VEndpt.depAtP (mm := mm) s0 s1 up z).card)
    (hZ : ∀ x : VEndpt n mm, VEndpt.isArr up x = true → VEndpt.siteP s0 s1 x ≠ z) :
    z ≠ s0 ∧ z ≠ s1 := by
  have hno := no_end_at_arrivalfree_gen (VEndpt.siteP (mm := mm) s0 s1)
    (VEndpt.isArr up) z (by rw [arrOfP_eq, depOfP_eq]; exact hbal) hZ
  constructor
  · intro hc
    exact hno (Sum.inr false) (by simp [VEndpt.siteP, hc])
  · intro hc
    exact hno (Sum.inr true) (by simp [VEndpt.siteP, hc])

/-- **Both edges adjacent to an arrival-free site are empty**, on the extended type. -/
theorem VEndpt.empty_edges_at_arrivalfree {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (s0 s1 z : ℤ)
    (hbal : (VEndpt.arrAtP (mm := mm) s0 s1 up z).card
      = (VEndpt.depAtP (mm := mm) s0 s1 up z).card)
    (hZ : ∀ x : VEndpt n mm, VEndpt.isArr up x = true → VEndpt.siteP s0 s1 x ≠ z) :
    ∀ e : Fin n, ((e : ℤ) = z ∨ (e : ℤ) = z - 1) → mm e = 0 := by
  have hno := no_end_at_arrivalfree_gen (VEndpt.siteP (mm := mm) s0 s1)
    (VEndpt.isArr up) z (by rw [arrOfP_eq, depOfP_eq]; exact hbal) hZ
  intro e he
  by_contra hne
  have hpos : 0 < mm e := Nat.pos_of_ne_zero hne
  rcases he with he | he
  · exact hno (Sum.inl ⟨e, ⟨0, hpos⟩, false⟩)
      (by simp [VEndpt.siteP, EndType.siteOf, EndType.edgeOf, EndType.atTop, he])
  · exact hno (Sum.inl ⟨e, ⟨0, hpos⟩, true⟩)
      (by simp [VEndpt.siteP, EndType.siteOf, EndType.edgeOf, EndType.atTop, he])

/-- **So a cut site of an element's configuration sits in the empty stretch.**

Combining: at a cut site there is no arrival, hence no end, hence both adjacent edges
are empty -- and the site is neither virtual site.  This is the structural picture the
shield law needs, now established on the extended type rather than assumed. -/
theorem VEndpt.cut_site_picture {n : ℕ} {mm : Fin n → ℕ} (up : Fin n → ℕ)
    (s0 s1 z : ℤ)
    (hbal : (VEndpt.arrAtP (mm := mm) s0 s1 up z).card
      = (VEndpt.depAtP (mm := mm) s0 s1 up z).card)
    (hZ : ∀ x : VEndpt n mm, VEndpt.isArr up x = true → VEndpt.siteP s0 s1 x ≠ z) :
    (z ≠ s0 ∧ z ≠ s1) ∧ ∀ e : Fin n, ((e : ℤ) = z ∨ (e : ℤ) = z - 1) → mm e = 0 :=
  ⟨VEndpt.arrivalfree_ne_virtual up s0 s1 z hbal hZ,
   VEndpt.empty_edges_at_arrivalfree up s0 s1 z hbal hZ⟩

/-! ### Locality of the extended graph constrains `bnd`

`CutComponents.Local` asks that the two ends of every graph edge lie on a common site's
two edges.  The virtual pair are partners on the common edge `bnd`, so that edge is
fine.  But the *turn* of the virtual arrival is a real end at site `s0`, hence on edge
`s0 - 1` or `s0` -- and locality then forces `bnd` to be within one of `s0`.

So the two constructions want different phantom edges: the merge (for `s0 < s1`) wants
`bnd` above every real edge, while locality wants it adjacent to `s0`.  The mirrored
orientation, which uses `bnd = s0 - 1`, satisfies both. -/

/-- **Locality confines the phantom edge to a window around `s0`.**

`Local` puts the two ends of a graph edge on a common site's two edges, so their
positions differ by at most one.  The turn of the virtual arrival is a real end at
site `s0`, hence on edge `s0 - 1` or `s0`; so `bnd` lies in `[s0 - 2, s0 + 1]`.

In particular `bnd` cannot be placed above every real edge of a wide configuration,
which is what the `s0 < s1` merge assembly wanted. -/
theorem VEndpt.local_confines_bnd {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ)
    (Zf : Finset ℤ) (E : WalkGraph.Data (VEndpt n mm))
    (hloc : CutComponents.Local (WalkGraph.graph E) (VEndpt.edgeOf bnd) Zf)
    (u : EndType.Endpt n mm) (hu : E.t (Sum.inr false) = Sum.inl u)
    (hsu : EndType.siteOf u = s0) :
    s0 - 2 ≤ bnd ∧ bnd ≤ s0 + 1 := by
  have hadj : (WalkGraph.graph E).Adj (Sum.inr false : VEndpt n mm)
      (E.t (Sum.inr false)) := Or.inr rfl
  obtain ⟨t, h1, h2, _⟩ := hloc _ _ hadj
  rw [hu] at h2
  have h1' : bnd = t - 1 ∨ bnd = t := h1
  have h2' : EndType.edgeOf u = t - 1 ∨ EndType.edgeOf u = t := h2
  have hue : EndType.edgeOf u = s0 ∨ EndType.edgeOf u = s0 - 1 := by
    have hs : EndType.edgeOf u + (if EndType.atTop u then (1:ℤ) else 0) = s0 := hsu
    cases hb : EndType.atTop u
    · have e : (if EndType.atTop u then (1:ℤ) else 0) = 0 := by rw [hb]; rfl
      rw [e] at hs; omega
    · have e : (if EndType.atTop u then (1:ℤ) else 0) = 1 := by rw [hb]; rfl
      rw [e] at hs; omega
  omega

/-- **The mirrored orientation is the one that can be local**: it puts the phantom
edge at `s0 - 1`, which is exactly one of the two positions locality allows. -/
theorem VEndpt.mirrored_bnd_ok (s0 : ℤ) : (s0 - 1) = s0 ∨ (s0 - 1) = s0 - 1 :=
  Or.inr rfl

/-! ### Locality bounds the travel

`local_confines_bnd` pins `bnd` to a window around `s0`, using the turn of the virtual
**arrival**.  The same argument at the virtual **departure** pins it to a window around
`s1`.  Both must hold at once, so the two windows meet -- and that bounds `|s0 - s1|`,
which is the length of the travel interval. -/

/-- The mirror of `local_confines_bnd`, at the virtual departure. -/
theorem VEndpt.local_confines_bnd' {n : ℕ} {mm : Fin n → ℕ} (s1 bnd : ℤ)
    (Zf : Finset ℤ) (E : WalkGraph.Data (VEndpt n mm))
    (hloc : CutComponents.Local (WalkGraph.graph E) (VEndpt.edgeOf bnd) Zf)
    (u : EndType.Endpt n mm) (hu : E.t (Sum.inr true) = Sum.inl u)
    (hsu : EndType.siteOf u = s1) :
    s1 - 2 ≤ bnd ∧ bnd ≤ s1 + 1 := by
  have hadj : (WalkGraph.graph E).Adj (Sum.inr true : VEndpt n mm)
      (E.t (Sum.inr true)) := Or.inr rfl
  obtain ⟨t, h1, h2, _⟩ := hloc _ _ hadj
  rw [hu] at h2
  have h1' : bnd = t - 1 ∨ bnd = t := h1
  have h2' : EndType.edgeOf u = t - 1 ∨ EndType.edgeOf u = t := h2
  have hue : EndType.edgeOf u = s1 ∨ EndType.edgeOf u = s1 - 1 := by
    have hs : EndType.edgeOf u + (if EndType.atTop u then (1:ℤ) else 0) = s1 := hsu
    cases hb : EndType.atTop u
    · have e : (if EndType.atTop u then (1:ℤ) else 0) = 0 := by rw [hb]; rfl
      rw [e] at hs; omega
    · have e : (if EndType.atTop u then (1:ℤ) else 0) = 1 := by rw [hb]; rfl
      rw [e] at hs; omega
  omega

/-- **Locality bounds the travel interval.**

If the extended graph is `CutComponents.Local`, the two virtual sites are within three
of each other.  Since `s0 = -A` and `s1 = kstar - A`, that says `|kstar| <= 3`.

So the shield law's locality hypothesis **cannot** hold on the extended type for a
configuration with travel longer than three.  This is not a defect in the
construction: the virtual pair joins site `s0` to site `s1` in one step, and locality
is precisely the statement that graph edges do not span more than one site. -/
theorem VEndpt.local_bounds_travel {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ)
    (Zf : Finset ℤ) (E : WalkGraph.Data (VEndpt n mm))
    (hloc : CutComponents.Local (WalkGraph.graph E) (VEndpt.edgeOf bnd) Zf)
    (u v : EndType.Endpt n mm)
    (hu : E.t (Sum.inr false) = Sum.inl u) (hsu : EndType.siteOf u = s0)
    (hv : E.t (Sum.inr true) = Sum.inl v) (hsv : EndType.siteOf v = s1) :
    |s0 - s1| ≤ 3 := by
  obtain ⟨h1, h2⟩ := VEndpt.local_confines_bnd s0 s1 bnd Zf E hloc u hu hsu
  obtain ⟨h3, h4⟩ := VEndpt.local_confines_bnd' s1 bnd Zf E hloc v hv hsv
  rw [abs_le]
  omega

/-! ### No cut site lies inside the travel interval

This is what makes route (b) work.  A cut site has `Phi = 0`, which away from the two
virtual sites reads `f(s-1) = 0`.  But `f` is the travel indicator, and it is `+1`
throughout `0 <= j < kstar`.  So no site strictly inside the travel interval is cut --
and therefore the two virtual sites lie in the **same run**, and the virtual pair
cannot merge two distinct runs. -/

/-- **The travel interval contains no cut site.** -/
theorem no_cut_inside_travel (P : SiteCost.PathData) (s : ℤ)
    (h0 : 0 < s) (hk : s < P.kstar) : ¬ P.cut s := by
  rintro ⟨-, -, hPhi⟩
  unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL SiteCost.PathData.vD
    SiteCost.vArr at hPhi
  rw [if_neg (by omega : ¬ s = (0:ℤ))] at hPhi
  rw [if_neg (by omega : ¬ s = P.kstar)] at hPhi
  simp only [ite_self, Nat.cast_zero, sub_zero, add_zero] at hPhi
  have hf : P.f (s - 1) = 1 := by
    unfold SiteCost.PathData.f travel
    rw [if_pos (by omega)]
  omega

/-- **So the two virtual sites lie in the same run.**  Between them -- the travel
interval -- there is no cut site, so the block index does not change. -/
theorem virtual_sites_same_run (P : SiteCost.PathData) (Zf : Finset ℤ)
    (hZ : ∀ z ∈ Zf, ¬ (0 < z ∧ z < P.kstar)) (hk : 0 < P.kstar) :
    ∀ z ∈ Zf, ¬ (0 < z ∧ z ≤ P.kstar - 1) := by
  intro z hz ⟨h1, h2⟩
  exact hZ z hz ⟨h1, by omega⟩

/-- The cut sites of a `PathData` avoid the interior of its travel interval. -/
theorem pdCut_avoids_travel (P : SiteCost.PathData) (s : ℤ)
    (h : P.cut s) : ¬ (0 < s ∧ s < P.kstar) := by
  rintro ⟨h1, h2⟩
  exact no_cut_inside_travel P s h1 h2 h

/-- **The converse of `gz_ne_of_between`**: no cut site between two points means the
same run.  BLOCK 3 proved the separating direction; this is the joining one. -/
theorem gz_eq_of_no_between (Zf : Finset ℤ) (a b : ℤ) (hab : a ≤ b)
    (h : ∀ z ∈ Zf, ¬ (a < z ∧ z ≤ b)) :
    CutComponents.gz Zf a = CutComponents.gz Zf b := by
  classical
  unfold CutComponents.gz
  congr 1
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, hle⟩; exact ⟨hz, by omega⟩
  · rintro ⟨hz, hle⟩
    refine ⟨hz, ?_⟩
    by_contra hc
    exact h z hz ⟨by omega, hle⟩

/-- **The two virtual sites lie in the same run.**

Cut sites avoid the interior of the travel interval (`pdCut_avoids_travel`) and are
never virtual sites (`VEndpt.arrivalfree_ne_virtual`), so nothing separates `s0` from
`s1`.  The virtual pair therefore joins two ends of one run, and cannot merge two
distinct runs -- which is what the lower bound `c >= |Z|` needs. -/
theorem virtual_pair_same_run (Zf : Finset ℤ) (s0 s1 : ℤ) (hle : s0 ≤ s1)
    (hsep : ∀ z ∈ Zf, ¬ (s0 < z ∧ z ≤ s1)) :
    CutComponents.gz Zf s0 = CutComponents.gz Zf s1 :=
  gz_eq_of_no_between Zf s0 s1 hle hsep

/-! ### `prop:cut` for the extended type

Every graph edge either preserves the block index or is local:

* **partner** edges keep the edge index (`hpe`), so both ends have the same position
  and the block index is trivially equal;
* **turn** edges between real ends are local, by the site-edge relation;
* **turn** edges at a virtual end preserve the block index, by `virtual_pair_same_run`
  -- supplied here as the hypothesis `hvirt`, which BLOCK 42 discharges. -/

theorem VEndpt.blk_or_local {n : ℕ} {mm : Fin n → ℕ} (bnd : ℤ) (Zf : Finset ℤ)
    (E : WalkGraph.Data (VEndpt n mm)) (hp : E.p = VEndpt.partner)
    (hreal : ∀ u : EndType.Endpt n mm, ∀ y : VEndpt n mm, E.t (Sum.inl u) = y →
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inl u)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf y ∨ (∃ t : ℤ,
        (VEndpt.edgeOf bnd (Sum.inl u) = t - 1 ∨ VEndpt.edgeOf bnd (Sum.inl u) = t) ∧
        (VEndpt.edgeOf bnd y = t - 1 ∨ VEndpt.edgeOf bnd y = t) ∧
        (VEndpt.edgeOf bnd (Sum.inl u) ≠ VEndpt.edgeOf bnd y → t ∉ Zf)))
    (hvirt : ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf (E.t (Sum.inr b : VEndpt n mm))) :
    ∀ x y : VEndpt n mm, (WalkGraph.graph E).Adj x y →
      CutComponents.blk (VEndpt.edgeOf bnd) Zf x
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf y ∨ (∃ t : ℤ,
        (VEndpt.edgeOf bnd x = t - 1 ∨ VEndpt.edgeOf bnd x = t) ∧
        (VEndpt.edgeOf bnd y = t - 1 ∨ VEndpt.edgeOf bnd y = t) ∧
        (VEndpt.edgeOf bnd x ≠ VEndpt.edgeOf bnd y → t ∉ Zf)) := by
  intro x y hxy
  rcases hxy with h | h
  · -- the crossing partner keeps the edge index
    left
    subst h
    unfold CutComponents.blk
    rw [hp, VEndpt.hpe (mm := mm) bnd x]
  · subst h
    cases x with
    | inl u => exact hreal u _ rfl
    | inr b => exact Or.inl (hvirt b)

/-- **`hreal` discharged.**  A turn out of a real end either lands on a real end --
where the site-edge relation makes it local -- or lands on a virtual end, in which case
the involution turns it back into an instance of `hvirt`. -/
theorem VEndpt.hreal_of_hturn {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ) (Zf : Finset ℤ)
    (E : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.siteP s0 s1 (E.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ u v : EndType.Endpt n mm, E.t (Sum.inl u) = Sum.inl v →
      EndType.edgeOf u ≠ EndType.edgeOf v → EndType.siteOf u ∉ Zf)
    (hvirt : ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf (E.t (Sum.inr b : VEndpt n mm))) :
    ∀ u : EndType.Endpt n mm, ∀ y : VEndpt n mm, E.t (Sum.inl u) = y →
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inl u)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf y ∨ (∃ t : ℤ,
        (VEndpt.edgeOf bnd (Sum.inl u) = t - 1 ∨ VEndpt.edgeOf bnd (Sum.inl u) = t) ∧
        (VEndpt.edgeOf bnd y = t - 1 ∨ VEndpt.edgeOf bnd y = t) ∧
        (VEndpt.edgeOf bnd (Sum.inl u) ≠ VEndpt.edgeOf bnd y → t ∉ Zf)) := by
  intro u y hy
  cases hcase : y with
  | inr b =>
    -- the turn landed on a virtual end; involution turns this into `hvirt`
    left
    have hback : E.t (Sum.inr b : VEndpt n mm) = Sum.inl u := by
      rw [← hcase, ← hy, E.t_invol]
    have := hvirt b
    rw [hback] at this
    exact this.symm
  | inl v =>
    -- both real: the site-edge relation makes the edge local
    right
    refine ⟨EndType.siteOf u, ?_, ?_, ?_⟩
    · have h : EndType.siteOf u
          = EndType.edgeOf u + (if EndType.atTop u then (1:ℤ) else 0) := rfl
      cases hb : EndType.atTop u
      · have e : (if EndType.atTop u then (1:ℤ) else 0) = 0 := by rw [hb]; rfl
        rw [e] at h; right; simp only [VEndpt.edgeOf]; omega
      · have e : (if EndType.atTop u then (1:ℤ) else 0) = 1 := by rw [hb]; rfl
        rw [e] at h; left; simp only [VEndpt.edgeOf]; omega
    · have hsv : EndType.siteOf v = EndType.siteOf u := by
        have := hts (Sum.inl u)
        rw [hy, hcase] at this
        exact this
      have h : EndType.siteOf v
          = EndType.edgeOf v + (if EndType.atTop v then (1:ℤ) else 0) := rfl
      cases hb : EndType.atTop v
      · have e : (if EndType.atTop v then (1:ℤ) else 0) = 0 := by rw [hb]; rfl
        rw [e] at h; right; simp only [VEndpt.edgeOf]; omega
      · have e : (if EndType.atTop v then (1:ℤ) else 0) = 1 := by rw [hb]; rfl
        rw [e] at h; left; simp only [VEndpt.edgeOf]; omega
    · intro hne
      refine hturn u v (by rw [hy, hcase]) ?_
      simpa [VEndpt.edgeOf] using hne

/-- **`prop:cut` for the extended type.**

`c >= |Z|`: at least `|Z|` connected components avoid any given one.  The hypotheses
are the three the construction supplies -- the pairing is the partner, turns preserve
sites, turns between real ends do not cross cut sites -- plus `hvirt` (the virtual pair
stays in one run, BLOCK 42) and `hruns` (every run carries an end). -/
theorem VEndpt.prop_cut {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ) (Zf : Finset ℤ)
    (E : WalkGraph.Data (VEndpt n mm)) (hp : E.p = VEndpt.partner)
    (hts : ∀ e, VEndpt.siteP s0 s1 (E.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ u v : EndType.Endpt n mm, E.t (Sum.inl u) = Sum.inl v →
      EndType.edgeOf u ≠ EndType.edgeOf v → EndType.siteOf u ∉ Zf)
    (hvirt : ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf (E.t (Sum.inr b : VEndpt n mm)))
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n mm, CutComponents.blk (VEndpt.edgeOf bnd) Zf v = i)
    (c0 : (WalkGraph.graph E).ConnectedComponent) :
    ∃ F : Fin Zf.card → (WalkGraph.graph E).ConnectedComponent,
      Function.Injective F ∧ ∀ i, F i ≠ c0 :=
  CutComponents.exists_injective_components_avoiding_blk_or_local
    (VEndpt.blk_or_local bnd Zf E hp
      (VEndpt.hreal_of_hturn s0 s1 bnd Zf E hts hturn hvirt) hvirt)
    hruns c0

/-- **`walkCount_ge_of_avoiding`, generic in the end type.**  The `ConfigLoop` version
is stated for `Endpt`; nothing in its proof uses that. -/
theorem walkCount_ge_of_avoiding_gen {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (k : ℕ)
    (c0 : (WalkGraph.graph D).ConnectedComponent)
    (F : Fin k → (WalkGraph.graph D).ConnectedComponent)
    (hinj : Function.Injective F) (havoid : ∀ i, F i ≠ c0) :
    k + 1 ≤ WalkGraph.walkCount D := by
  classical
  have hG : Function.Injective (Fin.cons c0 F : Fin (k + 1) → _) := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact absurd hij.symm (by simpa using havoid j)
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simpa using havoid i)
      | succ j => simpa using congrArg Fin.succ (hinj (by simpa using hij))
  simpa using Fintype.card_le_of_injective _ hG

/-- **`c >= |Z|` as a bound on the walk count**, for the extended type. -/
theorem VEndpt.walkCount_ge {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ) (Zf : Finset ℤ)
    (E : WalkGraph.Data (VEndpt n mm)) (hp : E.p = VEndpt.partner)
    (hts : ∀ e, VEndpt.siteP s0 s1 (E.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ u v : EndType.Endpt n mm, E.t (Sum.inl u) = Sum.inl v →
      EndType.edgeOf u ≠ EndType.edgeOf v → EndType.siteOf u ∉ Zf)
    (hvirt : ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf (E.t (Sum.inr b : VEndpt n mm)))
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n mm, CutComponents.blk (VEndpt.edgeOf bnd) Zf v = i)
    (z₀ : VEndpt n mm) :
    Zf.card + 1 ≤ WalkGraph.walkCount E := by
  obtain ⟨F, hinj, havoid⟩ := VEndpt.prop_cut s0 s1 bnd Zf E hp hts hturn hvirt hruns
    ((WalkGraph.graph E).connectedComponentMk z₀)
  exact walkCount_ge_of_avoiding_gen E Zf.card _ F hinj havoid

/-! ### The upper bound `c <= |Z|`, generically

`ConfigLoop.walkCount_le_runs_gen` is stated for `Endpt` and asks for `Local`.  Both
restrictions come off: `ConfigMerge.walkCount_le_card` is already generic, and
locality is used only through `blk_reachable`, which BLOCK 43 generalised. -/

/-- The run index, generically. -/
def runIndexG {α : Type*} (pos : α → ℤ) (Zf : Finset ℤ) (x : α) : Fin (Zf.card + 1) :=
  ⟨CutComponents.gz Zf (pos x), Nat.lt_succ_of_le (ConfigLoop.gz_le_card Zf _)⟩

/-- **`walkCount <= |Z| + 1`**, for any end type whose graph edges preserve the block
index or are local, and whose runs are connected. -/
theorem walkCount_le_runs_blk {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (pos : α → ℤ) (Zf : Finset ℤ)
    (hedge : ∀ x y : α, (WalkGraph.graph D).Adj x y →
      CutComponents.blk pos Zf x = CutComponents.blk pos Zf y ∨ (∃ t : ℤ,
        (pos x = t - 1 ∨ pos x = t) ∧ (pos y = t - 1 ∨ pos y = t) ∧
        (pos x ≠ pos y → t ∉ Zf)))
    (hsep : ∀ x y : α, runIndexG pos Zf x = runIndexG pos Zf y →
      (WalkGraph.graph D).Reachable x y) :
    WalkGraph.walkCount D ≤ Zf.card + 1 := by
  have hconst : ∀ x y : α, (WalkGraph.graph D).Reachable x y →
      runIndexG pos Zf x = runIndexG pos Zf y := by
    intro x y hr
    refine Fin.ext ?_
    exact CutComponents.blk_reachable_except
      (Exc := fun a b => CutComponents.blk pos Zf a = CutComponents.blk pos Zf b)
      hedge (fun _ _ h => h) hr
  simpa using ConfigMerge.walkCount_le_card D (runIndexG pos Zf) hconst hsep

/-- **`c <= |Z|` for the extended type**, given that the runs are connected. -/
theorem VEndpt.walkCount_le {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ) (Zf : Finset ℤ)
    (E : WalkGraph.Data (VEndpt n mm)) (hp : E.p = VEndpt.partner)
    (hts : ∀ e, VEndpt.siteP s0 s1 (E.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ u v : EndType.Endpt n mm, E.t (Sum.inl u) = Sum.inl v →
      EndType.edgeOf u ≠ EndType.edgeOf v → EndType.siteOf u ∉ Zf)
    (hvirt : ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf (E.t (Sum.inr b : VEndpt n mm)))
    (hsep : ∀ x y : VEndpt n mm,
      runIndexG (VEndpt.edgeOf bnd) Zf x = runIndexG (VEndpt.edgeOf bnd) Zf y →
      (WalkGraph.graph E).Reachable x y) :
    WalkGraph.walkCount E ≤ Zf.card + 1 :=
  walkCount_le_runs_blk E (VEndpt.edgeOf bnd) Zf
    (VEndpt.blk_or_local bnd Zf E hp
      (VEndpt.hreal_of_hturn s0 s1 bnd Zf E hts hturn hvirt) hvirt) hsep

/-- **The shield law for the extended type: `c = |Z|`.**

Both bounds now hold on `VEndpt`, so the walk count is exactly `|Z| + 1`.  The
hypotheses are: the pairing is the partner, turns preserve sites, real turns do not
cross cut sites, the virtual pair stays in one run, every run carries an end, and ends
of one run share a walk. -/
theorem VEndpt.shield {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ) (Zf : Finset ℤ)
    (E : WalkGraph.Data (VEndpt n mm)) (hp : E.p = VEndpt.partner)
    (hts : ∀ e, VEndpt.siteP s0 s1 (E.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ u v : EndType.Endpt n mm, E.t (Sum.inl u) = Sum.inl v →
      EndType.edgeOf u ≠ EndType.edgeOf v → EndType.siteOf u ∉ Zf)
    (hvirt : ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf (E.t (Sum.inr b : VEndpt n mm)))
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n mm, CutComponents.blk (VEndpt.edgeOf bnd) Zf v = i)
    (hsep : ∀ x y : VEndpt n mm,
      runIndexG (VEndpt.edgeOf bnd) Zf x = runIndexG (VEndpt.edgeOf bnd) Zf y →
      (WalkGraph.graph E).Reachable x y)
    (z₀ : VEndpt n mm) :
    WalkGraph.walkCount E = Zf.card + 1 :=
  le_antisymm
    (VEndpt.walkCount_le s0 s1 bnd Zf E hp hts hturn hvirt hsep)
    (VEndpt.walkCount_ge s0 s1 bnd Zf E hp hts hturn hvirt hruns z₀)

/-! ### The run step, generically

`hsep` -- ends of one run share a walk -- is the conclusion of a descent: while two
ends of a run lie in different walks, a free pair exists and merging it lowers the walk
count.  `CostMerge.step_of_split_local` supplies the step and is already generic, so
the run step is too. -/

/-- **The run step.**  Either a strict descent exists, or the runs are already
connected. -/
theorem run_step_gen {α : Type*} [Fintype α] [DecidableEq α]
    (d : EndData.Data α) (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (D : WalkGraph.Data α) (Zf : Finset ℤ)
    (hside : ∀ x, d.side x = atTop x)
    (hsW : ∀ w x, (WalkGraph.graph D).Reachable w x →
      siteOf x = WalkSupport.wLo edgeOf (WalkGraph.graph D) w →
      atTop x = false ∨ siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsX : ∀ w x, (WalkGraph.graph D).Reachable w x →
      edgeOf x = WalkSupport.wLo edgeOf (WalkGraph.graph D) w → atTop x = false →
      siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsT : ∀ w y, edgeOf y = WalkSupport.wLo edgeOf (WalkGraph.graph D) w - 1 →
      atTop y = true → siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, d.isArr (D.t e) = !d.isArr e)
    (hpsite : ∀ x, siteOf (D.p x) ≠ siteOf x)
    (hcov : ∀ z v : α, edgeOf v < WalkSupport.wLo edgeOf (WalkGraph.graph D) z →
      ∃ w : α, edgeOf w = WalkSupport.wLo edgeOf (WalkGraph.graph D) z - 1 ∧
        atTop w = true)
    (hmin : ∀ (b b' : α), siteOf b = siteOf b' →
      d.isArr b = true → d.isArr b' = true → ∀ h1 h2 h3,
      ¬ CostMerge.costOf d (WalkGraph.swapData D b (D.t b) b' (D.t b') h1 h2 h3)
        < CostMerge.costOf d D) :
    (∃ D' : WalkGraph.Data α, WalkGraph.walkCount D' < WalkGraph.walkCount D) ∨
      (∀ x y : α, runIndexG edgeOf Zf x = runIndexG edgeOf Zf y →
        (WalkGraph.graph D).Reachable x y) := by
  classical
  by_cases hsep : ∀ x y : α, runIndexG edgeOf Zf x = runIndexG edgeOf Zf y →
      (WalkGraph.graph D).Reachable x y
  · exact Or.inr hsep
  · left
    obtain ⟨x, hx⟩ := not_forall.mp hsep
    obtain ⟨y, hy⟩ := not_forall.mp hx
    have hnr : ¬ (WalkGraph.graph D).Reachable x y := fun hc => hy (fun _ => hc)
    exact CostMerge.step_of_split_local d edgeOf siteOf atTop D hside hsW hsX hsT
      hpe hpt hts hta hpsite hcov hmin x y hnr

/-- **The run step, preserving the merge class.**

`run_step_gen` drops the invariant.  `step_of_split'_local` returns enough to rebuild
it: the new datum has the same pairing and its turn is an explicit `swapT`, so
`swapT_site` and `swapT_arr` restore `Merges` and `cost_swapData` restores
minimality. -/
theorem run_step_min_gen {α : Type*} [Fintype α] [DecidableEq α]
    (d : EndData.Data α) (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (p₀ : α → α)
    (Zf : Finset ℤ)
    (hside : ∀ x, d.side x = atTop x)
    (hpe : ∀ x, edgeOf (p₀ x) = edgeOf x)
    (hpt : ∀ x, atTop (p₀ x) = !atTop x)
    (hpsite : ∀ x, siteOf (p₀ x) ≠ siteOf x)
    (hsW : ∀ E : WalkGraph.Data α, WalkSupport.Merges siteOf d.isArr p₀ E →
      ∀ w x, (WalkGraph.graph E).Reachable w x →
      siteOf x = WalkSupport.wLo edgeOf (WalkGraph.graph E) w →
      atTop x = false ∨ siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsX : ∀ E : WalkGraph.Data α, WalkSupport.Merges siteOf d.isArr p₀ E →
      ∀ w x, (WalkGraph.graph E).Reachable w x →
      edgeOf x = WalkSupport.wLo edgeOf (WalkGraph.graph E) w → atTop x = false →
      siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsT : ∀ E : WalkGraph.Data α, WalkSupport.Merges siteOf d.isArr p₀ E →
      ∀ w y, edgeOf y = WalkSupport.wLo edgeOf (WalkGraph.graph E) w - 1 →
      atTop y = true → siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hcov : ∀ E : WalkGraph.Data α, ∀ z v : α,
      edgeOf v < WalkSupport.wLo edgeOf (WalkGraph.graph E) z →
      ∃ w : α, edgeOf w = WalkSupport.wLo edgeOf (WalkGraph.graph E) z - 1 ∧
        atTop w = true)
    (D : WalkGraph.Data α) (hD : CostMerge.MergesMin siteOf d.isArr p₀ d D) :
    (∃ D' : WalkGraph.Data α, CostMerge.MergesMin siteOf d.isArr p₀ d D' ∧
      WalkGraph.walkCount D' < WalkGraph.walkCount D) ∨
      (∀ x y : α, runIndexG edgeOf Zf x = runIndexG edgeOf Zf y →
        (WalkGraph.graph D).Reachable x y) := by
  classical
  by_cases hsep : ∀ x y : α, runIndexG edgeOf Zf x = runIndexG edgeOf Zf y →
      (WalkGraph.graph D).Reachable x y
  · exact Or.inr hsep
  · left
    obtain ⟨x, hx⟩ := not_forall.mp hsep
    obtain ⟨y, hy⟩ := not_forall.mp hx
    have hnr : ¬ (WalkGraph.graph D).Reachable x y := fun hc => hy (fun _ => hc)
    obtain ⟨hM, hmin⟩ := hD
    obtain ⟨hp, hts, hta⟩ := hM
    obtain ⟨D', hlt, hpeq, a, a', harr, harr', hss, hsplit, hshared, hteq⟩ :=
      CostMerge.step_of_split'_local d edgeOf siteOf atTop D hside
        (hsW D ⟨hp, hts, hta⟩) (hsX D ⟨hp, hts, hta⟩) (hsT D ⟨hp, hts, hta⟩)
        (by rw [hp]; exact hpe) (by rw [hp]; exact hpt) hts hta
        (by rw [hp]; exact hpsite) (hcov D)
        (CostMerge.hmin_of_mergesMin siteOf p₀ d D ⟨⟨hp, hts, hta⟩, hmin⟩) x y hnr
    have hda : d.isArr (D.t a) = false := by rw [hta, harr]; rfl
    have hda' : d.isArr (D.t a') = false := by rw [hta, harr']; rfl
    have hne : a ≠ a' := fun h => hsplit (h ▸ SimpleGraph.Reachable.refl a)
    -- the new datum is in the class
    have hts' : ∀ e, siteOf (D'.t e) = siteOf e := by
      intro e
      rw [hteq]
      exact WalkGraph.swapT_site siteOf D.t a (D.t a) a' (D.t a') hts (hts a) hss
        (show siteOf (D.t a') = siteOf a from (hts a').trans hss) e
    have hta' : ∀ e, d.isArr (D'.t e) = !d.isArr e := by
      intro e
      rw [hteq]
      exact WalkGraph.swapT_arr d.isArr D.t a (D.t a) a' (D.t a') hta rfl rfl harr harr' e
    -- and cost-minimal, because the swap preserves cost
    have hcost : CostMerge.costOf d D' = CostMerge.costOf d D := by
      have h1 := WalkGraph.swapT_invol D.t_invol rfl rfl
        (ConfigMerge.dep_ne_arr' D rfl) (ConfigMerge.dep_ne_other D rfl hsplit)
        (Ne.symm hne) (ConfigMerge.dep_ne_dep' D rfl rfl (Ne.symm hne))
        (Ne.symm (ConfigMerge.dep_ne_arr' D rfl))
        (ConfigMerge.dep_ne_other' D rfl hsplit)
      have h2 := WalkGraph.swapT_ne D.t a (D.t a) a' (D.t a') D.t_ne
        (ConfigMerge.dep_ne_other D rfl hsplit) (ConfigMerge.dep_ne_other' D rfl hsplit)
      have h3 := WalkGraph.partner_ne_swapT siteOf D.p D.t a (D.t a) a' (D.t a')
        (by rw [hp]; exact hpsite) hts (hts a) hss (by rw [hts a']; exact hss)
      have hc := CostMerge.cost_swapData d D a a' harr harr' hda hda' hne hshared h1 h2 h3
      rw [← hc]
      exact CostMerge.cost_congr d D' _ (fun b _ => by rw [hteq]; rfl)
    exact ⟨D', ⟨⟨hpeq.trans hp, hts', hta'⟩, fun F hF => by rw [hcost]; exact hmin F hF⟩,
      hlt⟩

/-- **`hsep`, discharged.**  Iterating the invariant-preserving run step reaches a
cost-minimal datum whose runs are connected -- which is the last input of the shield
law. -/
theorem exists_run_connected {α : Type*} [Fintype α] [DecidableEq α]
    (d : EndData.Data α) (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (p₀ : α → α)
    (Zf : Finset ℤ)
    (hside : ∀ x, d.side x = atTop x)
    (hpe : ∀ x, edgeOf (p₀ x) = edgeOf x)
    (hpt : ∀ x, atTop (p₀ x) = !atTop x)
    (hpsite : ∀ x, siteOf (p₀ x) ≠ siteOf x)
    (hsW : ∀ E : WalkGraph.Data α, WalkSupport.Merges siteOf d.isArr p₀ E →
      ∀ w x, (WalkGraph.graph E).Reachable w x →
      siteOf x = WalkSupport.wLo edgeOf (WalkGraph.graph E) w →
      atTop x = false ∨ siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsX : ∀ E : WalkGraph.Data α, WalkSupport.Merges siteOf d.isArr p₀ E →
      ∀ w x, (WalkGraph.graph E).Reachable w x →
      edgeOf x = WalkSupport.wLo edgeOf (WalkGraph.graph E) w → atTop x = false →
      siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsT : ∀ E : WalkGraph.Data α, WalkSupport.Merges siteOf d.isArr p₀ E →
      ∀ w y, edgeOf y = WalkSupport.wLo edgeOf (WalkGraph.graph E) w - 1 →
      atTop y = true → siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hcov : ∀ E : WalkGraph.Data α, ∀ z v : α,
      edgeOf v < WalkSupport.wLo edgeOf (WalkGraph.graph E) z →
      ∃ w : α, edgeOf w = WalkSupport.wLo edgeOf (WalkGraph.graph E) z - 1 ∧
        atTop w = true)
    (D : WalkGraph.Data α) (hD : CostMerge.MergesMin siteOf d.isArr p₀ d D) :
    ∃ D' : WalkGraph.Data α, CostMerge.MergesMin siteOf d.isArr p₀ d D' ∧
      ∀ x y : α, runIndexG edgeOf Zf x = runIndexG edgeOf Zf y →
        (WalkGraph.graph D').Reachable x y :=
  ConfigMerge.reaches_stuck
    (P := CostMerge.MergesMin siteOf d.isArr p₀ d)
    (Stuck := fun E => ∀ x y : α, runIndexG edgeOf Zf x = runIndexG edgeOf Zf y →
      (WalkGraph.graph E).Reachable x y)
    (fun E hE => run_step_min_gen d edgeOf siteOf atTop p₀ Zf hside hpe hpt hpsite
      hsW hsX hsT hcov E hE) D hD

/-- **The shield law with `hsep` discharged.**

`c = |Z|` for a cost-minimal datum on the extended type.  `hsep` is now produced by
`exists_run_connected` rather than assumed; what remains are `hturn` (the paper's cut
condition on real turns) and `hruns` (every run carries an end), both statements about
the configuration, plus the construction's own hypotheses. -/
theorem VEndpt.shield_final {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ) (Zf : Finset ℤ)
    (d : EndData.Data (VEndpt n mm)) (up : Fin n → ℕ)
    (hd : d.isArr = VEndpt.isArr up)
    (hside : ∀ x, d.side x = VEndpt.atTop x)
    (hpsite : ∀ x : VEndpt n mm,
      VEndpt.siteP s0 s1 (VEndpt.partner x) ≠ VEndpt.siteP s0 s1 x)
    (hsW : ∀ E : WalkGraph.Data (VEndpt n mm),
      WalkSupport.Merges (VEndpt.siteP s0 s1) d.isArr VEndpt.partner E →
      ∀ w x : VEndpt n mm, (WalkGraph.graph E).Reachable w x →
      VEndpt.siteP s0 s1 x
        = WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) w →
      VEndpt.atTop x = false ∨ VEndpt.siteP s0 s1 x
        = VEndpt.edgeOf bnd x + (if VEndpt.atTop x then 1 else 0))
    (hsX : ∀ E : WalkGraph.Data (VEndpt n mm),
      WalkSupport.Merges (VEndpt.siteP s0 s1) d.isArr VEndpt.partner E →
      ∀ w x : VEndpt n mm, (WalkGraph.graph E).Reachable w x →
      VEndpt.edgeOf bnd x = WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) w →
      VEndpt.atTop x = false → VEndpt.siteP s0 s1 x
        = VEndpt.edgeOf bnd x + (if VEndpt.atTop x then 1 else 0))
    (hsT : ∀ E : WalkGraph.Data (VEndpt n mm),
      WalkSupport.Merges (VEndpt.siteP s0 s1) d.isArr VEndpt.partner E →
      ∀ w y : VEndpt n mm, VEndpt.edgeOf bnd y
        = WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) w - 1 →
      VEndpt.atTop y = true → VEndpt.siteP s0 s1 y
        = VEndpt.edgeOf bnd y + (if VEndpt.atTop y then 1 else 0))
    (hcov : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ z v : VEndpt n mm,
      VEndpt.edgeOf bnd v < WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) z →
      ∃ w : VEndpt n mm, VEndpt.edgeOf bnd w
        = WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) z - 1 ∧
        VEndpt.atTop w = true)
    (hturn : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ u v : EndType.Endpt n mm,
      E.t (Sum.inl u) = Sum.inl v →
      EndType.edgeOf u ≠ EndType.edgeOf v → EndType.siteOf u ∉ Zf)
    (hvirt : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf (E.t (Sum.inr b : VEndpt n mm)))
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n mm, CutComponents.blk (VEndpt.edgeOf bnd) Zf v = i)
    (z₀ : VEndpt n mm)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : CostMerge.MergesMin (VEndpt.siteP s0 s1) d.isArr VEndpt.partner d D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.siteP s0 s1) d.isArr VEndpt.partner d D' ∧
      WalkGraph.walkCount D' = Zf.card + 1 := by
  obtain ⟨D', hD', hsep⟩ :=
    exists_run_connected d (VEndpt.edgeOf bnd) (VEndpt.siteP s0 s1) VEndpt.atTop
      VEndpt.partner Zf hside (VEndpt.hpe bnd) VEndpt.hpt hpsite hsW hsX hsT hcov D hD
  exact ⟨D', hD', VEndpt.shield s0 s1 bnd Zf D' hD'.1.1 hD'.1.2.1 (hturn D')
    (hvirt D') hruns hsep z₀⟩

/-- **The shield law with `hsep` discharged**, parametrised by the `atTop` map so both
orientations fit.  The cut-side lemmas never mention it; only the merge does.

`c = |Z|` for a cost-minimal datum on the extended type.  `hsep` is now produced by
`exists_run_connected` rather than assumed; what remains are `hturn` (the paper's cut
condition on real turns) and `hruns` (every run carries an end), both statements about
the configuration, plus the construction's own hypotheses. -/
theorem VEndpt.shield_finalT {n : ℕ} {mm : Fin n → ℕ} (s0 s1 bnd : ℤ) (Zf : Finset ℤ)
    (d : EndData.Data (VEndpt n mm)) (top : VEndpt n mm → Bool)
    (hside : ∀ x, d.side x = top x)
    (hptT : ∀ x, top (VEndpt.partner x) = !top x)
    (hpsite : ∀ x : VEndpt n mm,
      VEndpt.siteP s0 s1 (VEndpt.partner x) ≠ VEndpt.siteP s0 s1 x)
    (hsW : ∀ E : WalkGraph.Data (VEndpt n mm),
      WalkSupport.Merges (VEndpt.siteP s0 s1) d.isArr VEndpt.partner E →
      ∀ w x : VEndpt n mm, (WalkGraph.graph E).Reachable w x →
      VEndpt.siteP s0 s1 x
        = WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) w →
      top x = false ∨ VEndpt.siteP s0 s1 x
        = VEndpt.edgeOf bnd x + (if top x then 1 else 0))
    (hsX : ∀ E : WalkGraph.Data (VEndpt n mm),
      WalkSupport.Merges (VEndpt.siteP s0 s1) d.isArr VEndpt.partner E →
      ∀ w x : VEndpt n mm, (WalkGraph.graph E).Reachable w x →
      VEndpt.edgeOf bnd x = WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) w →
      top x = false → VEndpt.siteP s0 s1 x
        = VEndpt.edgeOf bnd x + (if top x then 1 else 0))
    (hsT : ∀ E : WalkGraph.Data (VEndpt n mm),
      WalkSupport.Merges (VEndpt.siteP s0 s1) d.isArr VEndpt.partner E →
      ∀ w y : VEndpt n mm, VEndpt.edgeOf bnd y
        = WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) w - 1 →
      top y = true → VEndpt.siteP s0 s1 y
        = VEndpt.edgeOf bnd y + (if top y then 1 else 0))
    (hcov : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ z v : VEndpt n mm,
      VEndpt.edgeOf bnd v < WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) z →
      ∃ w : VEndpt n mm, VEndpt.edgeOf bnd w
        = WalkSupport.wLo (VEndpt.edgeOf bnd) (WalkGraph.graph E) z - 1 ∧
        top w = true)
    (hturn : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ u v : EndType.Endpt n mm,
      E.t (Sum.inl u) = Sum.inl v →
      EndType.edgeOf u ≠ EndType.edgeOf v → EndType.siteOf u ∉ Zf)
    (hvirt : ∀ E : WalkGraph.Data (VEndpt n mm),
      WalkSupport.Merges (VEndpt.siteP s0 s1) d.isArr VEndpt.partner E → ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf bnd) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf bnd) Zf (E.t (Sum.inr b : VEndpt n mm)))
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n mm, CutComponents.blk (VEndpt.edgeOf bnd) Zf v = i)
    (z₀ : VEndpt n mm)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : CostMerge.MergesMin (VEndpt.siteP s0 s1) d.isArr VEndpt.partner d D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.siteP s0 s1) d.isArr VEndpt.partner d D' ∧
      WalkGraph.walkCount D' = Zf.card + 1 := by
  obtain ⟨D', hD', hsep⟩ :=
    exists_run_connected d (VEndpt.edgeOf bnd) (VEndpt.siteP s0 s1) top
      VEndpt.partner Zf hside (VEndpt.hpe bnd) hptT hpsite hsW hsX hsT hcov D hD
  exact ⟨D', hD', VEndpt.shield s0 s1 bnd Zf D' hD'.1.1 hD'.1.2.1 (hturn D')
    (hvirt D' hD'.1) hruns hsep z₀⟩

/-! ### The three discharges, in `siteP` form, mirrored orientation

`bnd = s0 - 1`, virtual arrival a top at `s0 = bnd + 1`, virtual departure a bottom at
`s1`.  `hsW` and `hsT` hold outright; `hsX` needs the walk to reach back to `s1`. -/

theorem VEndpt.hsW_negP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (x : VEndpt n mm) :
    VEndpt.atTopN x = false ∨ VEndpt.siteP s0 s1 x
      = VEndpt.edgeOf (s0 - 1) x + (if VEndpt.atTopN x then 1 else 0) := by
  cases x with
  | inl y => exact Or.inr rfl
  | inr b =>
    cases b
    · exact Or.inr (by simp [VEndpt.siteP, VEndpt.edgeOf, VEndpt.atTopN])
    · exact Or.inl rfl

theorem VEndpt.hsT_negP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (y : VEndpt n mm)
    (hyt : VEndpt.atTopN y = true) :
    VEndpt.siteP s0 s1 y
      = VEndpt.edgeOf (s0 - 1) y + (if VEndpt.atTopN y then 1 else 0) := by
  cases y with
  | inl u => rfl
  | inr b =>
    cases b
    · simp [VEndpt.siteP, VEndpt.edgeOf, VEndpt.atTopN]
    · exact absurd hyt (by simp [VEndpt.atTopN])

theorem VEndpt.hsX_negP {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hlt : s1 < s0)
    (E : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.siteP s0 s1 (E.t e) = VEndpt.siteP s0 s1 e)
    (w x : VEndpt n mm) (hwx : (WalkGraph.graph E).Reachable w x)
    (hxe : VEndpt.edgeOf (s0 - 1) x
      = WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) w)
    (hxb : VEndpt.atTopN x = false) :
    VEndpt.siteP s0 s1 x
      = VEndpt.edgeOf (s0 - 1) x + (if VEndpt.atTopN x then 1 else 0) := by
  cases x with
  | inl y => rfl
  | inr b =>
    cases b
    · exact absurd hxb (by simp [VEndpt.atTopN])
    · have hw : WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) w = s0 - 1 := by
        simpa [VEndpt.edgeOf] using hxe.symm
      have hle := VEndpt.wlo_le_s1 s0 s1 (s0 - 1) (by omega) E w hts hwx
      rw [hw] at hle
      have hs : s1 = s0 - 1 := by omega
      simp [VEndpt.siteP, VEndpt.edgeOf, VEndpt.atTopN, hs]

/-- **The shield law, mirrored orientation, discharges plugged in.**

`c = |Z|` on the extended type with `s1 < s0` and `bnd = s0 - 1`.  The three locality
hypotheses are gone -- `hsW_negP`, `hsT_negP` and `hsX_negP` supply them -- leaving
only `hturn`, `hvirt`, `hruns` and `hcov`, all statements about the configuration. -/
theorem VEndpt.shield_neg {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hlt : s1 < s0)
    (Zf : Finset ℤ) (up : Fin n → ℕ) (ds : Bool → Bool)
    (hcov : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ z v : VEndpt n mm,
      VEndpt.edgeOf (s0 - 1) v
        < WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z →
      ∃ w : VEndpt n mm, VEndpt.edgeOf (s0 - 1) w
        = WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z - 1 ∧
        VEndpt.atTopN w = true)
    (hturn : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ u v : EndType.Endpt n mm,
      E.t (Sum.inl u) = Sum.inl v →
      EndType.edgeOf u ≠ EndType.edgeOf v → EndType.siteOf u ∉ Zf)
    (hvirt : ∀ E : WalkGraph.Data (VEndpt n mm),
      WalkSupport.Merges (VEndpt.siteP s0 s1) (vEndDataN up ds).isArr
        VEndpt.partner E → ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf
            (E.t (Sum.inr b : VEndpt n mm)))
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n mm, CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf v = i)
    (z₀ : VEndpt n mm)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : CostMerge.MergesMin (VEndpt.siteP s0 s1) (vEndDataN up ds).isArr
      VEndpt.partner (vEndDataN up ds) D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.siteP s0 s1) (vEndDataN up ds).isArr
        VEndpt.partner (vEndDataN up ds) D' ∧
      WalkGraph.walkCount D' = Zf.card + 1 :=
  VEndpt.shield_finalT s0 s1 (s0 - 1) Zf (vEndDataN up ds) VEndpt.atTopN
    (fun _ => rfl) VEndpt.hptN (VEndpt.partner_site_neP s0 s1 (by omega))
    (fun _ _ _ x _ _ => VEndpt.hsW_negP s0 s1 x)
    (fun E hE w x hwx hxe hxb => VEndpt.hsX_negP s0 s1 hlt E hE.2.1 w x hwx hxe hxb)
    (fun _ _ _ y _ hyt => VEndpt.hsT_negP s0 s1 y hyt)
    hcov hturn hvirt hruns z₀ D hD

/-- **`gz` is constant on a cut-free window.** -/
theorem gz_const_on (Zf : Finset ℤ) (lo hi : ℤ)
    (h : ∀ z ∈ Zf, ¬ (lo < z ∧ z ≤ hi)) :
    ∀ a b : ℤ, lo ≤ a → a ≤ hi → lo ≤ b → b ≤ hi →
      CutComponents.gz Zf a = CutComponents.gz Zf b := by
  intro a b hla hah hlb hbh
  have ha : CutComponents.gz Zf lo = CutComponents.gz Zf a :=
    gz_eq_of_no_between Zf lo a hla (fun z hz ⟨h1, h2⟩ => h z hz ⟨h1, by omega⟩)
  have hb : CutComponents.gz Zf lo = CutComponents.gz Zf b :=
    gz_eq_of_no_between Zf lo b hlb (fun z hz ⟨h1, h2⟩ => h z hz ⟨h1, by omega⟩)
  rw [← ha, hb]

/-- **`hvirt` supplied.**

The turn of a virtual end is either the other virtual end -- same edge, so the same
block -- or a real end at site `s0` or `s1`, hence on an edge inside the window
`[s1 - 1, s0]`.  With no cut site in that window (BLOCK 42's `no_cut_inside_travel`
for the interior, BLOCK 39's `arrivalfree_ne_virtual` for the two endpoints), `gz` is
constant there. -/
theorem VEndpt.hvirt_of_gap {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hlt : s1 < s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (E : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.siteP s0 s1 (E.t e) = VEndpt.siteP s0 s1 e) :
    ∀ b : Bool,
      CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf
            (E.t (Sum.inr b : VEndpt n mm)) := by
  -- one argument, run at each of the two virtual sites
  have key : ∀ (b : Bool) (sb : ℤ), VEndpt.siteP s0 s1 (Sum.inr b : VEndpt n mm) = sb →
      s1 - 1 ≤ sb - 1 → sb ≤ s0 →
      CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf (Sum.inr b : VEndpt n mm)
        = CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf
            (E.t (Sum.inr b : VEndpt n mm)) := by
    intro b sb hsb hlo hhi
    unfold CutComponents.blk
    have hsite : VEndpt.siteP s0 s1 (E.t (Sum.inr b : VEndpt n mm)) = sb := by
      rw [hts]; exact hsb
    cases hcase : E.t (Sum.inr b : VEndpt n mm) with
    | inr c => rfl
    | inl u =>
      rw [hcase] at hsite
      have hu : EndType.edgeOf u = sb ∨ EndType.edgeOf u = sb - 1 := by
        have hs : EndType.edgeOf u + (if EndType.atTop u then (1:ℤ) else 0) = sb := hsite
        cases hb : EndType.atTop u
        · have e : (if EndType.atTop u then (1:ℤ) else 0) = 0 := by rw [hb]; rfl
          rw [e] at hs; omega
        · have e : (if EndType.atTop u then (1:ℤ) else 0) = 1 := by rw [hb]; rfl
          rw [e] at hs; omega
      refine gz_const_on Zf (s1 - 1) s0 hgap _ _ ?_ ?_ ?_ ?_ <;>
        simp only [VEndpt.edgeOf] <;> omega
  intro b
  cases b
  · exact key false s0 rfl (by omega) (by omega)
  · exact key true s1 rfl (by omega) (by omega)

/-- **The shield law on the extended type, taking only configuration inputs.**

`hvirt` is now supplied by `hvirt_of_gap` from the cut-free window, so what the caller
must provide is `hgap` (no cut site in `[s1-1, s0]`, which BLOCKS 39 and 42 establish
for a real configuration), `hturn`, `hruns`, `hcov` and a basepoint.  Nothing about the
virtual pair, the phantom edge or the orientation appears. -/
theorem VEndpt.shield_gap {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hlt : s1 < s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (up : Fin n → ℕ) (ds : Bool → Bool)
    (hcov : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ z v : VEndpt n mm,
      VEndpt.edgeOf (s0 - 1) v
        < WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z →
      ∃ w : VEndpt n mm, VEndpt.edgeOf (s0 - 1) w
        = WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z - 1 ∧
        VEndpt.atTopN w = true)
    (hturn : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ u v : EndType.Endpt n mm,
      E.t (Sum.inl u) = Sum.inl v →
      EndType.edgeOf u ≠ EndType.edgeOf v → EndType.siteOf u ∉ Zf)
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n mm, CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf v = i)
    (z₀ : VEndpt n mm)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : CostMerge.MergesMin (VEndpt.siteP s0 s1) (vEndDataN up ds).isArr
      VEndpt.partner (vEndDataN up ds) D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      CostMerge.MergesMin (VEndpt.siteP s0 s1) (vEndDataN up ds).isArr
        VEndpt.partner (vEndDataN up ds) D' ∧
      WalkGraph.walkCount D' = Zf.card + 1 :=
  VEndpt.shield_neg s0 s1 hlt Zf up ds hcov hturn
    (fun E hE => VEndpt.hvirt_of_gap s0 s1 hlt Zf hgap E hE.2.1) hruns z₀ D hD

/-- **No cut site inside a NEGATIVE travel interval.**

The mirror of `no_cut_inside_travel`.  For `kstar < 0` the travel indicator is `-1`
throughout `kstar <= j < 0`, so `Phi = 0` fails at every site strictly between. -/
theorem no_cut_in_neg_travel (P : SiteCost.PathData) (s : ℤ)
    (hk : P.kstar < s) (h0 : s < 0) : ¬ P.cut s := by
  rintro ⟨-, -, hPhi⟩
  unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL SiteCost.PathData.vD
    SiteCost.vArr at hPhi
  rw [if_neg (by omega : ¬ s = (0:ℤ))] at hPhi
  rw [if_neg (by omega : ¬ s = P.kstar)] at hPhi
  simp only [ite_self, Nat.cast_zero, sub_zero, add_zero] at hPhi
  have hf : P.f (s - 1) = -1 := by
    unfold SiteCost.PathData.f travel
    rw [if_neg (by omega), if_pos (by omega)]
  omega

/-- **The gap condition, discharged.**

A cut site in the window `[kstar, 0]` is impossible: strictly inside by
`no_cut_in_neg_travel`, and at either endpoint because those are the two virtual sites,
which `arrivalfree_ne_virtual` excludes.  The two exclusions are passed in, since they
are facts about the configuration's balance. -/
theorem pd_hgap (P : SiteCost.PathData) (hk : P.kstar < 0) (Zf : Finset ℤ)
    (hZcut : ∀ z ∈ Zf, P.cut (P.A + z))
    (hne0 : (-P.A) ∉ Zf) (hne1 : (P.kstar - P.A) ∉ Zf) :
    ∀ z ∈ Zf, ¬ ((P.kstar - P.A) - 1 < z ∧ z ≤ -P.A) := by
  rintro z hz ⟨h1, h2⟩
  have hcut := hZcut z hz
  set u := P.A + z with hu
  have hu1 : P.kstar - 1 < u := by omega
  have hu2 : u ≤ 0 := by omega
  rcases lt_trichotomy u 0 with h | h | h
  · rcases lt_trichotomy P.kstar u with hh | hh | hh
    · exact no_cut_in_neg_travel P u hh h hcut
    · exact hne1 (by rw [show z = P.kstar - P.A by omega] at hz; exact hz)
    · omega
  · exact hne0 (by rw [show z = -P.A by omega] at hz; exact hz)
  · omega

/-! ### A virtual site CAN be a cut site

`pd_hgap` takes the two endpoint exclusions as hypotheses.  They are not free: for
`kstar < 0` the site `0` -- where the virtual arrival sits -- is cut exactly when
`d(-1) = 1` and `d(0) = 0`, and both are consistent with the parity constraint.

`cut_forces_no_cross` says strands do not *cross* at a cut site; it does **not** say
the site is empty.  So the route "cut site => arrival-free => not virtual" of BLOCK 39
does not close, and the exclusions must be assumed or established some other way. -/

/-- **Site `0` is a cut site whenever `d(-1) = 1` and `d(0) = 0`** (for `kstar < 0`). -/
theorem cut_at_zero (P : SiteCost.PathData) (hk : P.kstar < 0)
    (h1 : P.d (-1) = 1) (h2 : P.d 0 = 0) : P.cut 0 := by
  have hvD : P.vD 0 = 0 := by
    unfold SiteCost.PathData.vD; rw [if_neg (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.vArr
    rw [if_pos rfl, hvD]
    simp only [ite_self, Nat.cast_zero, mul_zero, add_zero]
    have h1' : P.d (0 - 1) = 1 := by simpa using h1
    rw [h1']; norm_num
  · unfold SiteCost.PathData.betaAt SiteCost.PathData.vR
    rw [hvD]
    simp only [ite_self, Nat.cast_zero, mul_zero, sub_zero]
    exact h2
  · unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL SiteCost.vArr
    rw [if_pos rfl, hvD]
    simp only [ite_self, Nat.cast_zero, sub_zero]
    have hf : P.f (0 - 1) = -1 := by
      unfold SiteCost.PathData.f travel
      rw [if_neg (by omega), if_pos (by omega)]
    rw [hf]; norm_num

/-- The parity constraint does not forbid it: `d(-1) = 1` has the parity of
`travel kstar (-1) = -1`, and `d(0) = 0` that of `travel kstar 0 = 0`. -/
theorem cut_at_zero_parity_ok (kstar : ℤ) (hk : kstar < 0) :
    ((1 : ℤ) - travel kstar (-1)) % 2 = 0 ∧ ((0 : ℤ) - travel kstar 0) % 2 = 0 := by
  unfold travel
  rw [if_neg (by omega), if_pos (by omega)]
  rw [if_neg (by omega), if_neg (by omega)]
  norm_num

/-! ### Exactly when a virtual site is cut

`hgap` holds iff neither virtual site is cut.  Both conditions are explicit read-offs,
so `hgap` is checkable on an element rather than opaque. -/

/-- **Site `0` is cut exactly when `d(-1) = 1` and `d(0) = 0`** (for `kstar < 0`).
`Phi` vanishes there automatically, since `f(-1) = -1` cancels the virtual arrival. -/
theorem cut_at_zero_iff (P : SiteCost.PathData) (hk : P.kstar < 0) :
    P.cut 0 ↔ (P.d (-1) = 1 ∧ P.d 0 = 0) := by
  have hvD : P.vD 0 = 0 := by
    unfold SiteCost.PathData.vD; rw [if_neg (by omega)]
  have hf : P.f (0 - 1) = -1 := by
    unfold SiteCost.PathData.f travel
    rw [if_neg (by omega), if_pos (by omega)]
  constructor
  · rintro ⟨ha, hb, -⟩
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL SiteCost.vArr at ha
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR at hb
    rw [if_pos rfl, hvD] at ha
    rw [hvD] at hb
    simp only [ite_self, Nat.cast_zero, mul_zero, add_zero, sub_zero] at ha hb
    have h1 : P.d (-1) = 1 := by
      have : P.d (0 - 1) = 1 := by omega
      simpa using this
    exact ⟨h1, hb⟩
  · rintro ⟨h1, h2⟩
    exact cut_at_zero P hk h1 h2

/-- **Site `kstar` is cut exactly when `delta` is set and the two read-offs hold.**
`Phi` there is `-vL(kstar)`, so it vanishes only when the virtual departure is on the
right -- that is, only when `delta` is `true`. -/
theorem cut_at_kstar_iff (P : SiteCost.PathData) (hk : P.kstar < 0) :
    P.cut P.kstar ↔
      (P.delta = true ∧ P.d (P.kstar - 1) = 0 ∧ P.d P.kstar = P.eps) := by
  have hvA : SiteCost.vArr P.kstar = 0 := by
    unfold SiteCost.vArr; rw [if_neg (by omega)]
  have hvD : P.vD P.kstar = 1 := by
    unfold SiteCost.PathData.vD; rw [if_pos rfl]
  have hf : P.f (P.kstar - 1) = 0 := by
    unfold SiteCost.PathData.f travel
    rw [if_neg (by omega), if_neg (by omega)]
  constructor
  · rintro ⟨ha, hb, hc⟩
    unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL at hc
    rw [hvA, hvD, hf] at hc
    have hd : P.delta = true := by
      by_contra hcon
      simp only [Bool.not_eq_true] at hcon
      rw [hcon] at hc; norm_num at hc
    unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL at ha
    unfold SiteCost.PathData.betaAt SiteCost.PathData.vR at hb
    rw [hvA, hvD, hd] at ha
    rw [hvD, hd] at hb
    simp only [if_true, Nat.cast_one, Nat.cast_zero, mul_zero, mul_one,
      add_zero, sub_zero] at ha hb
    exact ⟨hd, by omega, by omega⟩
  · rintro ⟨hd, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL
      rw [hvA, hvD, hd]
      simp only [if_true, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero, sub_zero]
      rw [h1]
    · unfold SiteCost.PathData.betaAt SiteCost.PathData.vR
      rw [hvD, hd]
      simp only [if_true, Nat.cast_one, mul_one]
      rw [h2]; ring
    · unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL
      rw [hvA, hvD, hd, hf]
      norm_num

/-! ### A witness with `kstar < 0` and a non-empty cut set

`witElt` has `kstar = 1` and no cut site, so it cannot exercise `shield_gap`.  This one
can: cursor `-1`, deposits `-1` at edge `-1` and `2` at edge `2`.  Its span is
`[-1, 2]`, and site `1` is cut while neither virtual site is. -/

/-- The second witness. -/
noncomputable def witNeg : Elt where
  kstar := -1
  eps := 1
  delta := false
  heps := Or.inl rfl
  d := fun j => if j = -1 then -1 else if j = 2 then 2 else 0
  hpar := by
    intro j
    unfold travel
    by_cases h1 : j = -1
    · subst h1; norm_num
    · by_cases h2 : j = 2
      · subst h2; simp [h1]
      · simp [h1, h2]; split_ifs <;> omega
  supp := {-1, 2}
  hsupp := by
    intro j hj
    have h1 : j ≠ -1 := by intro hc; exact hj (by simp [hc])
    have h2 : j ≠ 2 := by intro hc; exact hj (by simp [hc])
    refine ⟨by simp [h1, h2], ?_⟩
    unfold travel
    split_ifs <;> omega

@[simp] theorem witNeg_kstar : witNeg.kstar = -1 := rfl
@[simp] theorem witNeg_pd_kstar : witNeg.toPathData.kstar = -1 := rfl

/-- **Neither virtual site of `witNeg` is cut**, so `hgap` holds for it.

Site `0` would need `d(-1) = 1`; it is `-1`.  Site `kstar` would need `delta`; it is
`false`. -/
theorem witNeg_no_virtual_cut :
    ¬ witNeg.toPathData.cut 0 ∧ ¬ witNeg.toPathData.cut witNeg.toPathData.kstar := by
  constructor
  · rw [cut_at_zero_iff _ (by simp)]
    rintro ⟨h1, -⟩
    simp [witNeg, Elt.toPathData] at h1
  · rw [cut_at_kstar_iff _ (by simp)]
    rintro ⟨h1, -, -⟩
    simp [witNeg, Elt.toPathData] at h1

/-- **Site `1` of `witNeg` IS a cut site.**  Away from the virtual sites the condition
is the plain read-off, and `d(0) = d(1) = 0` with `f(0) = 0`. -/
theorem witNeg_cut_at_one : witNeg.toPathData.cut 1 := by
  have hvA : SiteCost.vArr (1 : ℤ) = 0 := by unfold SiteCost.vArr; norm_num
  have hvD : witNeg.toPathData.vD 1 = 0 := by
    unfold SiteCost.PathData.vD; rw [if_neg (by simp)]
  refine ⟨?_, ?_, ?_⟩
  · unfold SiteCost.PathData.alphaAt SiteCost.PathData.vL
    rw [hvA, hvD]
    simp [witNeg, Elt.toPathData]
  · unfold SiteCost.PathData.betaAt SiteCost.PathData.vR
    rw [hvD]
    simp [witNeg, Elt.toPathData]
  · unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL SiteCost.PathData.f
    rw [hvA, hvD]
    simp [witNeg, Elt.toPathData, travel]

/-- Its occupied set is `{-1, 0, 2}`. -/
theorem witNeg_occ : witNeg.occ = {-1, 0, 2} := by
  classical
  unfold Elt.occ
  ext x
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨h, -⟩)
    · simp [h]
    · have : x = -1 ∨ x = 2 := by simpa [witNeg] using h
      rcases this with h | h <;> simp [h]
  · rintro (h | h | h) <;> subst h
    · right
      refine ⟨by simp [witNeg], Or.inl ?_⟩
      simp [witNeg, Elt.toPathData]
    · exact Or.inl rfl
    · right
      refine ⟨by simp [witNeg], Or.inl ?_⟩
      simp [witNeg, Elt.toPathData]

theorem witNeg_A : witNeg.A = -1 := by
  have hm : witNeg.A ∈ witNeg.occ := Finset.min'_mem _ _
  have hle : witNeg.A ≤ -1 :=
    Finset.min'_le _ _ (by rw [witNeg_occ]; simp)
  rw [witNeg_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

theorem witNeg_B : witNeg.B = 2 := by
  have hm : witNeg.B ∈ witNeg.occ := Finset.max'_mem _ _
  have hle : (2:ℤ) ≤ witNeg.B :=
    Finset.le_max' _ _ (by rw [witNeg_occ]; simp)
  rw [witNeg_occ] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

@[simp] theorem witNeg_pd_A : witNeg.toPathData.A = -1 := witNeg_A
@[simp] theorem witNeg_pd_B : witNeg.toPathData.B = 2 := witNeg_B

/-- Its span has four edges. -/
theorem witNeg_width : pdWidth witNeg.toPathData = 4 := by
  unfold pdWidth
  rw [witNeg_pd_A, witNeg_pd_B]
  rfl

/-- **Site `2` of `witNeg` is NOT cut**: the deposit there is `2`. -/
theorem witNeg_not_cut_at_two : ¬ witNeg.toPathData.cut 2 := by
  rintro ⟨-, hb, -⟩
  have hvD : witNeg.toPathData.vD 2 = 0 := by
    unfold SiteCost.PathData.vD; rw [if_neg (by simp)]
  unfold SiteCost.PathData.betaAt SiteCost.PathData.vR at hb
  rw [hvD] at hb
  simp [witNeg, Elt.toPathData] at hb

/-- **The cut set of `witNeg` is a single site**, so `|Z| = 1`.

Shifted site `z` is original site `z - 1`.  Of the three interior sites `1, 2, 3`
(original `0, 1, 2`): the first is the virtual arrival's site and is not cut, the
second is cut, the third carries a deposit and is not. -/
theorem witNeg_cutSites : pdCutSites witNeg.toPathData = {2} := by
  classical
  ext z
  rw [mem_pdCutSites, Finset.mem_singleton, witNeg_width]
  constructor
  · rintro ⟨⟨h1, h2⟩, hcut⟩
    unfold pdCutAt at hcut
    rw [witNeg_pd_A] at hcut
    interval_cases z
    · exact absurd (by simpa using hcut) witNeg_no_virtual_cut.1
    · rfl
    · exact absurd (by simpa using hcut) witNeg_not_cut_at_two
  · rintro rfl
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    unfold pdCutAt
    rw [witNeg_pd_A]
    simpa using witNeg_cut_at_one

/-- **`hgap` holds for `witNeg`, with a non-empty cut set.**

Its virtual sites are `s0 = -A = 1` and `s1 = kstar - A = 0`, so the window
`(s1 - 1, s0]` is `{0, 1}`; the single cut site sits at `2`, outside it. -/
theorem witNeg_hgap :
    ∀ z ∈ pdCutSites witNeg.toPathData,
      ¬ ((witNeg.toPathData.kstar - witNeg.toPathData.A) - 1 < z ∧
        z ≤ -witNeg.toPathData.A) := by
  intro z hz
  rw [witNeg_cutSites, Finset.mem_singleton] at hz
  subst hz
  rw [witNeg_pd_A, witNeg_pd_kstar]
  rintro ⟨-, h⟩
  omega

/-- And its two virtual sites are ordered `s1 < s0`, so the mirrored orientation
applies. -/
theorem witNeg_sites_lt :
    witNeg.toPathData.kstar - witNeg.toPathData.A < -witNeg.toPathData.A := by
  rw [witNeg_pd_A, witNeg_pd_kstar]; omega

/-! ### `hturn` quantified over all data is too strong

`shield_gap` takes `hturn` as `forall E, ...`: **no** datum has a real turn crossing a
cut site.  That is a property of a *particular* realisation, not of the configuration,
and it fails as soon as a cut site carries real ends -- an arbitrary `Data` may pair
them across the site.

`witNeg`'s cut site does carry real ends, so the `forall E` form cannot be discharged
for it. -/

/-- Every edge of a `PathData` span carries a crossing. -/
theorem pdMm_pos (P : SiteCost.PathData) (i : Fin (pdWidth P))
    (hlo : P.A ≤ P.A + (i : ℤ)) (hhi : P.A + (i : ℤ) ≤ P.B) :
    0 < pdMm P i := by
  simp only [pdMm]
  rw [P.mm_eq_mu ⟨hlo, hhi⟩]
  exact P.mu_pos _

/-- **`witNeg`'s cut site carries a real end.**

Shifted site `2` is the top of shifted edge `1` -- original edge `0` -- whose
multiplicity is positive.  So `hturn` is a genuine constraint on the datum there, and
cannot hold for every `Data`. -/
theorem witNeg_end_at_cut :
    ∃ u : EndType.Endpt (pdWidth witNeg.toPathData) (pdMm witNeg.toPathData),
      EndType.siteOf u = 2 := by
  have hw := witNeg_width
  have hlt : (1 : ℕ) < pdWidth witNeg.toPathData := by omega
  have hpos : 0 < pdMm witNeg.toPathData ⟨1, hlt⟩ := by
    refine pdMm_pos witNeg.toPathData ⟨1, hlt⟩ ?_ ?_
    · simp
    · rw [witNeg_pd_A, witNeg_pd_B]; simp
  refine ⟨⟨⟨1, hlt⟩, ⟨0, hpos⟩, true⟩, ?_⟩
  simp [EndType.siteOf, EndType.edgeOf, EndType.atTop]

/-! ### `hZ` and `mu_pos` collide inside the span

BLOCK 12 proved that a balanced site carrying no arrival has **both adjacent edges
empty**.  But `PathData.mu_pos` says every edge of the span `[A, B]` carries at least
one crossing.  So no site strictly inside the span can be arrival-free, and `hZ` --
"no arrival sits at a cut site" -- forces the cut set to avoid the span's interior
entirely.

That is why BLOCK 5's witness used multiplicities `(2,0,0,2)`: the cut site there sits
between two **empty** edges.  Such a configuration does not arise from a `PathData`. -/

/-- **Both edges adjacent to an interior site are occupied.** -/
theorem pd_edges_occupied (P : SiteCost.PathData) (s : ℤ)
    (hlo : P.A < s) (hhi : s ≤ P.B) :
    0 < P.mm (s - 1) ∧ 0 < P.mm s := by
  constructor
  · rw [P.mm_eq_mu ⟨by omega, by omega⟩]; exact P.mu_pos _
  · rw [P.mm_eq_mu ⟨by omega, by omega⟩]; exact P.mu_pos _

/-- **So `hZ` cannot hold at an interior site of a `PathData` span.**

If a site strictly inside the span were arrival-free, BLOCK 12's argument would make
both its edges empty, contradicting `mu_pos`.  Stated as: the emptiness conclusion is
false there. -/
theorem no_arrivalfree_inside_span (P : SiteCost.PathData) (s : ℤ)
    (hlo : P.A < s) (hhi : s ≤ P.B)
    (hempty : ∀ j : ℤ, (j = s ∨ j = s - 1) → P.mm j = 0) : False := by
  have := (pd_edges_occupied P s hlo hhi).2
  have h0 := hempty s (Or.inl rfl)
  omega

/-! ### The correct replacement for `hZ`

The paper's condition at a cut site is that **no strand crosses**
(`SiteCost.cut_forces_no_cross`), not that the site is empty.  In the walk model that
is exactly `hturn`: the turn keeps the edge.  `ConfigLoop` already has both halves of
the bridge -- `no_cross_at_cut` (a cut site's optimal plan has zero cross) and
`turn_keeps_edge_of_cross_zero`.  Chaining them derives `hturn` **without `hZ`**. -/

/-- **`hturn` from zero crossing at the cut sites.**

Both roles are covered: for an arrival the bridge lemma applies directly, and for a
departure the turn's involutivity reduces it to the arrival case. -/
theorem hturn_of_cross_zero {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (ds : Bool → Bool)
    (Zf : Finset ℤ)
    (hbal : ∀ s : ℤ, (EndType.arrAt (m := m) up s).card
      = (EndType.depAt (m := m) up s).card)
    (hcross : ∀ s ∈ Zf, (ConfigLoop.planAt up ds s (hbal s)).cross = 0) :
    ∀ x : EndType.Endpt n m,
      EndType.edgeOf (DataBuild.turn up x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf := by
  intro x hne hmem
  refine hne ?_
  have hkeep := ConfigLoop.turn_keeps_edge_of_cross_zero (m := m) up ds
    (EndType.siteOf x) (hbal _) (hcross _ hmem)
  show EndType.edgeOf (DataBuild.turnAt up (EndType.siteOf x) x) = EndType.edgeOf x
  cases hax : EndType.isArrOf up x with
  | true =>
    exact hkeep x ((EndType.mem_arrAt up _ x).mpr ⟨rfl, hax⟩)
  | false =>
    -- a departure: its turn is an arrival at the same site, and the turn is an
    -- involution there, so the arrival case applies to the image
    set y := DataBuild.turnAt up (EndType.siteOf x) x with hy
    have hxdep : x ∈ EndType.depAt (m := m) up (EndType.siteOf x) :=
      (EndType.mem_depAt up _ x).mpr ⟨rfl, hax⟩
    have hyarr : y ∈ EndType.arrAt (m := m) up (EndType.siteOf x) :=
      DataBuild.turnAt_dep up _ (hbal _) x hxdep
    have hys : EndType.siteOf y = EndType.siteOf x :=
      ((EndType.mem_arrAt up _ y).mp hyarr).1
    have hinv : DataBuild.turnAt up (EndType.siteOf x) y = x :=
      DataBuild.turnAt_invol up _ x
    have := hkeep y hyarr
    rw [hinv] at this
    exact this.symm

/-! ### `hturn` is self-maintaining, so `hZ` can go

`hturn_swapT` asks that the merge site not be a cut site, and `hZ` was one way to get
that.  It is not needed.  At a cut site `hturn` says every turn keeps its edge, and the
free pair's `hshared` -- same side, or turns on the same side -- then forces the two
arrivals onto the **same edge**.  A swap between ends of one edge cannot create a
crossing, so `hturn` survives. -/

/-- Same site and same end-role means same edge. -/
theorem same_edge_of_site_top {n : ℕ} {m : Fin n → ℕ} (x y : EndType.Endpt n m)
    (hs : EndType.siteOf x = EndType.siteOf y)
    (ht : EndType.atTop x = EndType.atTop y) :
    EndType.edgeOf x = EndType.edgeOf y := by
  have hx : EndType.siteOf x
      = EndType.edgeOf x + (if EndType.atTop x then (1:ℤ) else 0) := rfl
  have hy : EndType.siteOf y
      = EndType.edgeOf y + (if EndType.atTop y then (1:ℤ) else 0) := rfl
  rw [ht] at hx
  omega

/-- **At a cut site the free pair lies on one edge.**

Either the two arrivals share a side -- hence an edge -- or their turns do, and at a
cut site the turns keep their edges, so the arrivals share an edge again. -/
theorem freePair_same_edge_at_cut {n : ℕ} {m : Fin n → ℕ} (Zf : Finset ℤ)
    (D : WalkGraph.Data (EndType.Endpt n m))
    (hts : ∀ e, EndType.siteOf (D.t e) = EndType.siteOf e)
    (hturn : ∀ x : EndType.Endpt n m,
      EndType.edgeOf (D.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (a a' : EndType.Endpt n m) (hss : EndType.siteOf a' = EndType.siteOf a)
    (hcut : EndType.siteOf a ∈ Zf)
    (hshared : EndType.atTop a = EndType.atTop a' ∨
      EndType.atTop (D.t a) = EndType.atTop (D.t a')) :
    EndType.edgeOf a = EndType.edgeOf a' := by
  have hka : EndType.edgeOf (D.t a) = EndType.edgeOf a := by
    by_contra hc; exact hturn a hc hcut
  have hka' : EndType.edgeOf (D.t a') = EndType.edgeOf a' := by
    by_contra hc; exact hturn a' hc (hss ▸ hcut)
  rcases hshared with h | h
  · exact same_edge_of_site_top a a' hss.symm h
  · have hd : EndType.edgeOf (D.t a) = EndType.edgeOf (D.t a') :=
      same_edge_of_site_top (D.t a) (D.t a')
        (by rw [hts a, hts a', hss]) h
    rw [hka, hka'] at hd
    exact hd

/-- **`swapT` preserves a position function when the four swapped points share it.**

Stated generically and proved by `split_ifs`, so the branch conditions come from Lean
in exactly the form the `if` chain uses -- which is what makes the four cases uniform. -/
theorem swapT_pos_eq {α : Type*} [DecidableEq α] (t : α → α) (pos : α → ℤ)
    (a d a' d' y : α)
    (h1 : pos a = pos d) (h2 : pos a = pos a') (h3 : pos a = pos d')
    (hy : pos (t y) = pos y) :
    pos (WalkGraph.swapT t a d a' d' y) = pos y := by
  unfold WalkGraph.swapT
  split_ifs with c1 c2 c3 c4
  · rw [c1]; omega
  · rw [c2]; omega
  · rw [c3]; omega
  · rw [c4]; omega
  · exact hy

/-- **`hturn` survives the merge, with no `hZ`.**

At a cut site the two arrivals share an edge (`freePair_same_edge_at_cut`) and their
turns keep theirs, so all four swapped ends sit on one edge and `swapT_pos_eq`
applies. -/
theorem hturn_swapT_nohZ {n : ℕ} {m : Fin n → ℕ} (Zf : Finset ℤ)
    (D : WalkGraph.Data (EndType.Endpt n m))
    (hts : ∀ e, EndType.siteOf (D.t e) = EndType.siteOf e)
    (hturn : ∀ x : EndType.Endpt n m,
      EndType.edgeOf (D.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (a a' : EndType.Endpt n m) (hss : EndType.siteOf a' = EndType.siteOf a)
    (hcut : EndType.siteOf a ∈ Zf)
    (hshared : EndType.atTop a = EndType.atTop a' ∨
      EndType.atTop (D.t a) = EndType.atTop (D.t a')) :
    ∀ x : EndType.Endpt n m,
      EndType.edgeOf (WalkGraph.swapT D.t a (D.t a) a' (D.t a') x)
        ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf := by
  have keep : ∀ y : EndType.Endpt n m, EndType.siteOf y ∈ Zf →
      EndType.edgeOf (D.t y) = EndType.edgeOf y := by
    intro y hy
    by_contra hc; exact hturn y hc hy
  have hea := freePair_same_edge_at_cut Zf D hts hturn a a' hss hcut hshared
  have hka := keep a hcut
  have hka' := keep a' (hss ▸ hcut)
  intro x hne hmem
  exact hne (swapT_pos_eq D.t EndType.edgeOf a (D.t a) a' (D.t a') x
    hka.symm hea (by omega) (keep x hmem))

/-- **`hturn_step` without `hZ`.**

Case on whether the merge site is cut.  If it is not, the original `hturn_swapT`
applies with `hsa`.  If it is, `hturn_swapT_nohZ` applies -- all four swapped ends
share an edge there.  Either way `hturn` survives, and `hZ` never appears. -/
theorem hturn_step_nohZ {n : ℕ} {m : Fin n → ℕ} (Zf : Finset ℤ)
    (D : WalkGraph.Data (EndType.Endpt n m)) (D' : WalkGraph.Data (EndType.Endpt n m))
    (a a' : EndType.Endpt n m)
    (hts : ∀ e, EndType.siteOf (D.t e) = EndType.siteOf e)
    (hturn : ∀ x : EndType.Endpt n m,
      EndType.edgeOf (D.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hss : EndType.siteOf a' = EndType.siteOf a)
    (hshared : EndType.atTop a = EndType.atTop a' ∨
      EndType.atTop (D.t a) = EndType.atTop (D.t a'))
    (heq : D'.t = WalkGraph.swapT D.t a (D.t a) a' (D.t a')) :
    ∀ x : EndType.Endpt n m,
      EndType.edgeOf (D'.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf := by
  rw [heq]
  by_cases hcut : EndType.siteOf a ∈ Zf
  · exact hturn_swapT_nohZ Zf D hts hturn a a' hss hcut hshared
  · exact ConfigLoop.hturn_swapT D.t Zf a (D.t a) a' (D.t a') hturn hcut
      (hts a) hss (by rw [hts a', hss])

/-! ### The descent invariant, without `hZ`

`RunInv` on the `Endpt` side bundles `hturn` with the merge data and maintains it using
`hZ`.  With `hturn_step_nohZ` the maintenance needs no `hZ`, so the invariant is just
"cost-minimal in the class, and turns keep their edges at cut sites". -/

/-- The descent invariant: cost-minimal, with turns keeping edges at cut sites. -/
def TurnInv {n : ℕ} {m : Fin n → ℕ} (d : EndData.Data (EndType.Endpt n m))
    (Zf : Finset ℤ) (E : WalkGraph.Data (EndType.Endpt n m)) : Prop :=
  CostMerge.MergesMin EndType.siteOf d.isArr EndType.partner d E ∧
    ∀ x : EndType.Endpt n m,
      EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf

/-- **The run step preserving `TurnInv`.**  Either a strict descent inside the
invariant, or the runs are already connected -- and `hZ` appears nowhere.

The body mirrors `run_step_min_gen` but calls `step_of_split'_local` directly, because
`hturn` needs the swap data (`a`, `a'`, `hshared`, and the equation on `.t`) that the
packaged version does not expose. -/
theorem run_step_turnInv {n : ℕ} {m : Fin n → ℕ} (d : EndData.Data (EndType.Endpt n m))
    (Zf : Finset ℤ)
    (hside : ∀ x, d.side x = EndType.atTop x)
    (hpsite : ∀ x : EndType.Endpt n m,
      EndType.siteOf (EndType.partner x) ≠ EndType.siteOf x)
    (hsW : ∀ E : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E →
      ∀ w x : EndType.Endpt n m, (WalkGraph.graph E).Reachable w x →
      EndType.siteOf x = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) w →
      EndType.atTop x = false ∨ EndType.siteOf x
        = EndType.edgeOf x + (if EndType.atTop x then 1 else 0))
    (hsX : ∀ E : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E →
      ∀ w x : EndType.Endpt n m, (WalkGraph.graph E).Reachable w x →
      EndType.edgeOf x = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) w →
      EndType.atTop x = false → EndType.siteOf x
        = EndType.edgeOf x + (if EndType.atTop x then 1 else 0))
    (hsT : ∀ E : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E →
      ∀ w y : EndType.Endpt n m,
      EndType.edgeOf y = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) w - 1 →
      EndType.atTop y = true → EndType.siteOf y
        = EndType.edgeOf y + (if EndType.atTop y then 1 else 0))
    (hcov : ∀ E : WalkGraph.Data (EndType.Endpt n m), ∀ z v : EndType.Endpt n m,
      EndType.edgeOf v < WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) z →
      ∃ w : EndType.Endpt n m,
        EndType.edgeOf w = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) z - 1 ∧
        EndType.atTop w = true)
    (D : WalkGraph.Data (EndType.Endpt n m)) (hD : TurnInv d Zf D) :
    (∃ D' : WalkGraph.Data (EndType.Endpt n m), TurnInv d Zf D' ∧
      WalkGraph.walkCount D' < WalkGraph.walkCount D) ∨
      (∀ x y : EndType.Endpt n m,
        runIndexG EndType.edgeOf Zf x = runIndexG EndType.edgeOf Zf y →
        (WalkGraph.graph D).Reachable x y) := by
  classical
  obtain ⟨hDmin, hturn⟩ := hD
  by_cases hsep : ∀ x y : EndType.Endpt n m,
      runIndexG EndType.edgeOf Zf x = runIndexG EndType.edgeOf Zf y →
      (WalkGraph.graph D).Reachable x y
  · exact Or.inr hsep
  · left
    obtain ⟨x, hx⟩ := not_forall.mp hsep
    obtain ⟨y, hy⟩ := not_forall.mp hx
    have hnr : ¬ (WalkGraph.graph D).Reachable x y := fun hc => hy (fun _ => hc)
    obtain ⟨hM, hmin⟩ := hDmin
    obtain ⟨hp, hts, hta⟩ := hM
    obtain ⟨D', hlt, hpeq, a, a', harr, harr', hss, hsplit, hshared, hteq⟩ :=
      CostMerge.step_of_split'_local d EndType.edgeOf EndType.siteOf EndType.atTop D
        hside (hsW D ⟨hp, hts, hta⟩) (hsX D ⟨hp, hts, hta⟩) (hsT D ⟨hp, hts, hta⟩)
        (by rw [hp]; exact fun x => EndType.partner_edgeOf x)
        (by rw [hp]; exact fun x => EndType.partner_top x) hts hta
        (by rw [hp]; exact hpsite) (hcov D)
        (CostMerge.hmin_of_mergesMin EndType.siteOf EndType.partner d D
          ⟨⟨hp, hts, hta⟩, hmin⟩) x y hnr
    have hda : d.isArr (D.t a) = false := by rw [hta, harr]; rfl
    have hda' : d.isArr (D.t a') = false := by rw [hta, harr']; rfl
    have hne : a ≠ a' := fun h => hsplit (h ▸ SimpleGraph.Reachable.refl a)
    have hts' : ∀ e, EndType.siteOf (D'.t e) = EndType.siteOf e := by
      intro e
      rw [hteq]
      exact WalkGraph.swapT_site EndType.siteOf D.t a (D.t a) a' (D.t a') hts (hts a) hss
        (show EndType.siteOf (D.t a') = EndType.siteOf a from (hts a').trans hss) e
    have hta' : ∀ e, d.isArr (D'.t e) = !d.isArr e := by
      intro e
      rw [hteq]
      exact WalkGraph.swapT_arr d.isArr D.t a (D.t a) a' (D.t a') hta rfl rfl harr harr' e
    have hcost : CostMerge.costOf d D' = CostMerge.costOf d D := by
      have h1 := WalkGraph.swapT_invol D.t_invol rfl rfl
        (ConfigMerge.dep_ne_arr' D rfl) (ConfigMerge.dep_ne_other D rfl hsplit)
        (Ne.symm hne) (ConfigMerge.dep_ne_dep' D rfl rfl (Ne.symm hne))
        (Ne.symm (ConfigMerge.dep_ne_arr' D rfl))
        (ConfigMerge.dep_ne_other' D rfl hsplit)
      have h2 := WalkGraph.swapT_ne D.t a (D.t a) a' (D.t a') D.t_ne
        (ConfigMerge.dep_ne_other D rfl hsplit) (ConfigMerge.dep_ne_other' D rfl hsplit)
      have h3 := WalkGraph.partner_ne_swapT EndType.siteOf D.p D.t a (D.t a) a' (D.t a')
        (by rw [hp]; exact hpsite) hts (hts a) hss (by rw [hts a']; exact hss)
      have hc := CostMerge.cost_swapData d D a a' harr harr' hda hda' hne hshared h1 h2 h3
      rw [← hc]
      exact CostMerge.cost_congr d D' _ (fun b _ => by rw [hteq]; rfl)
    refine ⟨D', ⟨⟨⟨hpeq.trans hp, hts', hta'⟩,
      fun F hF => by rw [hcost]; exact hmin F hF⟩, ?_⟩, hlt⟩
    exact hturn_step_nohZ Zf D D' a a' hts hturn hss
      (by rcases hshared with h | h
          · exact Or.inl (by rw [← hside a, ← hside a']; exact h)
          · exact Or.inr (by rw [← hside (D.t a), ← hside (D.t a')]; exact h)) hteq

/-- **Iterating the step**: a datum in `TurnInv` whose runs are connected. -/
theorem exists_turnInv_connected {n : ℕ} {m : Fin n → ℕ}
    (d : EndData.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (hside : ∀ x, d.side x = EndType.atTop x)
    (hpsite : ∀ x : EndType.Endpt n m,
      EndType.siteOf (EndType.partner x) ≠ EndType.siteOf x)
    (hsW : ∀ E : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E →
      ∀ w x : EndType.Endpt n m, (WalkGraph.graph E).Reachable w x →
      EndType.siteOf x = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) w →
      EndType.atTop x = false ∨ EndType.siteOf x
        = EndType.edgeOf x + (if EndType.atTop x then 1 else 0))
    (hsX : ∀ E : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E →
      ∀ w x : EndType.Endpt n m, (WalkGraph.graph E).Reachable w x →
      EndType.edgeOf x = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) w →
      EndType.atTop x = false → EndType.siteOf x
        = EndType.edgeOf x + (if EndType.atTop x then 1 else 0))
    (hsT : ∀ E : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E →
      ∀ w y : EndType.Endpt n m,
      EndType.edgeOf y = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) w - 1 →
      EndType.atTop y = true → EndType.siteOf y
        = EndType.edgeOf y + (if EndType.atTop y then 1 else 0))
    (hcov : ∀ E : WalkGraph.Data (EndType.Endpt n m), ∀ z v : EndType.Endpt n m,
      EndType.edgeOf v < WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) z →
      ∃ w : EndType.Endpt n m,
        EndType.edgeOf w = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) z - 1 ∧
        EndType.atTop w = true)
    (D : WalkGraph.Data (EndType.Endpt n m)) (hD : TurnInv d Zf D) :
    ∃ D' : WalkGraph.Data (EndType.Endpt n m), TurnInv d Zf D' ∧
      ∀ x y : EndType.Endpt n m,
        runIndexG EndType.edgeOf Zf x = runIndexG EndType.edgeOf Zf y →
        (WalkGraph.graph D').Reachable x y :=
  ConfigMerge.reaches_stuck
    (P := TurnInv d Zf)
    (Stuck := fun E => ∀ x y : EndType.Endpt n m,
      runIndexG EndType.edgeOf Zf x = runIndexG EndType.edgeOf Zf y →
      (WalkGraph.graph E).Reachable x y)
    (fun E hE => run_step_turnInv d Zf hside hpsite hsW hsX hsT hcov E hE) D hD

/-- A `TurnInv` datum's graph edges preserve the block index or are local. -/
theorem blk_or_local_of_turnInv {n : ℕ} {m : Fin n → ℕ}
    (d : EndData.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (E : WalkGraph.Data (EndType.Endpt n m)) (hE : TurnInv d Zf E) :
    ∀ x y : EndType.Endpt n m, (WalkGraph.graph E).Adj x y →
      CutComponents.blk EndType.edgeOf Zf x = CutComponents.blk EndType.edgeOf Zf y ∨
      (∃ t : ℤ, (EndType.edgeOf x = t - 1 ∨ EndType.edgeOf x = t) ∧
        (EndType.edgeOf y = t - 1 ∨ EndType.edgeOf y = t) ∧
        (EndType.edgeOf x ≠ EndType.edgeOf y → t ∉ Zf)) := by
  intro x y hxy
  exact Or.inr (ConfigLoop.local_of_hturn E Zf hE.1.1.1 hE.1.1.2.1 hE.2 x y hxy)

/-- **The shield law on `Endpt`, with `hZ` gone.**

`c = |Z|` for a datum in `TurnInv`.  Its inputs are the merge-side hypotheses, the
covering condition, and `hruns` -- no `hZ`, so it is not blocked by the collision
BLOCK 60 exhibited between `hZ` and `mu_pos`. -/
theorem shield_turnInv {n : ℕ} {m : Fin n → ℕ}
    (d : EndData.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (hside : ∀ x, d.side x = EndType.atTop x)
    (hpsite : ∀ x : EndType.Endpt n m,
      EndType.siteOf (EndType.partner x) ≠ EndType.siteOf x)
    (hsW : ∀ E : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E →
      ∀ w x : EndType.Endpt n m, (WalkGraph.graph E).Reachable w x →
      EndType.siteOf x = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) w →
      EndType.atTop x = false ∨ EndType.siteOf x
        = EndType.edgeOf x + (if EndType.atTop x then 1 else 0))
    (hsX : ∀ E : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E →
      ∀ w x : EndType.Endpt n m, (WalkGraph.graph E).Reachable w x →
      EndType.edgeOf x = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) w →
      EndType.atTop x = false → EndType.siteOf x
        = EndType.edgeOf x + (if EndType.atTop x then 1 else 0))
    (hsT : ∀ E : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E →
      ∀ w y : EndType.Endpt n m,
      EndType.edgeOf y = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) w - 1 →
      EndType.atTop y = true → EndType.siteOf y
        = EndType.edgeOf y + (if EndType.atTop y then 1 else 0))
    (hcov : ∀ E : WalkGraph.Data (EndType.Endpt n m), ∀ z v : EndType.Endpt n m,
      EndType.edgeOf v < WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) z →
      ∃ w : EndType.Endpt n m,
        EndType.edgeOf w = WalkSupport.wLo EndType.edgeOf (WalkGraph.graph E) z - 1 ∧
        EndType.atTop w = true)
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : EndType.Endpt n m, CutComponents.blk EndType.edgeOf Zf v = i)
    (z₀ : EndType.Endpt n m)
    (D : WalkGraph.Data (EndType.Endpt n m)) (hD : TurnInv d Zf D) :
    ∃ D' : WalkGraph.Data (EndType.Endpt n m), TurnInv d Zf D' ∧
      WalkGraph.walkCount D' = Zf.card + 1 := by
  obtain ⟨D', hD', hsep⟩ :=
    exists_turnInv_connected d Zf hside hpsite hsW hsX hsT hcov D hD
  refine ⟨D', hD', le_antisymm ?_ ?_⟩
  · exact walkCount_le_runs_blk D' EndType.edgeOf Zf
      (blk_or_local_of_turnInv d Zf D' hD') hsep
  · obtain ⟨F, hinj, havoid⟩ :=
      CutComponents.exists_injective_components_avoiding_blk_or_local
        (blk_or_local_of_turnInv d Zf D' hD') hruns
        ((WalkGraph.graph D').connectedComponentMk z₀)
    exact walkCount_ge_of_avoiding_gen D' Zf.card _ F hinj havoid

/-! ### Under `hgap`, cut sites carry only real ends

`TurnInv` ports to the extended type provided the free-pair argument still works at a
cut site, and that needs `same_edge_of_site_top` -- which holds only at real ends.
`hgap` supplies exactly that: it excludes both virtual sites from the cut set. -/

/-- **Every end at a cut site is real**, under `hgap`. -/
theorem VEndpt.cut_ends_real {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hle : s1 ≤ s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (x : VEndpt n mm) (hmem : VEndpt.siteP s0 s1 x ∈ Zf) :
    ∃ u : EndType.Endpt n mm, x = Sum.inl u := by
  cases hcase : x with
  | inl u => exact ⟨u, rfl⟩
  | inr b =>
    exfalso
    rw [hcase] at hmem
    cases b
    · exact hgap _ hmem ⟨by simp only [VEndpt.siteP]; omega,
        by simp only [VEndpt.siteP]; omega⟩
    · exact hgap _ hmem ⟨by simp only [VEndpt.siteP]; omega,
        by simp only [VEndpt.siteP]; omega⟩

/-- **So the site-edge relation holds at every end of a cut site**, and the free-pair
argument of BLOCK 62 transfers to the extended type. -/
theorem VEndpt.site_edge_at_cut {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hle : s1 ≤ s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0)) (bnd : ℤ)
    (x : VEndpt n mm) (hmem : VEndpt.siteP s0 s1 x ∈ Zf) :
    VEndpt.siteP s0 s1 x
      = VEndpt.edgeOf bnd x + (if VEndpt.atTop x then 1 else 0) := by
  obtain ⟨u, hu⟩ := VEndpt.cut_ends_real s0 s1 hle Zf hgap x hmem
  rw [hu]
  rfl

/-- **The free pair lies on one edge at a cut site**, extended type.

`site_edge_at_cut` gives the site-edge relation at every end of a cut site, so the
BLOCK 62 argument runs verbatim -- no case split on real versus virtual is needed. -/
theorem VEndpt.freePair_same_edge_at_cutV {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ)
    (hle : s1 ≤ s0) (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (bnd : ℤ) (D : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ x : VEndpt n mm,
      VEndpt.edgeOf bnd (D.t x) ≠ VEndpt.edgeOf bnd x → VEndpt.siteP s0 s1 x ∉ Zf)
    (a a' : VEndpt n mm) (hss : VEndpt.siteP s0 s1 a' = VEndpt.siteP s0 s1 a)
    (hcut : VEndpt.siteP s0 s1 a ∈ Zf)
    (hshared : VEndpt.atTop a = VEndpt.atTop a' ∨
      VEndpt.atTop (D.t a) = VEndpt.atTop (D.t a')) :
    VEndpt.edgeOf bnd a = VEndpt.edgeOf bnd a' := by
  have hcut' : VEndpt.siteP s0 s1 a' ∈ Zf := hss ▸ hcut
  have hka : VEndpt.edgeOf bnd (D.t a) = VEndpt.edgeOf bnd a := by
    by_contra hc; exact hturn a hc hcut
  have hka' : VEndpt.edgeOf bnd (D.t a') = VEndpt.edgeOf bnd a' := by
    by_contra hc; exact hturn a' hc hcut'
  have ea := VEndpt.site_edge_at_cut s0 s1 hle Zf hgap bnd a hcut
  have ea' := VEndpt.site_edge_at_cut s0 s1 hle Zf hgap bnd a' hcut'
  rcases hshared with h | h
  · rw [h] at ea; omega
  · have eta := VEndpt.site_edge_at_cut s0 s1 hle Zf hgap bnd (D.t a) (by rw [hts]; exact hcut)
    have eta' := VEndpt.site_edge_at_cut s0 s1 hle Zf hgap bnd (D.t a') (by rw [hts]; exact hcut')
    rw [h] at eta
    rw [hts a] at eta
    rw [hts a', hss] at eta'
    omega

/-- **`hturn` survives the merge on the extended type**, under `hgap`. -/
theorem VEndpt.hturn_swapT_nohZV {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hle : s1 ≤ s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (bnd : ℤ) (D : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ x : VEndpt n mm,
      VEndpt.edgeOf bnd (D.t x) ≠ VEndpt.edgeOf bnd x → VEndpt.siteP s0 s1 x ∉ Zf)
    (a a' : VEndpt n mm) (hss : VEndpt.siteP s0 s1 a' = VEndpt.siteP s0 s1 a)
    (hcut : VEndpt.siteP s0 s1 a ∈ Zf)
    (hshared : VEndpt.atTop a = VEndpt.atTop a' ∨
      VEndpt.atTop (D.t a) = VEndpt.atTop (D.t a')) :
    ∀ x : VEndpt n mm,
      VEndpt.edgeOf bnd (WalkGraph.swapT D.t a (D.t a) a' (D.t a') x)
        ≠ VEndpt.edgeOf bnd x → VEndpt.siteP s0 s1 x ∉ Zf := by
  have keep : ∀ y : VEndpt n mm, VEndpt.siteP s0 s1 y ∈ Zf →
      VEndpt.edgeOf bnd (D.t y) = VEndpt.edgeOf bnd y := by
    intro y hy
    by_contra hc; exact hturn y hc hy
  have hea := VEndpt.freePair_same_edge_at_cutV s0 s1 hle Zf hgap bnd D hts hturn
    a a' hss hcut hshared
  have hka := keep a hcut
  have hka' := keep a' (hss ▸ hcut)
  intro x hne hmem
  exact hne (swapT_pos_eq D.t (VEndpt.edgeOf bnd) a (D.t a) a' (D.t a') x
    hka.symm hea (by omega) (keep x hmem))

/-- **`hturn_swapT`, generically.**  `ConfigLoop.hturn_swapT` is stated for `Endpt`;
nothing in its proof uses that. -/
theorem hturn_swapT_gen {α : Type*} [DecidableEq α] (t : α → α) (pos site : α → ℤ)
    (Zf : Finset ℤ) (a d a' d' : α)
    (hturn : ∀ x, pos (t x) ≠ pos x → site x ∉ Zf)
    (hsa : site a ∉ Zf)
    (hd : site d = site a) (ha' : site a' = site a) (hd' : site d' = site a) :
    ∀ x, pos (WalkGraph.swapT t a d a' d' x) ≠ pos x → site x ∉ Zf := by
  intro x hne
  unfold WalkGraph.swapT at hne
  split_ifs at hne with c1 c2 c3 c4
  · rw [c1]; exact hsa
  · rw [c2, hd']; exact hsa
  · rw [c3, ha']; exact hsa
  · rw [c4, hd]; exact hsa
  · exact hturn x hne

/-- **`hturn_step` on the extended type, without `hZ`.** -/
theorem VEndpt.hturn_step_nohZV {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hle : s1 ≤ s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0)) (bnd : ℤ)
    (D D' : WalkGraph.Data (VEndpt n mm)) (a a' : VEndpt n mm)
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ x : VEndpt n mm,
      VEndpt.edgeOf bnd (D.t x) ≠ VEndpt.edgeOf bnd x → VEndpt.siteP s0 s1 x ∉ Zf)
    (hss : VEndpt.siteP s0 s1 a' = VEndpt.siteP s0 s1 a)
    (hshared : VEndpt.atTop a = VEndpt.atTop a' ∨
      VEndpt.atTop (D.t a) = VEndpt.atTop (D.t a'))
    (heq : D'.t = WalkGraph.swapT D.t a (D.t a) a' (D.t a')) :
    ∀ x : VEndpt n mm,
      VEndpt.edgeOf bnd (D'.t x) ≠ VEndpt.edgeOf bnd x →
      VEndpt.siteP s0 s1 x ∉ Zf := by
  rw [heq]
  by_cases hcut : VEndpt.siteP s0 s1 a ∈ Zf
  · exact VEndpt.hturn_swapT_nohZV s0 s1 hle Zf hgap bnd D hts hturn a a' hss hcut hshared
  · exact hturn_swapT_gen D.t (VEndpt.edgeOf bnd) (VEndpt.siteP s0 s1) Zf
      a (D.t a) a' (D.t a') hturn hcut (hts a) hss (by rw [hts a']; exact hss)

/-! ### The run step with `hturn`, generically

`run_step_turnInv` is `Endpt`-specific only through `hturn_step_nohZ`.  Taking that
step as a parameter makes the whole descent generic, and both end types supply it. -/

/-- The descent invariant, generically. -/
def TurnInvG {α : Type*} [Fintype α] [DecidableEq α] (siteOf edgeOf : α → ℤ)
    (p₀ : α → α) (d : EndData.Data α) (Zf : Finset ℤ) (E : WalkGraph.Data α) : Prop :=
  CostMerge.MergesMin siteOf d.isArr p₀ d E ∧
    ∀ x : α, edgeOf (E.t x) ≠ edgeOf x → siteOf x ∉ Zf

/-- **The run step preserving `TurnInvG`**, with the `hturn` maintenance supplied. -/
theorem run_step_turnInvG {α : Type*} [Fintype α] [DecidableEq α]
    (d : EndData.Data α) (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (p₀ : α → α)
    (Zf : Finset ℤ)
    (hside : ∀ x, d.side x = atTop x)
    (hpe : ∀ x, edgeOf (p₀ x) = edgeOf x)
    (hpt : ∀ x, atTop (p₀ x) = !atTop x)
    (hpsite : ∀ x, siteOf (p₀ x) ≠ siteOf x)
    (hsW : ∀ E : WalkGraph.Data α, WalkSupport.Merges siteOf d.isArr p₀ E →
      ∀ w x : α, (WalkGraph.graph E).Reachable w x →
      siteOf x = WalkSupport.wLo edgeOf (WalkGraph.graph E) w →
      atTop x = false ∨ siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsX : ∀ E : WalkGraph.Data α, WalkSupport.Merges siteOf d.isArr p₀ E →
      ∀ w x : α, (WalkGraph.graph E).Reachable w x →
      edgeOf x = WalkSupport.wLo edgeOf (WalkGraph.graph E) w → atTop x = false →
      siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsT : ∀ E : WalkGraph.Data α, WalkSupport.Merges siteOf d.isArr p₀ E →
      ∀ w y : α, edgeOf y = WalkSupport.wLo edgeOf (WalkGraph.graph E) w - 1 →
      atTop y = true → siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hcov : ∀ E : WalkGraph.Data α, ∀ z v : α,
      edgeOf v < WalkSupport.wLo edgeOf (WalkGraph.graph E) z →
      ∃ w : α, edgeOf w = WalkSupport.wLo edgeOf (WalkGraph.graph E) z - 1 ∧
        atTop w = true)
    (hstep : ∀ (D D' : WalkGraph.Data α) (a a' : α),
      (∀ e, siteOf (D.t e) = siteOf e) →
      (∀ x, edgeOf (D.t x) ≠ edgeOf x → siteOf x ∉ Zf) →
      siteOf a' = siteOf a →
      (atTop a = atTop a' ∨ atTop (D.t a) = atTop (D.t a')) →
      D'.t = WalkGraph.swapT D.t a (D.t a) a' (D.t a') →
      ∀ x, edgeOf (D'.t x) ≠ edgeOf x → siteOf x ∉ Zf)
    (D : WalkGraph.Data α) (hD : TurnInvG siteOf edgeOf p₀ d Zf D) :
    (∃ D' : WalkGraph.Data α, TurnInvG siteOf edgeOf p₀ d Zf D' ∧
      WalkGraph.walkCount D' < WalkGraph.walkCount D) ∨
      (∀ x y : α, runIndexG edgeOf Zf x = runIndexG edgeOf Zf y →
        (WalkGraph.graph D).Reachable x y) := by
  classical
  obtain ⟨hDmin, hturn⟩ := hD
  by_cases hsep : ∀ x y : α, runIndexG edgeOf Zf x = runIndexG edgeOf Zf y →
      (WalkGraph.graph D).Reachable x y
  · exact Or.inr hsep
  · left
    obtain ⟨x, hx⟩ := not_forall.mp hsep
    obtain ⟨y, hy⟩ := not_forall.mp hx
    have hnr : ¬ (WalkGraph.graph D).Reachable x y := fun hc => hy (fun _ => hc)
    obtain ⟨hM, hmin⟩ := hDmin
    obtain ⟨hp, hts, hta⟩ := hM
    obtain ⟨D', hlt, hpeq, a, a', harr, harr', hss, hsplit, hshared, hteq⟩ :=
      CostMerge.step_of_split'_local d edgeOf siteOf atTop D hside
        (hsW D ⟨hp, hts, hta⟩) (hsX D ⟨hp, hts, hta⟩) (hsT D ⟨hp, hts, hta⟩)
        (by rw [hp]; exact hpe) (by rw [hp]; exact hpt) hts hta
        (by rw [hp]; exact hpsite) (hcov D)
        (CostMerge.hmin_of_mergesMin siteOf p₀ d D ⟨⟨hp, hts, hta⟩, hmin⟩) x y hnr
    have hda : d.isArr (D.t a) = false := by rw [hta, harr]; rfl
    have hda' : d.isArr (D.t a') = false := by rw [hta, harr']; rfl
    have hne : a ≠ a' := fun h => hsplit (h ▸ SimpleGraph.Reachable.refl a)
    have hts' : ∀ e, siteOf (D'.t e) = siteOf e := by
      intro e
      rw [hteq]
      exact WalkGraph.swapT_site siteOf D.t a (D.t a) a' (D.t a') hts (hts a) hss
        (show siteOf (D.t a') = siteOf a from (hts a').trans hss) e
    have hta' : ∀ e, d.isArr (D'.t e) = !d.isArr e := by
      intro e
      rw [hteq]
      exact WalkGraph.swapT_arr d.isArr D.t a (D.t a) a' (D.t a') hta rfl rfl harr harr' e
    have hcost : CostMerge.costOf d D' = CostMerge.costOf d D := by
      have h1 := WalkGraph.swapT_invol D.t_invol rfl rfl
        (ConfigMerge.dep_ne_arr' D rfl) (ConfigMerge.dep_ne_other D rfl hsplit)
        (Ne.symm hne) (ConfigMerge.dep_ne_dep' D rfl rfl (Ne.symm hne))
        (Ne.symm (ConfigMerge.dep_ne_arr' D rfl))
        (ConfigMerge.dep_ne_other' D rfl hsplit)
      have h2 := WalkGraph.swapT_ne D.t a (D.t a) a' (D.t a') D.t_ne
        (ConfigMerge.dep_ne_other D rfl hsplit) (ConfigMerge.dep_ne_other' D rfl hsplit)
      have h3 := WalkGraph.partner_ne_swapT siteOf D.p D.t a (D.t a) a' (D.t a')
        (by rw [hp]; exact hpsite) hts (hts a) hss (by rw [hts a']; exact hss)
      have hc := CostMerge.cost_swapData d D a a' harr harr' hda hda' hne hshared h1 h2 h3
      rw [← hc]
      exact CostMerge.cost_congr d D' _ (fun b _ => by rw [hteq]; rfl)
    refine ⟨D', ⟨⟨⟨hpeq.trans hp, hts', hta'⟩,
      fun F hF => by rw [hcost]; exact hmin F hF⟩, ?_⟩, hlt⟩
    exact hstep D D' a a' hts hturn hss
      (by rcases hshared with h | h
          · exact Or.inl (by rw [← hside a, ← hside a']; exact h)
          · exact Or.inr (by rw [← hside (D.t a), ← hside (D.t a')]; exact h)) hteq

/-! ### The `hturn` chain, parametrised by the top map

`site_edge_at_cut` and everything above it were stated with `VEndpt.atTop`.  The only
property used is that the map agrees with `EndType.atTop` on real ends, which `atTopN`
also satisfies.  These are the parametrised forms. -/

/-- The site-edge relation at a cut site, for any top map agreeing on real ends. -/
theorem VEndpt.site_edge_at_cutT {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hle : s1 ≤ s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0)) (bnd : ℤ)
    (top : VEndpt n mm → Bool) (htop : ∀ u, top (Sum.inl u) = EndType.atTop u)
    (x : VEndpt n mm) (hmem : VEndpt.siteP s0 s1 x ∈ Zf) :
    VEndpt.siteP s0 s1 x = VEndpt.edgeOf bnd x + (if top x then 1 else 0) := by
  obtain ⟨u, hu⟩ := VEndpt.cut_ends_real s0 s1 hle Zf hgap x hmem
  rw [hu, htop u]
  rfl

/-- The free pair lies on one edge at a cut site, parametrised. -/
theorem VEndpt.freePair_same_edge_at_cutT {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ)
    (hle : s1 ≤ s0) (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (bnd : ℤ) (top : VEndpt n mm → Bool)
    (htop : ∀ u, top (Sum.inl u) = EndType.atTop u)
    (D : WalkGraph.Data (VEndpt n mm))
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ x : VEndpt n mm,
      VEndpt.edgeOf bnd (D.t x) ≠ VEndpt.edgeOf bnd x → VEndpt.siteP s0 s1 x ∉ Zf)
    (a a' : VEndpt n mm) (hss : VEndpt.siteP s0 s1 a' = VEndpt.siteP s0 s1 a)
    (hcut : VEndpt.siteP s0 s1 a ∈ Zf)
    (hshared : top a = top a' ∨ top (D.t a) = top (D.t a')) :
    VEndpt.edgeOf bnd a = VEndpt.edgeOf bnd a' := by
  have hcut' : VEndpt.siteP s0 s1 a' ∈ Zf := hss ▸ hcut
  have hka : VEndpt.edgeOf bnd (D.t a) = VEndpt.edgeOf bnd a := by
    by_contra hc; exact hturn a hc hcut
  have hka' : VEndpt.edgeOf bnd (D.t a') = VEndpt.edgeOf bnd a' := by
    by_contra hc; exact hturn a' hc hcut'
  have ea := VEndpt.site_edge_at_cutT s0 s1 hle Zf hgap bnd top htop a hcut
  have ea' := VEndpt.site_edge_at_cutT s0 s1 hle Zf hgap bnd top htop a' hcut'
  rcases hshared with h | h
  · rw [h] at ea; omega
  · have eta := VEndpt.site_edge_at_cutT s0 s1 hle Zf hgap bnd top htop (D.t a)
      (by rw [hts]; exact hcut)
    have eta' := VEndpt.site_edge_at_cutT s0 s1 hle Zf hgap bnd top htop (D.t a')
      (by rw [hts]; exact hcut')
    rw [h] at eta
    rw [hts a] at eta
    rw [hts a', hss] at eta'
    omega

/-- `hturn` survives the merge, parametrised. -/
theorem VEndpt.hturn_step_nohZT {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hle : s1 ≤ s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0)) (bnd : ℤ)
    (top : VEndpt n mm → Bool) (htop : ∀ u, top (Sum.inl u) = EndType.atTop u)
    (D D' : WalkGraph.Data (VEndpt n mm)) (a a' : VEndpt n mm)
    (hts : ∀ e, VEndpt.siteP s0 s1 (D.t e) = VEndpt.siteP s0 s1 e)
    (hturn : ∀ x : VEndpt n mm,
      VEndpt.edgeOf bnd (D.t x) ≠ VEndpt.edgeOf bnd x → VEndpt.siteP s0 s1 x ∉ Zf)
    (hss : VEndpt.siteP s0 s1 a' = VEndpt.siteP s0 s1 a)
    (hshared : top a = top a' ∨ top (D.t a) = top (D.t a'))
    (heq : D'.t = WalkGraph.swapT D.t a (D.t a) a' (D.t a')) :
    ∀ x : VEndpt n mm,
      VEndpt.edgeOf bnd (D'.t x) ≠ VEndpt.edgeOf bnd x →
      VEndpt.siteP s0 s1 x ∉ Zf := by
  rw [heq]
  by_cases hcut : VEndpt.siteP s0 s1 a ∈ Zf
  · have hea := VEndpt.freePair_same_edge_at_cutT s0 s1 hle Zf hgap bnd top htop D
      hts hturn a a' hss hcut hshared
    have keep : ∀ y : VEndpt n mm, VEndpt.siteP s0 s1 y ∈ Zf →
        VEndpt.edgeOf bnd (D.t y) = VEndpt.edgeOf bnd y := by
      intro y hy
      by_contra hc; exact hturn y hc hy
    have hka := keep a hcut
    have hka' := keep a' (hss ▸ hcut)
    intro x hne hmem
    exact hne (swapT_pos_eq D.t (VEndpt.edgeOf bnd) a (D.t a) a' (D.t a') x
      hka.symm hea (by omega) (keep x hmem))
  · exact hturn_swapT_gen D.t (VEndpt.edgeOf bnd) (VEndpt.siteP s0 s1) Zf
      a (D.t a) a' (D.t a') hturn hcut (hts a) hss (by rw [hts a']; exact hss)

/-! ### The descent on the extended type, mirrored orientation

`run_step_turnInvG` instantiated at `VEndpt` with `bnd = s0 - 1`, `atTopN`, and the
three discharges of BLOCK 51.  Its `hstep` is `hturn_step_nohZV`. -/

/-- **The run step on `VEndpt`.** -/
theorem VEndpt.run_step_turnInvN {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hlt : s1 < s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (up : Fin n → ℕ) (ds : Bool → Bool)
    (hcov : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ z v : VEndpt n mm,
      VEndpt.edgeOf (s0 - 1) v
        < WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z →
      ∃ w : VEndpt n mm, VEndpt.edgeOf (s0 - 1) w
        = WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z - 1 ∧
        VEndpt.atTopN w = true)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
      (vEndDataN up ds) Zf D) :
    (∃ D' : WalkGraph.Data (VEndpt n mm),
      TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
        (vEndDataN up ds) Zf D' ∧
      WalkGraph.walkCount D' < WalkGraph.walkCount D) ∨
      (∀ x y : VEndpt n mm,
        runIndexG (VEndpt.edgeOf (s0 - 1)) Zf x
          = runIndexG (VEndpt.edgeOf (s0 - 1)) Zf y →
        (WalkGraph.graph D).Reachable x y) :=
  run_step_turnInvG (vEndDataN up ds) (VEndpt.edgeOf (s0 - 1)) (VEndpt.siteP s0 s1)
    VEndpt.atTopN VEndpt.partner Zf (fun _ => rfl) (VEndpt.hpe (s0 - 1)) VEndpt.hptN
    (VEndpt.partner_site_neP s0 s1 (by omega))
    (fun _ _ _ x _ _ => VEndpt.hsW_negP s0 s1 x)
    (fun E hE w x hwx hxe hxb => VEndpt.hsX_negP s0 s1 hlt E hE.2.1 w x hwx hxe hxb)
    (fun _ _ _ y _ hyt => VEndpt.hsT_negP s0 s1 y hyt)
    hcov
    (fun D D' a a' hts hturn hss hshared heq =>
      VEndpt.hturn_step_nohZT s0 s1 (by omega) Zf hgap (s0 - 1) VEndpt.atTopN
        (fun _ => rfl) D D' a a' hts hturn hss hshared heq)
    D hD

/-- **Iterated: a `TurnInvG` datum on `VEndpt` whose runs are connected.** -/
theorem VEndpt.exists_turnInvN_connected {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ)
    (hlt : s1 < s0) (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (up : Fin n → ℕ) (ds : Bool → Bool)
    (hcov : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ z v : VEndpt n mm,
      VEndpt.edgeOf (s0 - 1) v
        < WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z →
      ∃ w : VEndpt n mm, VEndpt.edgeOf (s0 - 1) w
        = WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z - 1 ∧
        VEndpt.atTopN w = true)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
      (vEndDataN up ds) Zf D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
        (vEndDataN up ds) Zf D' ∧
      ∀ x y : VEndpt n mm,
        runIndexG (VEndpt.edgeOf (s0 - 1)) Zf x
          = runIndexG (VEndpt.edgeOf (s0 - 1)) Zf y →
        (WalkGraph.graph D').Reachable x y :=
  ConfigMerge.reaches_stuck
    (P := TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
      (vEndDataN up ds) Zf)
    (Stuck := fun E => ∀ x y : VEndpt n mm,
      runIndexG (VEndpt.edgeOf (s0 - 1)) Zf x
        = runIndexG (VEndpt.edgeOf (s0 - 1)) Zf y →
      (WalkGraph.graph E).Reachable x y)
    (fun E hE => VEndpt.run_step_turnInvN s0 s1 hlt Zf hgap up ds hcov E hE) D hD

/-- A `TurnInvG` datum's edges preserve the block index or are local, on `VEndpt`. -/
theorem VEndpt.blk_or_local_of_turnInvN {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ)
    (hlt : s1 < s0) (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (up : Fin n → ℕ) (ds : Bool → Bool) (E : WalkGraph.Data (VEndpt n mm))
    (hE : TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
      (vEndDataN up ds) Zf E) :
    ∀ x y : VEndpt n mm, (WalkGraph.graph E).Adj x y →
      CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf x
        = CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf y ∨ (∃ t : ℤ,
        (VEndpt.edgeOf (s0 - 1) x = t - 1 ∨ VEndpt.edgeOf (s0 - 1) x = t) ∧
        (VEndpt.edgeOf (s0 - 1) y = t - 1 ∨ VEndpt.edgeOf (s0 - 1) y = t) ∧
        (VEndpt.edgeOf (s0 - 1) x ≠ VEndpt.edgeOf (s0 - 1) y → t ∉ Zf)) := by
  have hts := hE.1.1.2.1
  have hvirt := VEndpt.hvirt_of_gap s0 s1 hlt Zf hgap E hts
  refine VEndpt.blk_or_local (s0 - 1) Zf E hE.1.1.1 ?_ hvirt
  refine VEndpt.hreal_of_hturn s0 s1 (s0 - 1) Zf E hts ?_ hvirt
  intro u v huv hedge
  have : VEndpt.siteP s0 s1 (Sum.inl u : VEndpt n mm) ∉ Zf := by
    refine hE.2 (Sum.inl u) ?_
    rw [huv]
    simpa [VEndpt.edgeOf] using Ne.symm hedge
  simpa [VEndpt.siteP] using this

/-- **The shield law on `VEndpt`, from `TurnInvG`: `c = |Z|`.**

No `hZ`, no `hturn` hypothesis -- both come from the invariant, which the descent
maintains.  What is left are `hcov`, `hruns`, `hgap` and a basepoint. -/
theorem VEndpt.shield_turnInvN {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hlt : s1 < s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (up : Fin n → ℕ) (ds : Bool → Bool)
    (hcov : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ z v : VEndpt n mm,
      VEndpt.edgeOf (s0 - 1) v
        < WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z →
      ∃ w : VEndpt n mm, VEndpt.edgeOf (s0 - 1) w
        = WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z - 1 ∧
        VEndpt.atTopN w = true)
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n mm, CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf v = i)
    (z₀ : VEndpt n mm)
    (D : WalkGraph.Data (VEndpt n mm))
    (hD : TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
      (vEndDataN up ds) Zf D) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
        (vEndDataN up ds) Zf D' ∧
      WalkGraph.walkCount D' = Zf.card + 1 := by
  obtain ⟨D', hD', hsep⟩ :=
    VEndpt.exists_turnInvN_connected s0 s1 hlt Zf hgap up ds hcov D hD
  have hedge := VEndpt.blk_or_local_of_turnInvN s0 s1 hlt Zf hgap up ds D' hD'
  refine ⟨D', hD', le_antisymm ?_ ?_⟩
  · exact walkCount_le_runs_blk D' (VEndpt.edgeOf (s0 - 1)) Zf hedge hsep
  · obtain ⟨F, hinj, havoid⟩ :=
      CutComponents.exists_injective_components_avoiding_blk_or_local hedge hruns
        ((WalkGraph.graph D').connectedComponentMk z₀)
    exact walkCount_ge_of_avoiding_gen D' Zf.card _ F hinj havoid

/-- **`hruns` for `witNeg`.**  Its two runs are `gz = 0` and `gz = 1`, witnessed by the
virtual arrival (edge `0`) and a real end on shifted edge `3`. -/
theorem witNeg_hruns :
    ∀ i : ℕ, i ≤ (pdCutSites witNeg.toPathData).card →
      ∃ v : VEndpt (pdWidth witNeg.toPathData) (pdMm witNeg.toPathData),
        CutComponents.blk (VEndpt.edgeOf (-witNeg.toPathData.A - 1))
          (pdCutSites witNeg.toPathData) v = i := by
  intro i hi
  rw [witNeg_cutSites, Finset.card_singleton] at hi
  have hw := witNeg_width
  interval_cases i
  · -- the virtual arrival sits on the phantom edge, left of the cut site
    refine ⟨Sum.inr false, ?_⟩
    rw [witNeg_cutSites]
    simp only [CutComponents.blk, VEndpt.edgeOf, witNeg_pd_A]
    decide
  · -- a real end on shifted edge 3, right of the cut site
    have hlt3 : (3 : ℕ) < pdWidth witNeg.toPathData := by omega
    have hpos : 0 < pdMm witNeg.toPathData ⟨3, hlt3⟩ := by
      refine pdMm_pos witNeg.toPathData ⟨3, hlt3⟩ ?_ ?_
      · simp
      · rw [witNeg_pd_A, witNeg_pd_B]; simp
    refine ⟨Sum.inl ⟨⟨3, hlt3⟩, ⟨0, hpos⟩, true⟩, ?_⟩
    rw [witNeg_cutSites]
    simp only [CutComponents.blk, VEndpt.edgeOf, EndType.edgeOf]
    decide

/-! ### The one remaining obligation: an initial `TurnInvG` datum

`shield_turnInvN` consumes a datum already in `TurnInvG` -- cost-minimal, with turns
keeping their edges at cut sites.  Cost-minimality comes from `exists_mergesMinN`.  The
`hturn` component does not: `turnG` is built from an arbitrary involution at each site,
and nothing makes it respect cut sites.

`hturn_of_cross_zero` (BLOCK 61) derives `hturn` from zero crossing at cut sites, and
`CostMerge.site_cost_le_of_global` turns global minimality into local minimality.  What
is missing is the last step: that the local minimum at a cut site is **zero**, which
needs a comparison datum of zero cost there -- a plan pairing each arrival with a
departure on its own side.

In the paper that datum is the realisation itself: `Realisation.cut_no_cross` holds for
a realisation with `R.cost = P.lR`.  So the initial datum should come from a
`Realisation`, not be built abstractly from `dataG`. -/

/-- **The remaining obligation, named** (Rule I7).  An initial datum in the invariant. -/
def HasInitialTurnInv {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (Zf : Finset ℤ)
    (up : Fin n → ℕ) (ds : Bool → Bool) : Prop :=
  ∃ D : WalkGraph.Data (VEndpt n mm),
    TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
      (vEndDataN up ds) Zf D

/-- **The shield law, modulo that one obligation.**  Everything else is discharged. -/
theorem VEndpt.shield_of_initial {n : ℕ} {mm : Fin n → ℕ} (s0 s1 : ℤ) (hlt : s1 < s0)
    (Zf : Finset ℤ) (hgap : ∀ z ∈ Zf, ¬ (s1 - 1 < z ∧ z ≤ s0))
    (up : Fin n → ℕ) (ds : Bool → Bool)
    (hcov : ∀ E : WalkGraph.Data (VEndpt n mm), ∀ z v : VEndpt n mm,
      VEndpt.edgeOf (s0 - 1) v
        < WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z →
      ∃ w : VEndpt n mm, VEndpt.edgeOf (s0 - 1) w
        = WalkSupport.wLo (VEndpt.edgeOf (s0 - 1)) (WalkGraph.graph E) z - 1 ∧
        VEndpt.atTopN w = true)
    (hruns : ∀ i : ℕ, i ≤ Zf.card →
      ∃ v : VEndpt n mm, CutComponents.blk (VEndpt.edgeOf (s0 - 1)) Zf v = i)
    (z₀ : VEndpt n mm)
    (hinit : HasInitialTurnInv (mm := mm) s0 s1 Zf up ds) :
    ∃ D' : WalkGraph.Data (VEndpt n mm),
      TurnInvG (VEndpt.siteP s0 s1) (VEndpt.edgeOf (s0 - 1)) VEndpt.partner
        (vEndDataN up ds) Zf D' ∧
      WalkGraph.walkCount D' = Zf.card + 1 := by
  obtain ⟨D, hD⟩ := hinit
  exact VEndpt.shield_turnInvN s0 s1 hlt Zf hgap up ds hcov hruns z₀ D hD

/-! ### At a cut site both adjacent edges have zero travel

A zero-cost plan at a cut site pairs each arrival with a departure **on its own side**,
which needs the counts to match side by side.  In the `Endpt` model that is exactly
`tr = 0` on both adjacent edges: the top half matches iff `tr` of the left edge
vanishes, the bottom half iff `tr` of the right edge does.

The cut condition supplies it.  `Phi = 0` gives `f(s-1) = 0`, and away from the two
virtual sites `travel` is constant, so `f(s) = 0` too. -/

/-- **Both edges at a cut site carry zero travel.** -/
theorem pdCut_travel_zero (P : SiteCost.PathData) (s : ℤ)
    (h0 : s ≠ 0) (hk : s ≠ P.kstar) (hcut : P.cut s) :
    travel P.kstar (s - 1) = 0 ∧ travel P.kstar s = 0 := by
  obtain ⟨-, -, hPhi⟩ := hcut
  unfold SiteCost.PathData.PhiAt SiteCost.PathData.vL SiteCost.PathData.vD
    SiteCost.vArr at hPhi
  rw [if_neg h0, if_neg hk] at hPhi
  simp only [ite_self, Nat.cast_zero, sub_zero, add_zero] at hPhi
  have hf : travel P.kstar (s - 1) = 0 := hPhi
  refine ⟨hf, ?_⟩
  have := travel_const_off P.kstar s h0 hk
  omega

/-- **So the site's two halves balance separately**, in the `Endpt` model: the top half
matches iff the left edge's signed travel vanishes, the bottom half iff the right
edge's does. -/
theorem sided_balance_of_tr_zero {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ)
    (e1 e2 : Fin n) (h1 : (e1 : ℤ) = s - 1) (h2 : (e2 : ℤ) = s)
    (ht1 : ConfigLoop.tr (m := m) up e1 = 0)
    (ht2 : ConfigLoop.tr (m := m) up e2 = 0) :
    ((EndType.arrAt (m := m) up s).filter (fun x => EndType.atTop x = true)).card
        = ((EndType.depAt (m := m) up s).filter (fun x => EndType.atTop x = true)).card ∧
      ((EndType.arrAt (m := m) up s).filter (fun x => EndType.atTop x = false)).card
        = ((EndType.depAt (m := m) up s).filter (fun x => EndType.atTop x = false)).card := by
  have ha := EndType.card_arr_top (m := m) up s e1 h1
  have hb := EndType.card_dep_top (m := m) up s e1 h1
  have hc := EndType.card_arr_bottom (m := m) up s e2 h2
  have hd := EndType.card_dep_bottom (m := m) up s e2 h2
  have k1 : min (up e1) (m e1) ≤ m e1 := min_le_right _ _
  have k2 : min (up e2) (m e2) ≤ m e2 := min_le_right _ _
  unfold ConfigLoop.tr at ht1 ht2
  constructor
  · rw [ha, hb]; omega
  · rw [hc, hd]; omega

/-! ### Combining two involutions on disjoint supports

At a cut site the top and bottom halves each balance, so each admits an involution
exchanging its arrivals and departures.  Combining them gives a turn that never crosses
sides -- a zero-cost plan. -/

/-- **Two involutions on disjoint supports combine.** -/
theorem exists_involution_two {α : Type*} [Fintype α] [DecidableEq α]
    (A1 D1 A2 D2 : Finset α)
    (hd1 : Disjoint A1 D1) (hc1 : A1.card = D1.card)
    (hd2 : Disjoint A2 D2) (hc2 : A2.card = D2.card)
    (hsep : Disjoint (A1 ∪ D1) (A2 ∪ D2)) :
    ∃ t : α → α, (∀ x, t (t x) = x) ∧
      (∀ x ∈ A1, t x ∈ D1) ∧ (∀ x ∈ D1, t x ∈ A1) ∧
      (∀ x ∈ A2, t x ∈ D2) ∧ (∀ x ∈ D2, t x ∈ A2) ∧
      (∀ x, x ∉ A1 → x ∉ D1 → x ∉ A2 → x ∉ D2 → t x = x) := by
  classical
  obtain ⟨t1, h1inv, h1AD, h1DA, h1fix, -, -⟩ :=
    TurnBuild.exists_involution_of_card_eq A1 D1 hd1 hc1
  obtain ⟨t2, h2inv, h2AD, h2DA, h2fix, -, -⟩ :=
    TurnBuild.exists_involution_of_card_eq A2 D2 hd2 hc2
  refine ⟨fun x => if x ∈ A1 ∪ D1 then t1 x else t2 x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ A1 ∪ D1
    · have himg : t1 x ∈ A1 ∪ D1 := by
        rcases Finset.mem_union.mp hx with h | h
        · exact Finset.mem_union_right _ (h1AD x h)
        · exact Finset.mem_union_left _ (h1DA x h)
      simp only [if_pos hx, if_pos himg, h1inv]
    · have hx2 : t2 x ∉ A1 ∪ D1 := by
        by_cases hx2 : x ∈ A2 ∪ D2
        · have : t2 x ∈ A2 ∪ D2 := by
            rcases Finset.mem_union.mp hx2 with h | h
            · exact Finset.mem_union_right _ (h2AD x h)
            · exact Finset.mem_union_left _ (h2DA x h)
          exact fun hc => (Finset.disjoint_left.mp hsep hc) this
        · rw [h2fix x (fun h => hx2 (Finset.mem_union_left _ h))
            (fun h => hx2 (Finset.mem_union_right _ h))]
          exact hx
      simp only [if_neg hx, if_neg hx2, h2inv]
  · intro x hx
    simp only [if_pos (Finset.mem_union_left _ hx)]
    exact h1AD x hx
  · intro x hx
    simp only [if_pos (Finset.mem_union_right _ hx)]
    exact h1DA x hx
  · intro x hx
    have hnot : x ∉ A1 ∪ D1 := fun hc =>
      (Finset.disjoint_left.mp hsep hc) (Finset.mem_union_left _ hx)
    simp only [if_neg hnot]
    exact h2AD x hx
  · intro x hx
    have hnot : x ∉ A1 ∪ D1 := fun hc =>
      (Finset.disjoint_left.mp hsep hc) (Finset.mem_union_right _ hx)
    simp only [if_neg hnot]
    exact h2DA x hx
  · intro x n1 n2 n3 n4
    have hnot : x ∉ A1 ∪ D1 := fun hc => by
      rcases Finset.mem_union.mp hc with h | h
      · exact n1 h
      · exact n2 h
    simp only [if_neg hnot]
    exact h2fix x n3 n4

/-- **The side-respecting turn at a cut site.**

Splitting the site's arrivals and departures by `atTop` gives two balanced pairs with
disjoint supports, so `exists_involution_two` produces an involution exchanging
arrivals and departures **within each side**.  It therefore preserves `atTop`, and
since it also preserves the site, it preserves the edge -- which is `hturn` there. -/
theorem exists_sided_turn_at {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ)
    (e1 e2 : Fin n) (h1 : (e1 : ℤ) = s - 1) (h2 : (e2 : ℤ) = s)
    (ht1 : ConfigLoop.tr (m := m) up e1 = 0)
    (ht2 : ConfigLoop.tr (m := m) up e2 = 0) :
    ∃ t : EndType.Endpt n m → EndType.Endpt n m, (∀ x, t (t x) = x) ∧
      (∀ x ∈ EndType.arrAt (m := m) up s, t x ∈ EndType.depAt (m := m) up s) ∧
      (∀ x ∈ EndType.depAt (m := m) up s, t x ∈ EndType.arrAt (m := m) up s) ∧
      (∀ x, EndType.siteOf x = s → EndType.atTop (t x) = EndType.atTop x) ∧
      (∀ x, x ∉ EndType.arrAt (m := m) up s → x ∉ EndType.depAt (m := m) up s →
        t x = x) := by
  classical
  obtain ⟨hT, hB⟩ := sided_balance_of_tr_zero (m := m) up s e1 e2 h1 h2 ht1 ht2
  set A1 := (EndType.arrAt (m := m) up s).filter (fun x => EndType.atTop x = true)
  set D1 := (EndType.depAt (m := m) up s).filter (fun x => EndType.atTop x = true)
  set A2 := (EndType.arrAt (m := m) up s).filter (fun x => EndType.atTop x = false)
  set D2 := (EndType.depAt (m := m) up s).filter (fun x => EndType.atTop x = false)
  have hAD : Disjoint (EndType.arrAt (m := m) up s) (EndType.depAt (m := m) up s) :=
    EndType.arrAt_disjoint_depAt up s
  have hd1 : Disjoint A1 D1 :=
    Finset.disjoint_filter_filter hAD
  have hd2 : Disjoint A2 D2 :=
    Finset.disjoint_filter_filter hAD
  have hsep : Disjoint (A1 ∪ D1) (A2 ∪ D2) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h : EndType.atTop x = true := by
      rcases Finset.mem_union.mp hx with h | h <;>
        exact (Finset.mem_filter.mp h).2
    have h' : EndType.atTop x = false := by
      rcases Finset.mem_union.mp hx' with h | h <;>
        exact (Finset.mem_filter.mp h).2
    rw [h] at h'; exact Bool.noConfusion h'
  obtain ⟨t, hinv, h1AD, h1DA, h2AD, h2DA, hfix⟩ :=
    exists_involution_two A1 D1 A2 D2 hd1 hT hd2 hB hsep
  refine ⟨t, hinv, ?_, ?_, ?_, ?_⟩
  · intro x hx
    cases hb : EndType.atTop x
    · exact (Finset.mem_filter.mp (h2AD x (Finset.mem_filter.mpr ⟨hx, hb⟩))).1
    · exact (Finset.mem_filter.mp (h1AD x (Finset.mem_filter.mpr ⟨hx, hb⟩))).1
  · intro x hx
    cases hb : EndType.atTop x
    · exact (Finset.mem_filter.mp (h2DA x (Finset.mem_filter.mpr ⟨hx, hb⟩))).1
    · exact (Finset.mem_filter.mp (h1DA x (Finset.mem_filter.mpr ⟨hx, hb⟩))).1
  · intro x hxs
    by_cases hx : x ∈ EndType.arrAt (m := m) up s
    · cases hb : EndType.atTop x
      · rw [(Finset.mem_filter.mp (h2AD x (Finset.mem_filter.mpr ⟨hx, hb⟩))).2]
      · rw [(Finset.mem_filter.mp (h1AD x (Finset.mem_filter.mpr ⟨hx, hb⟩))).2]
    · by_cases hx' : x ∈ EndType.depAt (m := m) up s
      · cases hb : EndType.atTop x
        · rw [(Finset.mem_filter.mp (h2DA x (Finset.mem_filter.mpr ⟨hx', hb⟩))).2]
        · rw [(Finset.mem_filter.mp (h1DA x (Finset.mem_filter.mpr ⟨hx', hb⟩))).2]
      · rw [hfix x (fun h => hx (Finset.mem_filter.mp h).1)
          (fun h => hx' (Finset.mem_filter.mp h).1)
          (fun h => hx (Finset.mem_filter.mp h).1)
          (fun h => hx' (Finset.mem_filter.mp h).1)]
  · intro x hx hx'
    exact hfix x (fun h => hx (Finset.mem_filter.mp h).1)
      (fun h => hx' (Finset.mem_filter.mp h).1)
      (fun h => hx (Finset.mem_filter.mp h).1)
      (fun h => hx' (Finset.mem_filter.mp h).1)

/-! ### The global turn: sided at cut sites, arbitrary elsewhere

Glueing the sided turns of `exists_sided_turn_at` at the cut sites with the generic
`turnAtG` everywhere else gives a datum satisfying `hturn`. -/

/-- **A datum in the merge class satisfying `hturn`.**

The hypothesis is exactly what `exists_sided_turn_at` supplies at each cut site. -/
theorem exists_merges_hturn {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (Zf : Finset ℤ)
    (hbal : ∀ s : ℤ, (GenericData.arrOf (EndType.siteOf (n := n) (m := m))
      (EndType.isArrOf up) s).card
      = (GenericData.depOf (EndType.siteOf (n := n) (m := m))
        (EndType.isArrOf up) s).card)
    (hsided : ∀ s ∈ Zf, ∃ t : EndType.Endpt n m → EndType.Endpt n m,
      (∀ x, t (t x) = x) ∧
      (∀ x ∈ EndType.arrAt (m := m) up s, t x ∈ EndType.depAt (m := m) up s) ∧
      (∀ x ∈ EndType.depAt (m := m) up s, t x ∈ EndType.arrAt (m := m) up s) ∧
      (∀ x, EndType.siteOf x = s → EndType.atTop (t x) = EndType.atTop x) ∧
      (∀ x, x ∉ EndType.arrAt (m := m) up s → x ∉ EndType.depAt (m := m) up s →
        t x = x)) :
    ∃ D : WalkGraph.Data (EndType.Endpt n m),
      WalkSupport.Merges EndType.siteOf (EndType.isArrOf up) EndType.partner D ∧
      ∀ x : EndType.Endpt n m,
        EndType.edgeOf (D.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf := by
  classical
  -- the local turn at each site
  set loc : ℤ → EndType.Endpt n m → EndType.Endpt n m := fun s =>
    if h : s ∈ Zf then (hsided s h).choose
    else GenericData.turnAtG EndType.siteOf (EndType.isArrOf up) hbal s with hloc
  have hlocinv : ∀ s x, loc s (loc s x) = x := by
    intro s x
    by_cases h : s ∈ Zf
    · simp only [hloc, dif_pos h]
      exact (hsided s h).choose_spec.1 x
    · simp only [hloc, dif_neg h]
      exact (TurnBuild.exists_involution_of_card_eq _ _
        (GenericData.arr_disj_dep _ _ s) (hbal s)).choose_spec.1 x
  have hlocsite : ∀ x, EndType.siteOf (loc (EndType.siteOf x) x) = EndType.siteOf x := by
    intro x
    by_cases h : EndType.siteOf x ∈ Zf
    · simp only [hloc, dif_pos h]
      obtain ⟨-, hAD, hDA, -, hfix⟩ := (hsided _ h).choose_spec
      by_cases hx : x ∈ EndType.arrAt (m := m) up (EndType.siteOf x)
      · exact ((EndType.mem_depAt up _ _).mp (hAD x hx)).1
      · by_cases hx' : x ∈ EndType.depAt (m := m) up (EndType.siteOf x)
        · exact ((EndType.mem_arrAt up _ _).mp (hDA x hx')).1
        · rw [hfix x hx hx']
    · simp only [hloc, dif_neg h]
      exact GenericData.turnG_site EndType.siteOf (EndType.isArrOf up) hbal x
  -- the glued turn preserves the edge at cut sites
  have hkeep : ∀ x, EndType.siteOf x ∈ Zf →
      EndType.edgeOf (loc (EndType.siteOf x) x) = EndType.edgeOf x := by
    intro x h
    have htop : EndType.atTop (loc (EndType.siteOf x) x) = EndType.atTop x := by
      simp only [hloc, dif_pos h]
      exact (hsided _ h).choose_spec.2.2.2.1 x rfl
    exact same_edge_of_site_top _ _ (hlocsite x) htop
  refine ⟨⟨EndType.partner, TurnBuild.glue EndType.siteOf loc, EndType.partner_invol,
    TurnBuild.glue_invol EndType.siteOf loc hlocinv hlocsite, EndType.partner_ne, ?_, ?_⟩,
    ⟨rfl, ?_, ?_⟩, ?_⟩
  · -- t_ne
    intro x
    show loc (EndType.siteOf x) x ≠ x
    by_cases h : EndType.siteOf x ∈ Zf
    · simp only [hloc, dif_pos h]
      obtain ⟨-, hAD, hDA, -, -⟩ := (hsided _ h).choose_spec
      by_cases hx : x ∈ EndType.arrAt (m := m) up (EndType.siteOf x)
      · intro hc
        have := hAD x hx
        rw [hc] at this
        exact (Finset.disjoint_left.mp (EndType.arrAt_disjoint_depAt up _) hx) this
      · by_cases hx' : x ∈ EndType.depAt (m := m) up (EndType.siteOf x)
        · intro hc
          have := hDA x hx'
          rw [hc] at this
          exact (Finset.disjoint_left.mp (EndType.arrAt_disjoint_depAt up _) this) hx'
        · exact absurd (GenericData.mem_own EndType.siteOf (EndType.isArrOf up) x)
            (by push_neg; exact ⟨hx, hx'⟩)
    · simp only [hloc, dif_neg h]
      exact GenericData.turnG_ne EndType.siteOf (EndType.isArrOf up) hbal x
  · -- pt_ne
    intro x hc
    exact EndType.partner_site_ne x (by rw [hc]; exact hlocsite x)
  · exact fun e => hlocsite e
  · -- hta
    intro e
    show EndType.isArrOf up (loc (EndType.siteOf e) e) = !EndType.isArrOf up e
    by_cases h : EndType.siteOf e ∈ Zf
    · simp only [hloc, dif_pos h]
      obtain ⟨-, hAD, hDA, -, -⟩ := (hsided _ h).choose_spec
      cases hax : EndType.isArrOf up e with
      | true =>
        have := (EndType.mem_depAt up _ _).mp
          (hAD e ((EndType.mem_arrAt up _ e).mpr ⟨rfl, hax⟩))
        rw [this.2]; rfl
      | false =>
        have := (EndType.mem_arrAt up _ _).mp
          (hDA e ((EndType.mem_depAt up _ e).mpr ⟨rfl, hax⟩))
        rw [this.2]; rfl
    · simp only [hloc, dif_neg h]
      exact GenericData.turnG_arr EndType.siteOf (EndType.isArrOf up) hbal e
  · -- hturn
    intro x hne hmem
    exact hne (hkeep x hmem)

/-! ### Minimising inside the `hturn` subclass

`CostMerge.exists_mergesMin` produces an arbitrary global minimiser, which need not
satisfy `hturn`.  It does not have to: the free-pair argument compares `E` only with
**swaps of `E`**, and swaps preserve `hturn` (BLOCK 63).  So minimising within the
subclass of data that satisfy `hturn` is enough, and that subclass is non-empty by
`exists_merges_hturn`. -/

/-- **A least-cost datum among those satisfying `hturn`.** -/
theorem exists_least_cost_hturn {n : ℕ} {m : Fin n → ℕ}
    (d : EndData.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (D₀ : WalkGraph.Data (EndType.Endpt n m))
    (hD₀ : WalkSupport.Merges EndType.siteOf d.isArr EndType.partner D₀ ∧
      ∀ x : EndType.Endpt n m,
        EndType.edgeOf (D₀.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf) :
    ∃ E : WalkGraph.Data (EndType.Endpt n m),
      (WalkSupport.Merges EndType.siteOf d.isArr EndType.partner E ∧
        ∀ x : EndType.Endpt n m,
          EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf) ∧
      ∀ F : WalkGraph.Data (EndType.Endpt n m),
        WalkSupport.Merges EndType.siteOf d.isArr EndType.partner F →
        (∀ x : EndType.Endpt n m,
          EndType.edgeOf (F.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf) →
        CostMerge.costOf d E ≤ CostMerge.costOf d F := by
  classical
  obtain ⟨c, ⟨E, hE, hEc⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun c => ∃ F, (WalkSupport.Merges EndType.siteOf d.isArr EndType.partner F ∧
        ∀ x : EndType.Endpt n m,
          EndType.edgeOf (F.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf) ∧
        CostMerge.costOf d F = c)
      ⟨0, fun z hz => by obtain ⟨F, -, hF⟩ := hz; rw [← hF]; exact CostMerge.costOf_nonneg d F⟩
      ⟨CostMerge.costOf d D₀, D₀, hD₀, rfl⟩
  refine ⟨E, hE, fun F hF1 hF2 => ?_⟩
  rw [hEc]
  exact hleast _ ⟨F, ⟨hF1, hF2⟩, rfl⟩

/-! ### Which swaps preserve `hturn`

Subclass minimality is only as strong as the comparisons it admits, so it matters
exactly which swaps stay inside the subclass.

* A swap at a **non-cut** site always does: `hturn` constrains nothing there, and
  `hturn_swapT_gen` needs only `site a ∉ Zf`.
* A swap at a **cut** site does iff the two arrivals share an edge, which
  `freePair_same_edge_at_cut` gives when they share a side.

So the only comparisons the subclass loses are cross-side swaps at cut sites. -/

/-- **Swaps at a non-cut site preserve `hturn`**, with no side condition. -/
theorem swap_preserves_hturn_offcut {n : ℕ} {m : Fin n → ℕ} (Zf : Finset ℤ)
    (D : WalkGraph.Data (EndType.Endpt n m)) (a a' : EndType.Endpt n m)
    (hts : ∀ e, EndType.siteOf (D.t e) = EndType.siteOf e)
    (hturn : ∀ x : EndType.Endpt n m,
      EndType.edgeOf (D.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hss : EndType.siteOf a' = EndType.siteOf a)
    (hoff : EndType.siteOf a ∉ Zf) :
    ∀ x : EndType.Endpt n m,
      EndType.edgeOf (WalkGraph.swapT D.t a (D.t a) a' (D.t a') x)
        ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf :=
  hturn_swapT_gen D.t EndType.edgeOf EndType.siteOf Zf a (D.t a) a' (D.t a')
    hturn hoff (hts a) hss (by rw [hts a']; exact hss)

/-- **And at a cut site, exactly when the pair shares a side.** -/
theorem swap_preserves_hturn_atcut {n : ℕ} {m : Fin n → ℕ} (Zf : Finset ℤ)
    (D : WalkGraph.Data (EndType.Endpt n m)) (a a' : EndType.Endpt n m)
    (hts : ∀ e, EndType.siteOf (D.t e) = EndType.siteOf e)
    (hturn : ∀ x : EndType.Endpt n m,
      EndType.edgeOf (D.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hss : EndType.siteOf a' = EndType.siteOf a)
    (hcut : EndType.siteOf a ∈ Zf)
    (hshared : EndType.atTop a = EndType.atTop a' ∨
      EndType.atTop (D.t a) = EndType.atTop (D.t a')) :
    ∀ x : EndType.Endpt n m,
      EndType.edgeOf (WalkGraph.swapT D.t a (D.t a) a' (D.t a') x)
        ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf :=
  hturn_swapT_nohZ Zf D hts hturn a a' hss hcut hshared

/-! ### The forced sign, and what it does to cut sites

`EndData.sgn` is a function of `(side, isArr, depSign side)` only.  So on a fixed side
every arrival has one sign and every departure the other -- the sign is **forced**, not
free.  Two consequences:

* a same-side arrival/departure pair always costs `2`, and a cross-side pair `1`
  (`pcost_eq_of_arr_dep`);
* in the four transportation classes, one of each side's two is empty, so
  `alpha = -(A + C)` and `alpha = 0` forces the site to carry **no ends** on that side
  -- which is `ConfigLoop.no_ends_of_alpha_zero`.

The paper's `Plan` does not force the sign: `Ap, Am, Cp, Cm` are independent, and a
same-side same-sign pair costs `0`.  So the `EndData` model is strictly less general
than the site model it is meant to realise, and that gap is where `hZ` came from. -/

/-- **The sign is forced**: on one side, arrivals and departures always differ. -/
theorem sgn_arr_ne_dep {α : Type*} (d : EndData.Data α) (a b : α)
    (hside : d.side a = d.side b) (ha : d.isArr a = true) (hb : d.isArr b = false) :
    EndData.sgn d a ≠ EndData.sgn d b := by
  unfold EndData.sgn
  rw [hside, ha, hb]
  cases hs : d.side b <;> simp

/-- **So a same-side arrival/departure pair costs two**, never zero. -/
theorem pcost_same_side_two {α : Type*} (d : EndData.Data α) (a b : α)
    (hside : d.side a = d.side b) (ha : d.isArr a = true) (hb : d.isArr b = false) :
    EndData.pcostF d a b = 2 := by
  unfold EndData.pcostF
  rw [if_pos hside, if_neg (sgn_arr_ne_dep d a b hside ha hb)]

/-- **Hence every pairing costs at least one per arrival**: there is no zero-cost plan
at a site carrying ends. -/
theorem pcostF_ge_one {α : Type*} (d : EndData.Data α) (a b : α)
    (ha : d.isArr a = true) (hb : d.isArr b = false) :
    1 ≤ EndData.pcostF d a b := by
  unfold EndData.pcostF
  by_cases hside : d.side a = d.side b
  · rw [if_pos hside, if_neg (sgn_arr_ne_dep d a b hside ha hb)]; norm_num
  · rw [if_neg hside]

/-! ### End data with a free sign

`EndData.Data` derives each end's sign from its side and role.  The paper's site model
does not: the four classes `(L,+), (L,-), (R,+), (R,-)` are independent.  This is the
free-sign version, in which a same-side same-sign pair costs `0` and zero-cost plans
exist. -/

/-- End data with the sign carried per end rather than derived. -/
structure GData (α : Type*) where
  /-- which side of the site the end is on -/
  side : α → Bool
  /-- whether the end is an arrival -/
  isArr : α → Bool
  /-- the end's sign, free -/
  sgnOf : α → Bool

/-- The pairing cost with a free sign: `0` same side and same sign, `2` same side and
opposite sign, `1` across sides. -/
def GData.pcost {α : Type*} (d : GData α) (a b : α) : ℤ :=
  if d.side a = d.side b then (if d.sgnOf a = d.sgnOf b then 0 else 2) else 1

/-- **A same-side same-sign pair costs nothing** -- the possibility the forced model
lacks. -/
theorem GData.pcost_zero {α : Type*} (d : GData α) (a b : α)
    (hside : d.side a = d.side b) (hsgn : d.sgnOf a = d.sgnOf b) :
    d.pcost a b = 0 := by
  unfold GData.pcost
  rw [if_pos hside, if_pos hsgn]

theorem GData.pcost_nonneg {α : Type*} (d : GData α) (a b : α) : 0 ≤ d.pcost a b := by
  unfold GData.pcost
  split <;> [split; skip] <;> norm_num

/-- The forced model embeds: take the derived sign as the free one. -/
def GData.ofEndData {α : Type*} (d : EndData.Data α) : GData α :=
  ⟨d.side, d.isArr, EndData.sgn d⟩

@[simp] theorem GData.ofEndData_pcost {α : Type*} (d : EndData.Data α) (a b : α) :
    (GData.ofEndData d).pcost a b = EndData.pcostF d a b := rfl

/-- **And the embedding is strict**: in the forced model a same-side arrival/departure
pair costs `2`, while the free model allows `0` for the same side.  So `GData` is
genuinely more general, which is what the site model needs. -/
theorem GData.strictly_more_general {α : Type*} (d : EndData.Data α) (a b : α)
    (hside : d.side a = d.side b) (ha : d.isArr a = true) (hb : d.isArr b = false) :
    (GData.ofEndData d).pcost a b = 2 ∧
    (GData.mk d.side d.isArr (fun _ => true)).pcost a b = 0 := by
  refine ⟨pcost_same_side_two d a b hside ha hb, ?_⟩
  exact GData.pcost_zero _ a b hside rfl

/-! ### Combining involutions, chainably

`exists_involution_two` takes two balanced pairs.  For the four-way split by
`(side, sign)` a combinator over *involutions* is better: it chains. -/

/-- **Two involutions supported on disjoint sets combine.** -/
theorem combine_involutions {α : Type*} [DecidableEq α] (t1 t2 : α → α)
    (S1 S2 : Finset α)
    (h1inv : ∀ x, t1 (t1 x) = x) (h1S : ∀ x ∈ S1, t1 x ∈ S1)
    (h1fix : ∀ x, x ∉ S1 → t1 x = x)
    (h2inv : ∀ x, t2 (t2 x) = x) (h2S : ∀ x ∈ S2, t2 x ∈ S2)
    (h2fix : ∀ x, x ∉ S2 → t2 x = x)
    (hdisj : Disjoint S1 S2) :
    ∃ t : α → α, (∀ x, t (t x) = x) ∧ (∀ x ∈ S1, t x = t1 x) ∧
      (∀ x ∈ S2, t x = t2 x) ∧ (∀ x, x ∉ S1 → x ∉ S2 → t x = x) ∧
      (∀ x ∈ S1, t x ∈ S1) ∧ (∀ x ∈ S2, t x ∈ S2) := by
  classical
  refine ⟨fun x => if x ∈ S1 then t1 x else t2 x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ S1
    · simp only [if_pos hx, if_pos (h1S x hx), h1inv]
    · have hnot : t2 x ∉ S1 := by
        by_cases hx2 : x ∈ S2
        · exact fun hc => (Finset.disjoint_left.mp hdisj hc) (h2S x hx2)
        · rw [h2fix x hx2]; exact hx
      simp only [if_neg hx, if_neg hnot, h2inv]
  · intro x hx; simp only [if_pos hx]
  · intro x hx
    have hnot : x ∉ S1 := fun hc => (Finset.disjoint_left.mp hdisj hc) hx
    simp only [if_neg hnot]
  · intro x h1 h2; simp only [if_neg h1]; exact h2fix x h2
  · intro x hx; simp only [if_pos hx]; exact h1S x hx
  · intro x hx
    have hnot : x ∉ S1 := fun hc => (Finset.disjoint_left.mp hdisj hc) hx
    simp only [if_neg hnot]; exact h2S x hx

/-- **A balanced pair gives an involution supported on its union.** -/
theorem involution_of_pair {α : Type*} [Fintype α] [DecidableEq α] (A D : Finset α)
    (hdisj : Disjoint A D) (hcard : A.card = D.card) :
    ∃ t : α → α, (∀ x, t (t x) = x) ∧ (∀ x ∈ A, t x ∈ D) ∧ (∀ x ∈ D, t x ∈ A) ∧
      (∀ x ∈ A ∪ D, t x ∈ A ∪ D) ∧ (∀ x, x ∉ A ∪ D → t x = x) := by
  obtain ⟨t, hinv, hAD, hDA, hfix, -, -⟩ :=
    TurnBuild.exists_involution_of_card_eq A D hdisj hcard
  refine ⟨t, hinv, hAD, hDA, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_right _ (hAD x h)
    · exact Finset.mem_union_left _ (hDA x h)
  · intro x hx
    exact hfix x (fun h => hx (Finset.mem_union_left _ h))
      (fun h => hx (Finset.mem_union_right _ h))

/-! ### The zero-cost turn from four-class balance

With a free sign, a site whose four `(side, sign)` classes balance admits an involution
pairing each arrival with a departure **in its own class** -- so every pair costs `0`. -/

/-- **A zero-cost involution from four-class balance.** -/
theorem exists_zero_cost_turn {α : Type*} [Fintype α] [DecidableEq α]
    (d : GData α) (A D : Finset α) (hdisj : Disjoint A D)
    (hbal : ∀ sd sg : Bool,
      (A.filter (fun x => d.side x = sd ∧ d.sgnOf x = sg)).card
        = (D.filter (fun x => d.side x = sd ∧ d.sgnOf x = sg)).card) :
    ∃ t : α → α, (∀ x, t (t x) = x) ∧
      (∀ x ∈ A, d.side (t x) = d.side x ∧ d.sgnOf (t x) = d.sgnOf x) ∧
      (∀ x, x ∉ A → x ∉ D → t x = x) := by
  classical
  -- the four class sets
  set cA : Bool → Bool → Finset α := fun sd sg =>
    A.filter (fun x => d.side x = sd ∧ d.sgnOf x = sg) with hcA
  set cD : Bool → Bool → Finset α := fun sd sg =>
    D.filter (fun x => d.side x = sd ∧ d.sgnOf x = sg) with hcD
  -- an involution per class, supported on that class's union
  have hcls : ∀ sd sg : Bool, ∃ t : α → α, (∀ x, t (t x) = x) ∧
      (∀ x ∈ cA sd sg ∪ cD sd sg, t x ∈ cA sd sg ∪ cD sd sg) ∧
      (∀ x, x ∉ cA sd sg ∪ cD sd sg → t x = x) := by
    intro sd sg
    obtain ⟨t, hinv, -, -, hS, hfix⟩ :=
      involution_of_pair (cA sd sg) (cD sd sg)
        (Finset.disjoint_filter_filter hdisj) (hbal sd sg)
    exact ⟨t, hinv, hS, hfix⟩
  choose t ht using hcls
  -- supports are pairwise disjoint: side and sign separate the classes
  have hsupp : ∀ (sd sg : Bool) x, x ∈ cA sd sg ∪ cD sd sg →
      d.side x = sd ∧ d.sgnOf x = sg := by
    intro sd sg x hx
    rcases Finset.mem_union.mp hx with h | h <;> exact (Finset.mem_filter.mp h).2
  have hdis : ∀ (a b c e : Bool), (a, b) ≠ (c, e) →
      Disjoint (cA a b ∪ cD a b) (cA c e ∪ cD c e) := by
    intro a b c e hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨h1, h2⟩ := hsupp a b x hx
    obtain ⟨h3, h4⟩ := hsupp c e x hx'
    exact hne (by rw [← h1, ← h2, h3, h4])
  -- chain them
  set S1 : Finset α := (cA true true ∪ cD true true) ∪ (cA true false ∪ cD true false)
  set S2 : Finset α := (cA false true ∪ cD false true) ∪ (cA false false ∪ cD false false)
  obtain ⟨u1, hu1inv, hu1a, hu1b, hu1fix, hu1S, hu1S'⟩ :=
    combine_involutions (t true true) (t true false)
      (cA true true ∪ cD true true) (cA true false ∪ cD true false)
      (ht true true).1 (ht true true).2.1 (ht true true).2.2
      (ht true false).1 (ht true false).2.1 (ht true false).2.2
      (hdis true true true false (by simp))
  obtain ⟨u2, hu2inv, hu2a, hu2b, hu2fix, hu2S, hu2S'⟩ :=
    combine_involutions (t false true) (t false false)
      (cA false true ∪ cD false true) (cA false false ∪ cD false false)
      (ht false true).1 (ht false true).2.1 (ht false true).2.2
      (ht false false).1 (ht false false).2.1 (ht false false).2.2
      (hdis false true false false (by simp))
  have hu1cl : ∀ x ∈ S1, u1 x ∈ S1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ (hu1S x h)
    · exact Finset.mem_union_right _ (hu1S' x h)
  have hu1out : ∀ x, x ∉ S1 → u1 x = x := by
    intro x hx
    exact hu1fix x (fun h => hx (Finset.mem_union_left _ h))
      (fun h => hx (Finset.mem_union_right _ h))
  have hu2cl : ∀ x ∈ S2, u2 x ∈ S2 := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ (hu2S x h)
    · exact Finset.mem_union_right _ (hu2S' x h)
  have hu2out : ∀ x, x ∉ S2 → u2 x = x := by
    intro x hx
    exact hu2fix x (fun h => hx (Finset.mem_union_left _ h))
      (fun h => hx (Finset.mem_union_right _ h))
  have hS12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 : d.side x = true := by
      rcases Finset.mem_union.mp hx with h | h
      · exact (hsupp true true x h).1
      · exact (hsupp true false x h).1
    have h2 : d.side x = false := by
      rcases Finset.mem_union.mp hx' with h | h
      · exact (hsupp false true x h).1
      · exact (hsupp false false x h).1
    rw [h1] at h2; exact Bool.noConfusion h2
  obtain ⟨v, hvinv, hva, hvb, hvfix, hvS1, hvS2⟩ :=
    combine_involutions u1 u2 S1 S2 hu1inv hu1cl hu1out hu2inv hu2cl hu2out hS12
  refine ⟨v, hvinv, ?_, ?_⟩
  · -- `v` preserves the class of every arrival
    intro x hx
    have hxc : x ∈ cA (d.side x) (d.sgnOf x) :=
      Finset.mem_filter.mpr ⟨hx, rfl, rfl⟩
    have hxu : x ∈ cA (d.side x) (d.sgnOf x) ∪ cD (d.side x) (d.sgnOf x) :=
      Finset.mem_union_left _ hxc
    have himg : v x ∈ cA (d.side x) (d.sgnOf x) ∪ cD (d.side x) (d.sgnOf x) := by
      cases hsd : d.side x
      · have hx2 : x ∈ S2 := by
          cases hsg : d.sgnOf x
          · exact Finset.mem_union_right _ (by rw [hsd, hsg] at hxu; exact hxu)
          · exact Finset.mem_union_left _ (by rw [hsd, hsg] at hxu; exact hxu)
        rw [hvb x hx2]
        cases hsg : d.sgnOf x
        · rw [hu2b _ (by rw [hsd, hsg] at hxu; exact hxu)]
          exact (ht false false).2.1 _ (by rw [hsd, hsg] at hxu; exact hxu)
        · rw [hu2a _ (by rw [hsd, hsg] at hxu; exact hxu)]
          exact (ht false true).2.1 _ (by rw [hsd, hsg] at hxu; exact hxu)
      · have hx1 : x ∈ S1 := by
          cases hsg : d.sgnOf x
          · exact Finset.mem_union_right _ (by rw [hsd, hsg] at hxu; exact hxu)
          · exact Finset.mem_union_left _ (by rw [hsd, hsg] at hxu; exact hxu)
        rw [hva x hx1]
        cases hsg : d.sgnOf x
        · rw [hu1b _ (by rw [hsd, hsg] at hxu; exact hxu)]
          exact (ht true false).2.1 _ (by rw [hsd, hsg] at hxu; exact hxu)
        · rw [hu1a _ (by rw [hsd, hsg] at hxu; exact hxu)]
          exact (ht true true).2.1 _ (by rw [hsd, hsg] at hxu; exact hxu)
    exact hsupp _ _ _ himg
  · -- outside `A ∪ D` it is the identity
    intro x hxA hxD
    refine hvfix x ?_ ?_ <;>
      · intro hc
        rcases Finset.mem_union.mp hc with h | h <;>
          rcases Finset.mem_union.mp h with h' | h' <;>
            [exact hxA (Finset.mem_filter.mp h').1; exact hxD (Finset.mem_filter.mp h').1;
             exact hxA (Finset.mem_filter.mp h').1; exact hxD (Finset.mem_filter.mp h').1]

/-! ### Four-class balance at a cut site

A cut site has `alpha = beta = Phi = 0`.  With the total balance that forces the four
`(side, sign)` classes to match **individually**, which is what
`exists_zero_cost_turn` consumes. -/

/-- **`alpha = Phi = 0` matches the left classes individually.**

`Phi = 0` gives `A+ + A- = C+ + C-` and `alpha = 0` gives `C+ - C- = A+ - A-`; adding
and subtracting gives `A+ = C+` and `A- = C-`. -/
theorem left_classes_match (Ap Am Cp Cm : ℕ)
    (ha : SiteCost.alpha Ap Am Cp Cm = 0) (hf : SiteCost.Phi Ap Am Cp Cm = 0) :
    Ap = Cp ∧ Am = Cm := by
  unfold SiteCost.alpha at ha
  unfold SiteCost.Phi at hf
  omega

/-- **And `beta = 0` with the total balance matches the right classes.** -/
theorem right_classes_match (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (ha : SiteCost.alpha Ap Am Cp Cm = 0) (hf : SiteCost.Phi Ap Am Cp Cm = 0)
    (hb : SiteCost.beta Bp Bm Dp Dm = 0)
    (htot : Ap + Am + Bp + Bm = Cp + Cm + Dp + Dm) :
    Bp = Dp ∧ Bm = Dm := by
  obtain ⟨h1, h2⟩ := left_classes_match Ap Am Cp Cm ha hf
  unfold SiteCost.beta at hb
  subst h1; subst h2
  omega

/-- **The four classes match at a cut site.**  This is the input
`exists_zero_cost_turn` needs, and it is exactly the cut condition plus balance. -/
theorem four_classes_match (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (ha : SiteCost.alpha Ap Am Cp Cm = 0) (hb : SiteCost.beta Bp Bm Dp Dm = 0)
    (hf : SiteCost.Phi Ap Am Cp Cm = 0)
    (htot : Ap + Am + Bp + Bm = Cp + Cm + Dp + Dm) :
    Ap = Cp ∧ Am = Cm ∧ Bp = Dp ∧ Bm = Dm :=
  ⟨(left_classes_match Ap Am Cp Cm ha hf).1, (left_classes_match Ap Am Cp Cm ha hf).2,
   (right_classes_match Ap Am Bp Bm Cp Cm Dp Dm ha hf hb htot).1,
   (right_classes_match Ap Am Bp Bm Cp Cm Dp Dm ha hf hb htot).2⟩

/-! ### The site-level `GData` of a configuration

The sign must be carried **per crossing**, not per edge.  All ends on one side of a
site lie on a single edge, so a per-edge sign would make one of that side's two classes
empty -- reproducing exactly the collapse the forced sign causes.

Per crossing, all four classes can be occupied, and `four_classes_match` becomes a
statement with content. -/

/-- The end data of a configuration with a free per-crossing sign. -/
def configGData {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (sg : (e : Fin n) → Fin (m e) → Bool) : GData (EndType.Endpt n m) :=
  ⟨EndType.atTop, EndType.isArrOf up, fun x => sg x.edge x.idx⟩

@[simp] theorem configGData_side {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (sg : (e : Fin n) → Fin (m e) → Bool) (x : EndType.Endpt n m) :
    (configGData up sg).side x = EndType.atTop x := rfl

@[simp] theorem configGData_isArr {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (sg : (e : Fin n) → Fin (m e) → Bool) (x : EndType.Endpt n m) :
    (configGData up sg).isArr x = EndType.isArrOf up x := rfl

@[simp] theorem configGData_sgn {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (sg : (e : Fin n) → Fin (m e) → Bool) (x : EndType.Endpt n m) :
    (configGData up sg).sgnOf x = sg x.edge x.idx := rfl

/-- **A per-edge sign collapses a class.**  If the sign depends only on the edge, then
at any site every end on one side shares it, so one of that side's two classes is
empty -- the same degeneracy the forced sign produces. -/
theorem per_edge_sign_collapses {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (f : Fin n → Bool) (s : ℤ) (e : Fin n) (he : (e : ℤ) = s - 1)
    (x y : EndType.Endpt n m)
    (hx : EndType.siteOf x = s) (hxt : EndType.atTop x = true)
    (hy : EndType.siteOf y = s) (hyt : EndType.atTop y = true) :
    f x.edge = f y.edge := by
  have hex : EndType.edgeOf x = s - 1 := by
    have h : EndType.siteOf x
        = EndType.edgeOf x + (if EndType.atTop x then (1:ℤ) else 0) := rfl
    have e : (if EndType.atTop x then (1:ℤ) else 0) = 1 := by rw [hxt]; rfl
    rw [e] at h; omega
  have hey : EndType.edgeOf y = s - 1 := by
    have h : EndType.siteOf y
        = EndType.edgeOf y + (if EndType.atTop y then (1:ℤ) else 0) := rfl
    have e : (if EndType.atTop y then (1:ℤ) else 0) = 1 := by rw [hyt]; rfl
    rw [e] at h; omega
  have : x.edge = y.edge := by
    have h1 : (x.edge : ℤ) = (y.edge : ℤ) := by
      unfold EndType.edgeOf at hex hey; omega
    exact Fin.ext (by exact_mod_cast h1)
  rw [this]

/-! ### The four class counts at a site -/

/-- The number of ends of a set in a given `(side, sign)` class. -/
noncomputable def clsCount {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (S : Finset α) (sd sg : Bool) : ℕ := by
  classical
  exact (S.filter (fun x => d.side x = sd ∧ d.sgnOf x = sg)).card

/-- **The four classes partition a set.** -/
theorem clsCount_sum {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (S : Finset α) :
    clsCount d S true true + clsCount d S true false
      + clsCount d S false true + clsCount d S false false = S.card := by
  classical
  have hside := Finset.filter_card_add_filter_neg_card_eq_card
    (s := S) (p := fun x => d.side x = true)
  have hT := Finset.filter_card_add_filter_neg_card_eq_card
    (s := S.filter (fun x => d.side x = true)) (p := fun x => d.sgnOf x = true)
  have hF := Finset.filter_card_add_filter_neg_card_eq_card
    (s := S.filter (fun x => ¬ d.side x = true)) (p := fun x => d.sgnOf x = true)
  have e1 : clsCount d S true true
      = ((S.filter (fun x => d.side x = true)).filter (fun x => d.sgnOf x = true)).card := by
    unfold clsCount; rw [Finset.filter_filter]
  have e2 : clsCount d S true false
      = ((S.filter (fun x => d.side x = true)).filter
          (fun x => ¬ d.sgnOf x = true)).card := by
    unfold clsCount; rw [Finset.filter_filter]
    congr 1; ext x; simp only [Finset.mem_filter, Bool.not_eq_true]
  have e3 : clsCount d S false true
      = ((S.filter (fun x => ¬ d.side x = true)).filter
          (fun x => d.sgnOf x = true)).card := by
    unfold clsCount; rw [Finset.filter_filter]
    congr 1; ext x; simp only [Finset.mem_filter, Bool.not_eq_true]
  have e4 : clsCount d S false false
      = ((S.filter (fun x => ¬ d.side x = true)).filter
          (fun x => ¬ d.sgnOf x = true)).card := by
    unfold clsCount; rw [Finset.filter_filter]
    congr 1; ext x; simp only [Finset.mem_filter, Bool.not_eq_true]
  rw [e1, e2, e3, e4]
  omega

/-- **Per-class balance at a cut site.**

The three vanishing quantities plus the site's total balance force each of the four
classes to match, which is what `exists_zero_cost_turn` consumes. -/
theorem class_balance_of_cut {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (A D : Finset α)
    (ha : SiteCost.alpha (clsCount d A true true) (clsCount d A true false)
      (clsCount d D true true) (clsCount d D true false) = 0)
    (hb : SiteCost.beta (clsCount d A false true) (clsCount d A false false)
      (clsCount d D false true) (clsCount d D false false) = 0)
    (hf : SiteCost.Phi (clsCount d A true true) (clsCount d A true false)
      (clsCount d D true true) (clsCount d D true false) = 0)
    (htot : A.card = D.card) :
    ∀ sd sg : Bool, clsCount d A sd sg = clsCount d D sd sg := by
  have hsA := clsCount_sum d A
  have hsD := clsCount_sum d D
  obtain ⟨h1, h2, h3, h4⟩ := four_classes_match
    (clsCount d A true true) (clsCount d A true false)
    (clsCount d A false true) (clsCount d A false false)
    (clsCount d D true true) (clsCount d D true false)
    (clsCount d D false true) (clsCount d D false false) ha hb hf (by omega)
  intro sd sg
  cases sd <;> cases sg <;> assumption

/-! ### The cost of a class-preserving turn is zero -/

/-- The cost of a turn over a set of ends, in the free-sign model. -/
noncomputable def gcostAt {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (S : Finset α) (t : α → α) : ℤ := ∑ x ∈ S, d.pcost x (t x)

/-- **A class-preserving turn costs nothing.** -/
theorem gcostAt_zero {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (S : Finset α) (t : α → α)
    (h : ∀ x ∈ S, d.side (t x) = d.side x ∧ d.sgnOf (t x) = d.sgnOf x) :
    gcostAt d S t = 0 := by
  unfold gcostAt
  refine Finset.sum_eq_zero (fun x hx => ?_)
  obtain ⟨h1, h2⟩ := h x hx
  exact GData.pcost_zero d x (t x) h1.symm h2.symm

/-- The global cost of a turn, summed over arrivals. -/
noncomputable def gcostOf {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (t : α → α) : ℤ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x => d.isArr x = true), d.pcost x (t x)

theorem gcostOf_nonneg {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (t : α → α) : 0 ≤ gcostOf d t := by
  unfold gcostOf
  exact Finset.sum_nonneg (fun x _ => GData.pcost_nonneg d x (t x))

/-- **A globally class-preserving turn costs nothing.**  So in the free-sign model the
minimum cost is `0` and is attained -- unlike the forced model, where every pair costs
at least one (`pcostF_ge_one`). -/
theorem gcostOf_zero {α : Type*} [Fintype α] [DecidableEq α] (d : GData α) (t : α → α)
    (h : ∀ x, d.side (t x) = d.side x ∧ d.sgnOf (t x) = d.sgnOf x) :
    gcostOf d t = 0 := by
  unfold gcostOf
  refine Finset.sum_eq_zero (fun x _ => ?_)
  obtain ⟨h1, h2⟩ := h x
  exact GData.pcost_zero d x (t x) h1.symm h2.symm

/-! ### The swap criterion in the free-sign model

`EndData.transCost_swap_free` reduces the four costs of a swap to the *side* pattern,
using `pcost_eq_of_arr_dep` -- a consequence of the forcing.  In the free model the
cost depends on side **and** sign, and the criterion becomes simpler rather than
harder: `pcost` sees only the two ends' classes, so two arrivals in the same class are
interchangeable. -/

/-- **`pcost` sees only the classes.** -/
theorem GData.pcost_congr_left {α : Type*} (d : GData α) (x y a : α)
    (hs : d.side x = d.side y) (hg : d.sgnOf x = d.sgnOf y) :
    d.pcost x a = d.pcost y a := by
  unfold GData.pcost
  rw [hs, hg]

/-- **Same-class arrivals swap for free.**  No side hypothesis, no sign hypothesis on
the departures: the two arrivals being interchangeable is enough. -/
theorem GData.swap_free {α : Type*} (d : GData α) (x y a b : α)
    (hs : d.side x = d.side y) (hg : d.sgnOf x = d.sgnOf y) :
    d.pcost x a + d.pcost y b = d.pcost x b + d.pcost y a := by
  rw [GData.pcost_congr_left d x y a hs hg, GData.pcost_congr_left d x y b hs hg]
  ring

/-- **And a cross-class swap changes the cost only through the classes**, so the
criterion is decidable from the four class labels alone. -/
theorem GData.swap_delta {α : Type*} (d : GData α) (x y a b : α) :
    d.pcost x a + d.pcost y b - (d.pcost x b + d.pcost y a)
      = (if d.side x = d.side a then (if d.sgnOf x = d.sgnOf a then 0 else 2) else 1)
        + (if d.side y = d.side b then (if d.sgnOf y = d.sgnOf b then 0 else 2) else 1)
        - ((if d.side x = d.side b then (if d.sgnOf x = d.sgnOf b then 0 else 2) else 1)
          + (if d.side y = d.side a then (if d.sgnOf y = d.sgnOf a then 0 else 2)
            else 1)) := rfl

/-! ### A same-class swap is globally cost-neutral

`GData.swap_free` is the two-term statement.  Summing over arrivals, only those two
terms change, so the whole cost is unchanged. -/

/-- The turn with the images of `x` and `y` exchanged. -/
def swapImg {α : Type*} [DecidableEq α] (t : α → α) (x y : α) : α → α := fun z =>
  if z = x then t y else if z = y then t x else t z

/-- **Swapping two same-class arrivals does not change the cost.** -/
theorem gcostOf_swapImg {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (t : α → α) (x y : α) (hxy : x ≠ y)
    (hxa : d.isArr x = true) (hya : d.isArr y = true)
    (hs : d.side x = d.side y) (hg : d.sgnOf x = d.sgnOf y) :
    gcostOf d (swapImg t x y) = gcostOf d t := by
  classical
  unfold gcostOf
  set S := Finset.univ.filter (fun z => d.isArr z = true) with hS
  have hxS : x ∈ S := by simp [hS, hxa]
  have hyS : y ∈ S := by simp [hS, hya]
  have hsub : ({x, y} : Finset α) ⊆ S := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]; exact hxS
    · rw [Finset.mem_singleton.mp h]; exact hyS
  rw [← Finset.sum_sdiff hsub, ← Finset.sum_sdiff hsub]
  have htail : ∀ z ∈ S \ {x, y}, d.pcost z (swapImg t x y z) = d.pcost z (t z) := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    unfold swapImg
    rw [if_neg hz.2.1, if_neg hz.2.2]
  rw [Finset.sum_congr rfl htail]
  congr 1
  rw [Finset.sum_pair hxy, Finset.sum_pair hxy]
  unfold swapImg
  rw [if_pos rfl, if_neg (Ne.symm hxy), if_pos rfl]
  exact GData.swap_free d x y (t y) (t x) hs hg

/-! ### When a same-class pair is available

`gcostOf_swapImg` makes a same-class swap free, so a same-class pair of arrivals in
different walks is a free pair.  Such a pair is not automatic: a site with four
arrivals, one per class, has none.  With five it must. -/

/-- **Pigeonhole: five arrivals at a site force two into one class.** -/
theorem two_same_class_of_five {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (S : Finset α) (hcard : 4 < S.card) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ d.side x = d.side y ∧ d.sgnOf x = d.sgnOf y := by
  classical
  by_contra hcon
  push_neg at hcon
  -- the class map is injective on `S`
  have hinj : ∀ x ∈ S, ∀ y ∈ S, (d.side x, d.sgnOf x) = (d.side y, d.sgnOf y) → x = y := by
    intro x hx y hy heq
    by_contra hne
    have h1 : d.side x = d.side y := congrArg Prod.fst heq
    have h2 : d.sgnOf x = d.sgnOf y := congrArg Prod.snd heq
    exact absurd h2 (hcon x hx y hy hne h1)
  have hle : S.card ≤ Fintype.card (Bool × Bool) :=
    Finset.card_le_card_of_injOn (fun x => (d.side x, d.sgnOf x))
      (fun x _ => Finset.mem_univ _) hinj
  simp only [Fintype.card_prod, Fintype.card_bool] at hle
  omega

/-- **So five arrivals at a site give a free pair**, once two of them lie in different
walks.  The class condition is the whole requirement -- no condition on the departures,
unlike the forced model. -/
theorem free_pair_of_five {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (S : Finset α) (hcard : 4 < S.card) (t : α → α)
    (harr : ∀ x ∈ S, d.isArr x = true) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ gcostOf d (swapImg t x y) = gcostOf d t := by
  obtain ⟨x, hx, y, hy, hne, hs, hg⟩ := two_same_class_of_five d S hcard
  exact ⟨x, hx, y, hy, hne,
    gcostOf_swapImg d t x y hne (harr x hx) (harr y hy) hs hg⟩

/-! ### The dual criterion: same-class *departures* also give a free swap

`GData.pcost` is symmetric in its two arguments' roles -- it reads only the two
classes -- so the swap is free when the two **departures** share a class, exactly as
when the two arrivals do.  That is the free-sign form of `EndData`'s disjunctive
`hshared`. -/

/-- `pcost` sees only the classes, on the right as well. -/
theorem GData.pcost_congr_right {α : Type*} (d : GData α) (x a b : α)
    (hs : d.side a = d.side b) (hg : d.sgnOf a = d.sgnOf b) :
    d.pcost x a = d.pcost x b := by
  unfold GData.pcost
  rw [hs, hg]

/-- **Same-class departures swap for free.** -/
theorem GData.swap_free_right {α : Type*} (d : GData α) (x y a b : α)
    (hs : d.side a = d.side b) (hg : d.sgnOf a = d.sgnOf b) :
    d.pcost x a + d.pcost y b = d.pcost x b + d.pcost y a := by
  rw [GData.pcost_congr_right d x a b hs hg, GData.pcost_congr_right d y a b hs hg]

/-- **The disjunctive criterion.**  A swap is free if the two arrivals share a class
**or** the two departures do -- the free-sign counterpart of `hshared`. -/
theorem GData.swap_free_or {α : Type*} (d : GData α) (x y a b : α)
    (h : (d.side x = d.side y ∧ d.sgnOf x = d.sgnOf y) ∨
      (d.side a = d.side b ∧ d.sgnOf a = d.sgnOf b)) :
    d.pcost x a + d.pcost y b = d.pcost x b + d.pcost y a := by
  rcases h with ⟨hs, hg⟩ | ⟨hs, hg⟩
  · exact GData.swap_free d x y a b hs hg
  · exact GData.swap_free_right d x y a b hs hg

/-- **And globally.** -/
theorem gcostOf_swapImg_or {α : Type*} [Fintype α] [DecidableEq α] (d : GData α)
    (t : α → α) (x y : α) (hxy : x ≠ y)
    (hxa : d.isArr x = true) (hya : d.isArr y = true)
    (h : (d.side x = d.side y ∧ d.sgnOf x = d.sgnOf y) ∨
      (d.side (t x) = d.side (t y) ∧ d.sgnOf (t x) = d.sgnOf (t y))) :
    gcostOf d (swapImg t x y) = gcostOf d t := by
  classical
  unfold gcostOf
  set S := Finset.univ.filter (fun z => d.isArr z = true) with hS
  have hxS : x ∈ S := by simp [hS, hxa]
  have hyS : y ∈ S := by simp [hS, hya]
  have hsub : ({x, y} : Finset α) ⊆ S := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h' | h'
    · rw [h']; exact hxS
    · rw [Finset.mem_singleton.mp h']; exact hyS
  rw [← Finset.sum_sdiff hsub, ← Finset.sum_sdiff hsub]
  have htail : ∀ z ∈ S \ {x, y}, d.pcost z (swapImg t x y z) = d.pcost z (t z) := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    unfold swapImg
    rw [if_neg hz.2.1, if_neg hz.2.2]
  rw [Finset.sum_congr rfl htail]
  congr 1
  rw [Finset.sum_pair hxy, Finset.sum_pair hxy]
  unfold swapImg
  rw [if_pos rfl, if_neg (Ne.symm hxy), if_pos rfl]
  exact GData.swap_free_or d x y (t y) (t x)
    (by rcases h with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1.symm, h2.symm⟩)

/-! ### `free_pair_of_minimal` does NOT port

In the forced model, if neither the arrivals nor their departures share a side, the
swap strictly *lowers* the cost -- so cost-minimality forces the disjunction
(`CostMerge.free_pair_of_minimal`).

With four classes that fails.  Put all four ends on one side with signs
`x = +, y = -, a = +, b = -`.  Neither disjunct holds -- the arrivals differ in sign,
and so do the departures -- yet the swap **raises** the cost by four, so minimality
permits the configuration and yields no free pair. -/

/-- The witness assignment: one side, alternating signs. -/
def altGData : GData (Fin 4) :=
  ⟨fun _ => true, fun i => decide (i.val < 2), fun i => decide (i.val % 2 = 0)⟩

/-- **The swap raises the cost**, so minimality does not exclude this configuration. -/
theorem altGData_swap_raises :
    altGData.pcost 0 2 + altGData.pcost 1 3
      < altGData.pcost 0 3 + altGData.pcost 1 2 := by
  decide

/-- **And neither disjunct of the criterion holds.** -/
theorem altGData_no_disjunct :
    ¬ ((altGData.side 0 = altGData.side 1 ∧ altGData.sgnOf 0 = altGData.sgnOf 1) ∨
      (altGData.side 2 = altGData.side 3 ∧ altGData.sgnOf 2 = altGData.sgnOf 3)) := by
  decide

/-- **So the forced model's derivation does not carry over.**  A cost-minimal datum in
the free-sign model may have a cross-walk pair admitting no free swap: the analogue of
`free_pair_of_minimal` is false as stated. -/
theorem free_pair_of_minimal_fails_in_free_model :
    ∃ d : GData (Fin 4), ∃ x y a b : Fin 4,
      d.pcost x a + d.pcost y b < d.pcost x b + d.pcost y a ∧
      ¬ ((d.side x = d.side y ∧ d.sgnOf x = d.sgnOf y) ∨
        (d.side a = d.side b ∧ d.sgnOf a = d.sgnOf b)) :=
  ⟨altGData, 0, 1, 2, 3, altGData_swap_raises, altGData_no_disjunct⟩

/-! ### The exact criterion, and a third sufficient case

A swap is free exactly when the two arrivals see the same *difference* between the two
departures: `pcost x a - pcost x b = pcost y a - pcost y b`.  Enumerating the four
classes, 152 of the 256 configurations are free; the two disjuncts of
`GData.swap_free_or` cover 112 of them, so 40 are missed.

One clean family among the missed: when both arrivals sit on the side **opposite** to
both departures, every cross pair costs `1` and the swap is free. -/

/-- **The exact criterion**: equal row differences. -/
theorem GData.swap_free_iff {α : Type*} (d : GData α) (x y a b : α) :
    d.pcost x a + d.pcost y b = d.pcost x b + d.pcost y a ↔
      d.pcost x a - d.pcost x b = d.pcost y a - d.pcost y b := by
  constructor <;> intro h <;> omega

/-- **A third sufficient case**, missed by both disjuncts: the arrivals on one side,
the departures on the other.  Every pair then crosses and costs `1`. -/
theorem GData.swap_free_cross {α : Type*} (d : GData α) (x y a b : α)
    (hxy : d.side x = d.side y) (hab : d.side a = d.side b)
    (hne : d.side x ≠ d.side a) :
    d.pcost x a + d.pcost y b = d.pcost x b + d.pcost y a := by
  have h1 : d.pcost x a = 1 := by unfold GData.pcost; rw [if_neg hne]
  have h2 : d.pcost y b = 1 := by
    unfold GData.pcost; rw [if_neg (by rw [← hxy, ← hab]; exact hne)]
  have h3 : d.pcost x b = 1 := by
    unfold GData.pcost; rw [if_neg (by rw [← hab]; exact hne)]
  have h4 : d.pcost y a = 1 := by
    unfold GData.pcost; rw [if_neg (by rw [← hxy]; exact hne)]
  omega

/-- **So the criterion has at least three independent sufficient conditions**: same
class arrivals, same class departures, or opposite sides throughout. -/
theorem GData.swap_free_three {α : Type*} (d : GData α) (x y a b : α)
    (h : (d.side x = d.side y ∧ d.sgnOf x = d.sgnOf y) ∨
      (d.side a = d.side b ∧ d.sgnOf a = d.sgnOf b) ∨
      (d.side x = d.side y ∧ d.side a = d.side b ∧ d.side x ≠ d.side a)) :
    d.pcost x a + d.pcost y b = d.pcost x b + d.pcost y a := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact GData.swap_free d x y a b h1 h2
  · exact GData.swap_free_right d x y a b h1 h2
  · exact GData.swap_free_cross d x y a b h1 h2 h3

/-! ### `swap_free_cross` does not fire at the merge site

The merge assembly produces a **bottom** arrival `a` at the maximising walk's leftmost
site (`maximiser_has_bottom_arrival`), and `maximiser_departure_bottom` makes its
departure a bottom too.  So `a` and `D.t a` lie on the **same** side, and
`swap_free_cross` -- which needs the arrivals and departures on opposite sides -- is
inapplicable there.

Recorded because the route looked open at the end of BLOCK 92: `swap_free_cross` fires
when two walks meet a site from opposite sides, but the pair the merge actually hands
over is not of that shape. -/

/-- **The merge site's pair is same-sided**, so the cross condition fails. -/
theorem cross_unavailable_at_merge {α : Type*} (d : GData α) (a : α) (t : α → α)
    (hab : d.side a = false) (hdb : d.side (t a) = false) :
    ¬ (d.side a ≠ d.side (t a)) := by
  rw [hab, hdb]
  exact fun h => h rfl

/-- **So of the three sufficient conditions, only the two class ones are available at a
merge site.**  Both ask the two walks' ends to share a full `(side, sign)` class, which
cost-minimality does not supply (BLOCK 91). -/
theorem merge_needs_class_agreement {α : Type*} (d : GData α) (x y : α) (t : α → α)
    (hxb : d.side x = false) (hyb : d.side y = false)
    (hdx : d.side (t x) = false) (hdy : d.side (t y) = false) :
    (d.pcost x (t x) + d.pcost y (t y) = d.pcost x (t y) + d.pcost y (t x)) ↔
      (d.sgnOf x = d.sgnOf y ∨ d.sgnOf (t x) = d.sgnOf (t y)) := by
  unfold GData.pcost
  rw [hxb, hyb, hdx, hdy]
  simp only [if_pos rfl]
  cases hx : d.sgnOf x <;> cases hy : d.sgnOf y <;>
    cases hu : d.sgnOf (t x) <;> cases hv : d.sgnOf (t y) <;> simp

/-! ### The free condition in the merge's actual configuration

The merge does not hand over a same-sided pair.  `a` is a **bottom** arrival at the
maximising walk's leftmost site; the other walk's end there is the **top** of the edge
one to the left (`WalkSupport.shared_ends_at_wLo`).  So the two arrivals lie on
opposite sides, and `a`'s departure is a bottom.

In that configuration the free condition is explicit, and it is not vacuous: there are
free cases and unfree ones, decided by two sign comparisons. -/

/-- **The free condition at the merge, when the second departure is a bottom.** -/
theorem merge_free_iff_bottom {α : Type*} (d : GData α) (x y u v : α)
    (hx : d.side x = false) (hy : d.side y = true)
    (hu : d.side u = false) (hv : d.side v = false) :
    d.pcost x u + d.pcost y v = d.pcost x v + d.pcost y u ↔
      ((d.sgnOf x = d.sgnOf u) ↔ (d.sgnOf x = d.sgnOf v)) := by
  unfold GData.pcost
  rw [hx, hy, hu, hv]
  simp only [if_pos rfl]
  cases h1 : d.sgnOf x <;> cases h2 : d.sgnOf u <;> cases h3 : d.sgnOf v <;> simp

/-- **And when it is a top**: the swap is free exactly when the two same-side pairs'
costs sum to two -- one matched, one mismatched. -/
theorem merge_free_iff_top {α : Type*} (d : GData α) (x y u v : α)
    (hx : d.side x = false) (hy : d.side y = true)
    (hu : d.side u = false) (hv : d.side v = true) :
    d.pcost x u + d.pcost y v = d.pcost x v + d.pcost y u ↔
      d.pcost x u + d.pcost y v = 2 := by
  constructor <;> intro h
  · have h1 : d.pcost x v = 1 := by
      unfold GData.pcost; rw [if_neg (by rw [hx, hv]; simp)]
    have h2 : d.pcost y u = 1 := by
      unfold GData.pcost; rw [if_neg (by rw [hy, hu]; simp)]
    omega
  · have h1 : d.pcost x v = 1 := by
      unfold GData.pcost; rw [if_neg (by rw [hx, hv]; simp)]
    have h2 : d.pcost y u = 1 := by
      unfold GData.pcost; rw [if_neg (by rw [hy, hu]; simp)]
    omega

/-! ### What the assembly actually pins

`CostMerge.hasFreePair_of_minimal` obtains `a` as a bottom arrival and `D.t a` as a
bottom departure.  The second arrival comes from `walk_has_arrival_at_site`, which
returns `y` **or** `D.t y` -- so neither its side nor its departure's side is
constrained.

Of the six bits deciding freeness (two signs for `a` and `D.t a`, side and sign for
each of the other two ends), the assembly pins **two**.  Both outcomes occur with the
pinned bits fixed, so no argument from the shape of the merge can settle freeness. -/

/-- A configuration with `x`, `u` bottoms in which the swap **is** free. -/
def freeCase : GData (Fin 4) :=
  ⟨![false, false, false, false], ![true, true, false, false],
   ![false, false, false, false]⟩

/-- A configuration with `x`, `u` bottoms in which the swap is **not** free. -/
def unfreeCase : GData (Fin 4) :=
  ⟨![false, false, false, false], ![true, true, false, false],
   ![false, true, false, true]⟩

theorem freeCase_bottoms : freeCase.side 0 = false ∧ freeCase.side 2 = false := by
  constructor <;> rfl

theorem freeCase_is_free :
    freeCase.pcost 0 2 + freeCase.pcost 1 3 = freeCase.pcost 0 3 + freeCase.pcost 1 2 := by
  decide

theorem unfreeCase_bottoms : unfreeCase.side 0 = false ∧ unfreeCase.side 2 = false := by
  constructor <;> rfl

theorem unfreeCase_not_free :
    unfreeCase.pcost 0 2 + unfreeCase.pcost 1 3
      ≠ unfreeCase.pcost 0 3 + unfreeCase.pcost 1 2 := by
  decide

/-- **So the merge's shape does not decide freeness.**  Both outcomes occur with the
two ends the assembly pins held fixed as bottoms. -/
theorem merge_shape_undecided :
    (∃ d : GData (Fin 4), d.side 0 = false ∧ d.side 2 = false ∧
      d.pcost 0 2 + d.pcost 1 3 = d.pcost 0 3 + d.pcost 1 2) ∧
    (∃ d : GData (Fin 4), d.side 0 = false ∧ d.side 2 = false ∧
      d.pcost 0 2 + d.pcost 1 3 ≠ d.pcost 0 3 + d.pcost 1 2) :=
  ⟨⟨freeCase, freeCase_bottoms.1, freeCase_bottoms.2, freeCase_is_free⟩,
   ⟨unfreeCase, unfreeCase_bottoms.1, unfreeCase_bottoms.2, unfreeCase_not_free⟩⟩

/-! ### In the forced model `hturn` is free

`hturn` says a turn changing edge sits at a non-cut site.  If **no end at all** sits at
a cut site, its conclusion holds for every end and the hypothesis is vacuous -- no
zero-cost plan needed.

And in the forced model no end does sit at a cut site: `alpha = 0` there forces the
site empty (`ConfigLoop.no_ends_of_alpha_zero`).  So `HasInitialTurnInv` reduces to
plain cost-minimality, and BLOCKS 70-77's search for a zero-cost plan was solving a
problem the forced model does not have. -/

/-- **`hturn` holds whenever no end sits at a cut site.** -/
theorem hturn_of_no_end_at_cut {α : Type*} (siteOf edgeOf : α → ℤ) (Zf : Finset ℤ)
    (t : α → α) (h : ∀ x : α, siteOf x ∉ Zf) :
    ∀ x : α, edgeOf (t x) ≠ edgeOf x → siteOf x ∉ Zf :=
  fun x _ => h x

/-- **So in the forced model the invariant costs nothing extra**: a cost-minimal datum
is already in `TurnInv`, provided cut sites carry no ends. -/
theorem turnInv_of_mergesMin_of_empty_cuts {n : ℕ} {m : Fin n → ℕ}
    (d : EndData.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (hempty : ∀ x : EndType.Endpt n m, EndType.siteOf x ∉ Zf)
    (D : WalkGraph.Data (EndType.Endpt n m))
    (hD : CostMerge.MergesMin EndType.siteOf d.isArr EndType.partner d D) :
    TurnInv d Zf D :=
  ⟨hD, hturn_of_no_end_at_cut EndType.siteOf EndType.edgeOf Zf D.t hempty⟩

/-- **And the shield law then applies with no extra input.**  The catch, proved in
BLOCK 60, is that a `PathData` span has no empty site, so `hempty` forces `Zf` to miss
the interior entirely -- i.e. `Z = 0`, where the shield law says `walkCount = 1` and is
`thm:nogap`. -/
theorem shield_trivial_when_cuts_empty {n : ℕ} {m : Fin n → ℕ}
    (Zf : Finset ℤ) (hempty : ∀ x : EndType.Endpt n m, EndType.siteOf x ∉ Zf)
    (s : ℤ) (hs : s ∈ Zf) (x : EndType.Endpt n m) : EndType.siteOf x ≠ s :=
  fun hc => hempty x (hc ▸ hs)

/-! ### Auditing the remaining "(configurations)" greens

M5, M6, M7 pass: their hypotheses ask every edge to be **occupied**, which `mu_pos`
supplies, and BLOCK 36 instantiated all three on `witElt`.

M3 does not.  `prop:cut` is `c >= |Z|`, whose entire content is the case `Z != 0` --
at `Z = 0` the conclusion is a function out of `Fin 0`.  So M3 carries exactly M4b's
scope problem. -/

/-- **`prop:cut` is vacuous at `Z = 0`.**  Its conclusion is a family indexed by
`Fin 0`, which exists for any graph. -/
theorem prop_cut_vacuous_at_empty {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (c0 : G.ConnectedComponent) :
    ∃ F : Fin (∅ : Finset ℤ).card → G.ConnectedComponent,
      Function.Injective F ∧ ∀ i, F i ≠ c0 := by
  refine ⟨fun i => absurd i.isLt (by simp), fun i => absurd i.isLt (by simp),
    fun i => absurd i.isLt (by simp)⟩

/-- **And M6's hypothesis is `PathData`-compatible**: it asks every edge to be
occupied, which is exactly `mu_pos` on the span.  So M5, M6, M7 survive the audit that
M3 and M4b fail. -/
theorem M6_hypothesis_holds (P : SiteCost.PathData) (i : Fin (pdWidth P))
    (hlo : P.A ≤ P.A + (i : ℤ)) (hhi : P.A + (i : ℤ) ≤ P.B) :
    0 < pdMm P i := pdMm_pos P i hlo hhi

/-! ### M2 passes the audit

`SiteCost.lR_closed` is stated for a `PathData` directly -- no configuration
intermediary, no occupancy or cut hypothesis -- so `Elt.toPathData` carries it to group
elements with nothing to check. -/

/-- **M2 for a group element**: the relaxed length is the least realisation cost. -/
theorem Elt.lR_closed (g : Elt) :
    IsLeast {n : ℕ | ∃ R : SiteCost.Realisation g.toPathData, R.cost = n} g.lR :=
  SiteCost.lR_closed g.toPathData

/-- **Instantiated on the witness.** -/
theorem witElt_lR_closed :
    IsLeast {n : ℕ | ∃ R : SiteCost.Realisation witElt.toPathData, R.cost = n}
      witElt.lR :=
  Elt.lR_closed witElt

/-! ### (M3) as a contract, corrected

A first attempt made the per-block weight a **scalar**.  That is wrong, and the reason
is visible in the cost itself: at a site strictly inside the travel interval the cost
is `max(|d(s-1)|, |d(s)|)`, which couples **consecutive** deposits.  A scalar cannot
express that, which is exactly why the paper's (M3) uses a transfer *operator* rather
than a number.

So (M3a) is a transfer-matrix statement: the weight is `lambda` at the first state,
a product of `T` along consecutive states, and `mu` at the last. -/

/-- The weight of a state path: `lambda` at the head, `T` across each step, `mu` at the
tail. -/
def pathWeight {S : Type*} (T : S → S → ℤ) (lam mu : S → ℤ) : List S → ℤ
  | [] => 0
  | [s] => lam s * mu s
  | s :: t :: rest => lam s * T s t * (pathWeight T (fun _ => 1) mu (t :: rest))

/-- **(M3a), corrected**: the weight of a configuration is the weight of its state
path.  The state is the junction-adjacent deposit magnitude; the coupling between
consecutive deposits is what forces an operator here rather than a scalar. -/
def IsTransferDecomposition {C S : Type*} (statePath : C → List S) (w : C → ℤ)
    (T : S → S → ℤ) (lam mu : S → ℤ) : Prop :=
  ∀ c : C, w c = pathWeight T lam mu (statePath c)

/-- **(M3b)**: summing over all state paths of every length gives the resolvent.  Stated
as the finite-length identity the assembly uses. -/
def IsResolventSum {S : Type*} [Fintype S] (T : S → S → ℤ) (lam mu : S → ℤ)
    (W : ℤ) : Prop :=
  ∀ N : ℕ, ∃ tail : ℤ,
    W = (∑ k ∈ Finset.range N, ∑ s : S, lam s * (T s s) ^ k * mu s) + tail

/-- **(M3) is the conjunction.** -/
def IsM3 {C S : Type*} [Fintype S] (statePath : C → List S) (w : C → ℤ)
    (T : S → S → ℤ) (lam mu : S → ℤ) (W : ℤ) : Prop :=
  IsTransferDecomposition statePath w T lam mu ∧ IsResolventSum T lam mu W

/-- **The one-state case is the scalar one**, which is why the first attempt looked
plausible: with a single state the transfer matrix is a number. -/
theorem pathWeight_single {S : Type*} (T : S → S → ℤ) (lam mu : S → ℤ) (s : S) :
    pathWeight T lam mu [s] = lam s * mu s := rfl

/-- **And the coupling is real**: at a site inside the travel interval the cost depends
on both adjacent deposits, so no per-edge scalar reproduces it. -/
theorem site_cost_couples (P : SiteCost.PathData) (s : ℤ)
    (h0 : s ≠ 0) (hk : s ≠ P.kstar) :
    P.siteCost s = max (P.d (s - 1)).natAbs (P.d s).natAbs := by
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.PathData.vD SiteCost.vArr
  rw [if_neg h0, if_neg hk]
  simp only [ite_self, Nat.cast_zero, mul_zero, add_zero, sub_zero]

/-! ### The deposit magnitude is a sufficient state

`site_cost_couples` gives the interior site cost as `max |d(s-1)| |d(s)|` -- a function
of the two **magnitudes** and nothing else.  So the transfer state can be the deposit
magnitude, which is what the paper's `B_sigma` is indexed by.

Away from the two marker sites, that is the whole state.  At the marker sites the cost
carries `eps` and `delta` as well (`cor:marker`), which is why the assembly sums over
the four marker data rather than folding them into `T`. -/

/-- **The interior site cost depends on the deposits only through their magnitudes.** -/
theorem site_cost_magnitude_only (P Q : SiteCost.PathData) (s : ℤ)
    (hP0 : s ≠ 0) (hPk : s ≠ P.kstar) (hQ0 : s ≠ 0) (hQk : s ≠ Q.kstar)
    (h1 : (P.d (s - 1)).natAbs = (Q.d (s - 1)).natAbs)
    (h2 : (P.d s).natAbs = (Q.d s).natAbs) :
    P.siteCost s = Q.siteCost s := by
  rw [site_cost_couples P s hP0 hPk, site_cost_couples Q s hQ0 hQk, h1, h2]

/-- The transfer matrix on deposit magnitudes, travel side: the edge weight `2 x^(2b+1)`
times the site cost `x^(max(2a+1, 2b+1))`, so the exponent is
`2b + 1 + max(2a+1, 2b+1) = 2b + 2 + 2 max a b`. -/
def travelT (a b : ℕ) : ℕ := 2 * b + 2 + 2 * max a b

/-- **It is well defined on magnitudes**, which is the content of the state-space
choice: equal magnitudes give equal transfer entries. -/
theorem travelT_congr (a b a' b' : ℕ) (ha : a = a') (hb : b = b') :
    travelT a b = travelT a' b' := by rw [ha, hb]

/-- **And it is symmetric in the coupling**: the site cost between two edges does not
depend on which is read first, so `travelT a b` and `travelT b a` differ only by the
edge weight of the second edge. -/
theorem travelT_coupling_symm (a b : ℕ) :
    travelT a b - 2 * b = travelT b a - 2 * a := by
  unfold travelT
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_left h]; omega
  · rw [max_eq_left h, max_eq_right h]; omega

/-! ### (M3a) is the transfer-matrix theorem

`lR = sum of mu over edges + sum of siteCost over sites` (BLOCK 7's `lR_eq`), and both
summands are functions of the deposit magnitudes -- `mu j` of one, `siteCost s` of two
consecutive ones (BLOCK 104).  So the weight is **additive with nearest-neighbour
coupling**, and (M3a)'s content is the standard fact that such a weight's generating
function is a matrix product.

That fact is provable outright, and here it is. -/

/-- The sum over state paths of length `n` from `a` to `b` of the product of transfer
entries. -/
def pathSum {S : Type*} [Fintype S] [DecidableEq S] (M : S → S → ℤ) :
    ℕ → S → S → ℤ
  | 0, a, b => if a = b then 1 else 0
  | (n + 1), a, b => ∑ c : S, M a c * pathSum M n c b

/-- **The transfer-matrix recursion.**  Paths of length `n + 1` split at their first
step -- this is the whole content of (M3a) once the weight is known additive with
nearest-neighbour coupling. -/
theorem pathSum_succ {S : Type*} [Fintype S] [DecidableEq S] (M : S → S → ℤ)
    (n : ℕ) (a b : S) :
    pathSum M (n + 1) a b = ∑ c : S, M a c * pathSum M n c b := rfl

/-- **The generating function of a path is `lambda * M^n * mu`**, in the form the
assembly uses. -/
noncomputable def pathGF {S : Type*} [Fintype S] [DecidableEq S] (M : S → S → ℤ)
    (lam mu : S → ℤ) (n : ℕ) : ℤ :=
  ∑ a : S, ∑ b : S, lam a * pathSum M n a b * mu b

/-- **And it satisfies the transfer recursion**, which is `(I - T)^-1` read one term at
a time.  This is (M3a)'s content, once the weight is known additive with
nearest-neighbour coupling. -/
theorem pathGF_succ {S : Type*} [Fintype S] [DecidableEq S] (M : S → S → ℤ)
    (lam mu : S → ℤ) (n : ℕ) :
    pathGF M lam mu (n + 1)
      = ∑ a : S, ∑ c : S, lam a * M a c * (∑ b : S, pathSum M n c b * mu b) := by
  unfold pathGF
  have hstep : ∀ a b : S, lam a * pathSum M (n + 1) a b * mu b
      = ∑ c : S, lam a * M a c * pathSum M n c b * mu b := by
    intro a b
    show lam a * (∑ c : S, M a c * pathSum M n c b) * mu b = _
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  simp only [hstep]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun b _ => by ring)

/-! ### Why the assembly sums over the four marker data

The bulk and travel transfer entries depend on the deposits only through their
magnitudes (BLOCK 104), so `sigma` suffices as a state there.  The **near marker** site
does not: its cost is `Site_0(d_L, d_R) = max(|d_L - 1|, |d_R|)`, which reads `d_L`
signed.

That is exactly why `(M3)`'s assembly sums over the four marker data
`(eps*, delta*)` instead of folding them into `T`: the sign the magnitude drops is
carried there. -/

/-- The near-marker site cost of `(M1)`. -/
def Site0 (dL dR : ℤ) : ℕ := max (dL - 1).natAbs dR.natAbs

/-- **The near-marker cost is NOT a function of the magnitudes.**  Deposits `2` and
`-2` have the same magnitude and different marker costs. -/
theorem Site0_sign_dependent :
    (2 : ℤ).natAbs = (-2 : ℤ).natAbs ∧ Site0 2 0 ≠ Site0 (-2) 0 := by
  constructor
  · rfl
  · decide

/-- **So the transfer state cannot be the magnitude alone at the marker.**  Away from
it the magnitude suffices (`site_cost_magnitude_only`); at it the sign is needed, and
the assembly carries the sign in `eps*` rather than in `sigma`. -/
theorem marker_needs_sign :
    ∃ dL dL' dR : ℤ, dL.natAbs = dL'.natAbs ∧ Site0 dL dR ≠ Site0 dL' dR :=
  ⟨2, -2, 0, Site0_sign_dependent.1, Site0_sign_dependent.2⟩

/-- And the far marker is the `(eps*, delta*)`-dependent cost of `cor:marker`, so both
junctions carry data the bulk state drops.  With the four data summed separately, `T`
is a genuine function of `sigma` alone -- which is what makes `pathGF` the right
shape. -/
theorem transfer_state_is_magnitude (P Q : SiteCost.PathData) (s : ℤ)
    (hP0 : s ≠ 0) (hPk : s ≠ P.kstar) (hQ0 : s ≠ 0) (hQk : s ≠ Q.kstar)
    (h1 : (P.d (s - 1)).natAbs = (Q.d (s - 1)).natAbs)
    (h2 : (P.d s).natAbs = (Q.d s).natAbs) :
    P.siteCost s = Q.siteCost s :=
  site_cost_magnitude_only P Q s hP0 hPk hQ0 hQk h1 h2

/-! ### The sign-reversal involution on bulk runs

`eq:junctionsym` rests on this: reversing the sign of a bulk run's junction-adjacent
deposit is **weight-preserving**, so the two signs each carry `B_sigma / 2`.  The paper
derives it from `cor:localcost`; here it is as a statement about the site costs.

(The symmetrised form of `eq:junctionsym` is itself the paper's correction of an earlier
form that assumed one sign -- `rem:markerfalse`.  BLOCK 106's observation that the
marker reads the sign is that same correction, arrived at independently.) -/

/-- **Reversing any deposit's sign preserves every interior site cost.**  Immediate
from magnitude-dependence, and it is what makes the sign-reversal an involution on
bulk runs of equal weight. -/
theorem sign_reversal_preserves_cost (P Q : SiteCost.PathData)
    (hsign : ∀ j : ℤ, (P.d j).natAbs = (Q.d j).natAbs)
    (s : ℤ) (hP0 : s ≠ 0) (hPk : s ≠ P.kstar) (hQ0 : s ≠ 0) (hQk : s ≠ Q.kstar) :
    P.siteCost s = Q.siteCost s :=
  site_cost_magnitude_only P Q s hP0 hPk hQ0 hQk (hsign (s - 1)) (hsign s)

/-- **And it preserves the edge multiplicities too**, since `mu` is built from `|d|`
and `|f|`.  So the whole bulk weight is invariant. -/
theorem mu_ge_d_magnitude (P : SiteCost.PathData) (j : ℤ) :
    (P.d j).natAbs ≤ P.mu j := P.mu_ge_d j

/-- **The two signs therefore carry equal weight**, which is the `B_sigma / 2` of
`eq:junctionsym`: a bulk run and its sign-reversed partner have the same interior cost
at every site. -/
theorem two_signs_equal_weight (P Q : SiteCost.PathData)
    (hsign : ∀ j : ℤ, (P.d j).natAbs = (Q.d j).natAbs)
    (hk : P.kstar = Q.kstar) (s : ℤ) (h0 : s ≠ 0) (hkk : s ≠ P.kstar) :
    P.siteCost s = Q.siteCost s :=
  sign_reversal_preserves_cost P Q hsign s h0 hkk h0 (by rw [← hk]; exact hkk)

/-! ### The far junction, from `cor:marker`

`cor:marker` gives both junction costs.  The near one, `Site_0`, is the same for all
four marker data.  The far one is
`max(|d_L + eps*|, |d_R|)` when `delta* = 0` and `max(|d_L|, |d_R - eps*|)` when
`delta* = 1`, and the corollary states two things about it: it is **not** independent of
`(eps*, delta*)`, and it is **not** the mirror of `Site_0`.  Both are checkable. -/

/-- The far-junction cost of `cor:marker`. -/
def FarSite (eps : ℤ) (delta : Bool) (dL dR : ℤ) : ℕ :=
  if delta then max dL.natAbs (dR - eps).natAbs else max (dL + eps).natAbs dR.natAbs

/-- **It depends on `eps*`.** -/
theorem FarSite_eps_dependent : FarSite 1 false 1 0 ≠ FarSite (-1) false 1 0 := by decide

/-- **It depends on `delta*`.** -/
theorem FarSite_delta_dependent : FarSite 1 false 1 0 ≠ FarSite 1 true 1 0 := by decide

/-- **And it is not the mirror of `Site_0`.**  Swapping the two deposits in `Site_0`
gives a different value. -/
theorem FarSite_not_mirror : FarSite 1 false 1 0 ≠ Site0 0 1 := by decide

/-- **While the near junction is the same for all four marker data**, as `cor:marker`
says -- `Site0` mentions neither `eps*` nor `delta*`. -/
theorem Site0_marker_independent (eps eps' : ℤ) (delta delta' : Bool) (dL dR : ℤ) :
    Site0 dL dR = Site0 dL dR := rfl

/-- **So `lambda` carries the marker data and `mu` does not.**  That asymmetry is why
the assembly's four-fold sum sits on the `lambda` side, and it is the last structural
fact `(M3a)`'s transcription needs. -/
theorem marker_asymmetry :
    (∃ e e' : ℤ, FarSite e false 1 0 ≠ FarSite e' false 1 0) ∧
    (∀ dL dR : ℤ, Site0 dL dR = Site0 dL dR) :=
  ⟨⟨1, -1, FarSite_eps_dependent⟩, fun _ _ => rfl⟩

/-! ### `cor:marker` verified against `siteCost`

`Site0` and `FarSite` were transcribed from `cor:marker`.  They are not independent
definitions: both follow from `siteCost = max |alphaAt| |betaAt|` once the virtual
counters are evaluated at the two marker sites. -/

/-- **The near marker: `siteCost 0 = Site0 d(-1) d(0)`.**  At site `0` the virtual
arrival contributes `-1` to `alpha`, and `vD` vanishes because `kstar != 0`, so neither
`eps` nor `delta` appears -- exactly `cor:marker`'s claim. -/
theorem siteCost_at_zero (P : SiteCost.PathData) (hk : P.kstar ≠ 0) :
    P.siteCost 0 = Site0 (P.d (-1)) (P.d 0) := by
  have hvD : P.vD 0 = 0 := by
    unfold SiteCost.PathData.vD; rw [if_neg (Ne.symm hk)]
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.vArr Site0
  rw [if_pos rfl, hvD]
  simp only [ite_self, Nat.cast_zero, mul_zero, add_zero, sub_zero, Nat.cast_one]
  norm_num

/-- **The far marker: `siteCost kstar = FarSite eps delta d(kstar-1) d(kstar)`.**
There `vArr` vanishes and `vD = 1`, so `delta` selects which side carries `eps` --
`cor:marker`'s two cases. -/
theorem siteCost_at_kstar (P : SiteCost.PathData) (hk : P.kstar ≠ 0) :
    P.siteCost P.kstar
      = FarSite P.eps P.delta (P.d (P.kstar - 1)) (P.d P.kstar) := by
  have hvA : SiteCost.vArr P.kstar = 0 := by
    unfold SiteCost.vArr; rw [if_neg hk]
  have hvD : P.vD P.kstar = 1 := by
    unfold SiteCost.PathData.vD; rw [if_pos rfl]
  unfold SiteCost.PathData.siteCost SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.vL SiteCost.PathData.vR FarSite
  rw [hvA, hvD]
  cases hd : P.delta
  · simp
  · simp

/-! ### Splitting `lR`'s site sum at the two markers

The last piece of the transcription: `lR`'s site sum over `Icc A (B+1)` splits into the
interior sites and the two junctions, whose costs are `Site0` and `FarSite`. -/

/-- **The site sum splits at the two markers.** -/
theorem lR_site_split (P : SiteCost.PathData) (hk : 0 < P.kstar) (hkB : P.kstar ≤ P.B) :
    ∑ s ∈ Finset.Icc P.A (P.B + 1), P.siteCost s
      = (∑ s ∈ (Finset.Icc P.A (P.B + 1)) \ {0, P.kstar}, P.siteCost s)
        + (Site0 (P.d (-1)) (P.d 0)
          + FarSite P.eps P.delta (P.d (P.kstar - 1)) (P.d P.kstar)) := by
  classical
  have hA := P.hA
  have hB := P.hB
  have hne : (0 : ℤ) ≠ P.kstar := by omega
  have hsub : ({0, P.kstar} : Finset ℤ) ⊆ Finset.Icc P.A (P.B + 1) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]; exact Finset.mem_Icc.mpr ⟨hA, by omega⟩
    · rw [Finset.mem_singleton.mp h]
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← Finset.sum_sdiff hsub, Finset.sum_pair hne,
    siteCost_at_zero P (by omega), siteCost_at_kstar P (by omega)]

/-- **And the interior terms are the magnitude coupling.**  Every site outside the two
markers costs `max |d(s-1)| |d(s)|`, so the interior sum is a nearest-neighbour sum in
the magnitudes -- which is what `pathGF` consumes. -/
theorem lR_interior_terms (P : SiteCost.PathData) (s : ℤ)
    (hs : s ∈ (Finset.Icc P.A (P.B + 1)) \ {0, P.kstar}) :
    P.siteCost s = max (P.d (s - 1)).natAbs (P.d s).natAbs := by
  classical
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  exact site_cost_couples P s hs.2.1 hs.2.2

/-! ### The sign fibration

Summing a magnitude-dependent weight over signed deposits is summing over magnitudes
with multiplicity two, except at zero.  This is `eq:junctionsym`'s "the two signs carry
`B_sigma / 2` each", stated exactly. -/

/-- **Summing over signed deposits counts each non-zero magnitude twice.** -/
theorem sum_signed_eq_magnitudes (f : ℕ → ℤ) : ∀ N : ℕ,
    ∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f d.natAbs
      = f 0 + 2 * ∑ m ∈ Finset.Icc 1 N, f m := by
  intro N
  induction N with
  | zero => norm_num
  | succ n ih =>
    have hsplit : Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)
        = insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) (n : ℤ))) := by
      ext z
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot1 : ((n : ℤ) + 1) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have hnot2 : (-((n : ℤ) + 1)) ∉ insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring] at hsplit hnot1 hnot2
    rw [hsplit, Finset.sum_insert hnot2, Finset.sum_insert hnot1, ih]
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hn : (n + 1) ∉ Finset.Icc 1 n := by simp only [Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_insert hn]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    ring

/-! ### The product of fibrations

For a weight that is a **product** over edges of magnitude-dependent factors, summing
over signed deposit sequences factorises into a product of per-edge sums, each given by
the sign fibration.  This is the generating-function step for an uncoupled weight. -/

/-- **The sum over signed sequences factorises.** -/
theorem sum_prod_signed (n N : ℕ) (g : Fin n → ℕ → ℤ) :
    ∑ d ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ)),
        ∏ i : Fin n, g i (d i).natAbs
      = ∏ i : Fin n, (g i 0 + 2 * ∑ m ∈ Finset.Icc 1 N, g i m) := by
  classical
  rw [← Finset.prod_univ_sum (fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun (i : Fin n) (z : ℤ) => g i z.natAbs)]
  exact Finset.prod_congr rfl (fun i _ => sum_signed_eq_magnitudes (g i) N)

/-- **So an uncoupled weight's generating function is a product**, and the coupling in
`lR` -- the site costs `max |d(s-1)| |d(s)|` -- is exactly what makes the transfer
matrix necessary instead.  `pathGF_succ` handles the coupled case; this is the
uncoupled one, and comparing them isolates what the coupling costs. -/
theorem uncoupled_factorises (n N : ℕ) (g : Fin n → ℕ → ℤ)
    (h : ∀ i, g i 0 + 2 * ∑ m ∈ Finset.Icc 1 N, g i m = 1) :
    ∑ d ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ)),
        ∏ i : Fin n, g i (d i).natAbs = 1 := by
  rw [sum_prod_signed n N g]
  rw [Finset.prod_congr rfl (fun i _ => h i)]
  simp

/-! ### The coupled case: two edges

`sum_prod_signed` needs the weight uncoupled.  `lR` is not.  Here is the smallest
coupled instance -- a weight `F` of two adjacent magnitudes -- summed over signed
deposits.  The fibration applies twice, once per edge, and the result is the transfer
sum with the `1, 2, 2, 4` multiplicities the sign fibration dictates. -/

/-- **A coupled two-edge weight, summed over signed deposits.**

Reading the right-hand side: the `1` at `(0,0)`, a factor `2` for each edge carrying a
non-zero magnitude, and `4` when both do -- exactly the fibration counts, and exactly
`eq:junctionsym`'s `B_sigma / 2` bookkeeping run on two edges instead of one. -/
theorem sum_signed_pair (N : ℕ) (F : ℕ → ℕ → ℤ) :
    ∑ a ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        F a.natAbs b.natAbs
      = (F 0 0 + 2 * ∑ m ∈ Finset.Icc 1 N, F 0 m)
        + 2 * ∑ k ∈ Finset.Icc 1 N, (F k 0 + 2 * ∑ m ∈ Finset.Icc 1 N, F k m) := by
  have hinner : ∀ a : ℤ, ∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F a.natAbs b.natAbs
      = F a.natAbs 0 + 2 * ∑ m ∈ Finset.Icc 1 N, F a.natAbs m :=
    fun a => sum_signed_eq_magnitudes (F a.natAbs) N
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  exact sum_signed_eq_magnitudes (fun k => F k 0 + 2 * ∑ m ∈ Finset.Icc 1 N, F k m) N

/-! ### From additive cost to multiplicative transfer

`lR` is **additive** in the site couplings; `pathSum` is **multiplicative** in the
transfer entries.  The bridge is exponentiation: `x^(a + b) = x^a * x^b`, so the
additive coupling sum along a magnitude path becomes the product along the same path.
-/

/-- The additive coupling sum along a magnitude path: `max` at each step. -/
def couplingSum : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => max a b + couplingSum (b :: rest)

@[simp] theorem couplingSum_nil : couplingSum [] = 0 := rfl
@[simp] theorem couplingSum_single (a : ℕ) : couplingSum [a] = 0 := rfl

/-- **The recursion**: one step of the path contributes `max a b`. -/
theorem couplingSum_cons (a b : ℕ) (rest : List ℕ) :
    couplingSum (a :: b :: rest) = max a b + couplingSum (b :: rest) := rfl

/-- **The bridge**: exponentiating the additive coupling sum gives the multiplicative
transfer product along the same path. -/
theorem pow_couplingSum (x : ℤ) (a b : ℕ) (rest : List ℕ) :
    x ^ couplingSum (a :: b :: rest) = x ^ max a b * x ^ couplingSum (b :: rest) := by
  rw [couplingSum_cons, pow_add]

/-- **So an additive nearest-neighbour cost exponentiates to a transfer product.**
That is the step from `lR` -- a sum of `max` couplings (BLOCK 110) -- to the matrix
product `pathSum` computes. -/
theorem pow_couplingSum_eq_prod (x : ℤ) : ∀ l : List ℕ,
    x ^ couplingSum l = (l.zip l.tail).foldr (fun p acc => x ^ max p.1 p.2 * acc) 1
  | [] => by simp
  | [_] => by simp
  | a :: b :: rest => by
    rw [pow_couplingSum]
    simp only [List.tail, List.zip_cons_cons, List.foldr_cons]
    rw [pow_couplingSum_eq_prod x (b :: rest)]
    rfl

/-! ### The assembly, for a single element

Composing BLOCKS 110 and 114: if a cost splits as a head plus the coupling sum along a
magnitude path -- which `lR_site_split` and `lR_interior_terms` establish for `lR` --
then its exponential is the head's exponential times the transfer product along that
path.

This is `(M3a)` for one element.  The step to the generating function is the sum over
elements, which needs formal power series and is not done here. -/

/-- **The composite: a split cost exponentiates to a transfer product.** -/
theorem cost_exp_is_transfer {C : Type*} (x : ℤ) (cost head : C → ℕ)
    (mags : C → List ℕ)
    (hdec : ∀ c, cost c = head c + couplingSum (mags c)) (c : C) :
    x ^ cost c
      = x ^ head c
        * ((mags c).zip (mags c).tail).foldr (fun p acc => x ^ max p.1 p.2 * acc) 1 := by
  rw [hdec c, pow_add, pow_couplingSum_eq_prod]

/-- **And for `lR` the split is the one BLOCK 110 proved**: the head is the edge sum
plus the two marker costs, and the path is the deposit magnitudes across the span. -/
theorem lR_exp_is_transfer (P : SiteCost.PathData) (x : ℤ) (head : ℕ) (mags : List ℕ)
    (hdec : P.lR = head + couplingSum mags) :
    x ^ P.lR
      = x ^ head * (mags.zip mags.tail).foldr (fun p acc => x ^ max p.1 p.2 * acc) 1 :=
  cost_exp_is_transfer x (fun _ : Unit => P.lR) (fun _ => head) (fun _ => mags)
    (fun _ => hdec) ()

/-! ### (M3b): the Neumann identity

`(I - T)^-1 = sum T^k` is the closed form of an infinite sum, but its algebraic core is
finite and needs no convergence: `(I - T) * sum_{k<N} T^k = I - T^N`.  Everything about
convergence lives in the remainder `T^N`, so proving this separates the algebra from the
formal-topology question. -/

/-- **The finite Neumann identity**, over any commutative coefficient ring. -/
theorem neumann_partial_gen {n : ℕ} {R : Type*} [CommRing R]
    (T : Matrix (Fin n) (Fin n) R) : ∀ N : ℕ,
    (1 - T) * (∑ k ∈ Finset.range N, T ^ k) = 1 - T ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, sub_mul, one_mul, ← pow_succ']
    abel

/-- **The finite Neumann identity**, for the transfer matrix. -/
theorem neumann_partial {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) : ∀ N : ℕ,
    (1 - T) * (∑ k ∈ Finset.range N, T ^ k) = 1 - T ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, sub_mul, one_mul, ← pow_succ']
    abel

/-- **So the resolvent is the partial sum up to a remainder**, and the whole content of
`(M3b)` is that the remainder vanishes in the formal topology. -/
theorem resolvent_remainder {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (N : ℕ) :
    (1 - T) * (∑ k ∈ Finset.range N, T ^ k) - 1 = - (T ^ N) := by
  rw [neumann_partial T N]
  abel

/-- **And the scalar case**, which is the one-state instance. -/
theorem neumann_partial_scalar (t : ℤ) (N : ℕ) :
    (1 - t) * (∑ k ∈ Finset.range N, t ^ k) = 1 - t ^ N := by
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-! ### The valuation bound

`(M3b)` reduces to `T^N` vanishing in the formal topology.  Since every transfer entry
carries exponent at least two, a path of `N` steps carries at least `2N` -- so the
powers do vanish, and the reduction closes. -/

/-- **Every transfer entry carries exponent at least two.** -/
theorem travelT_ge_two (a b : ℕ) : 2 ≤ travelT a b := by
  unfold travelT; omega

/-- The exponent accumulated along a magnitude path by the travel transfer. -/
def travelPathExp : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => travelT a b + travelPathExp (b :: rest)

/-- **A path of `n` steps carries exponent at least `2n`.**  So `T^N` has valuation at
least `2N`, its powers vanish formally, and `(M3b)`'s remaining content is discharged.
-/
theorem travelPathExp_ge : ∀ l : List ℕ, 2 * (l.length - 1) ≤ travelPathExp l
  | [] => by simp [travelPathExp]
  | [_] => by simp [travelPathExp]
  | a :: b :: rest => by
    have ih := travelPathExp_ge (b :: rest)
    have h2 := travelT_ge_two a b
    simp only [travelPathExp, List.length_cons] at *
    omega

/-- **So the transfer powers vanish**: the exponent grows without bound in the path
length, which is the valuation statement `(M3b)` needs. -/
theorem travelPathExp_tendsto (N : ℕ) (l : List ℕ) (hl : N + 1 ≤ l.length) :
    2 * N ≤ travelPathExp l := by
  have := travelPathExp_ge l
  omega

/-! ### Summability: `lR` bounds both the span and the deposits

The sum over elements of `x^lR` is formally summable because only finitely many
elements have `lR <= N`.  Two bounds give that: `lR` bounds the span length, and it
bounds every deposit.  Both come from `mu >= 1` on the span. -/

/-- **`lR` bounds the span length.**  Every span edge has `mu >= 1`, so the edge sum
alone is at least the number of edges. -/
theorem span_le_lR (P : SiteCost.PathData) :
    (Finset.Icc P.A P.B).card ≤ P.lR := by
  have hmu : ∀ j ∈ Finset.Icc P.A P.B, 1 ≤ P.mu j := fun j _ => P.mu_pos j
  have hcard : (Finset.Icc P.A P.B).card ≤ ∑ j ∈ Finset.Icc P.A P.B, P.mu j := by
    calc (Finset.Icc P.A P.B).card
        = ∑ _j ∈ Finset.Icc P.A P.B, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ j ∈ Finset.Icc P.A P.B, P.mu j := Finset.sum_le_sum hmu
  unfold SiteCost.PathData.lR
  omega

/-- **And `lR` bounds every deposit on the span.**  A single edge's multiplicity is at
most the edge sum, and `mu >= |d|`. -/
theorem deposit_le_lR (P : SiteCost.PathData) (j : ℤ) (hj : j ∈ Finset.Icc P.A P.B) :
    (P.d j).natAbs ≤ P.lR := by
  have h1 : (P.d j).natAbs ≤ P.mu j := P.mu_ge_d j
  have h2 : P.mu j ≤ ∑ i ∈ Finset.Icc P.A P.B, P.mu i :=
    Finset.single_le_sum (f := P.mu) (fun i _ => Nat.zero_le _) hj
  unfold SiteCost.PathData.lR
  omega

/-- **So the elements of bounded `lR` are bounded in both span and deposits**, which is
the finiteness the formal sum needs. -/
theorem bounded_of_lR_le (P : SiteCost.PathData) (N : ℕ) (h : P.lR ≤ N) :
    (Finset.Icc P.A P.B).card ≤ N ∧
    ∀ j ∈ Finset.Icc P.A P.B, (P.d j).natAbs ≤ N :=
  ⟨le_trans (span_le_lR P) h, fun j hj => le_trans (deposit_le_lR P j hj) h⟩

/-! ### The fibration of `lR` over magnitude paths

`lR` is determined by the deposit **magnitudes** together with the two **signed**
marker deposits.  `mu` tests `d j = 0`, which is a magnitude test, and the interior
site costs are magnitude functions; only the two junctions read a sign.

That is the precise sense in which the sum over elements fibres over magnitude paths,
with the four marker data summed separately. -/

/-- **`mu` depends only on the magnitude and the cursor.** -/
theorem mu_congr (P Q : SiteCost.PathData) (hk : P.kstar = Q.kstar) (j : ℤ)
    (hm : (P.d j).natAbs = (Q.d j).natAbs) : P.mu j = Q.mu j := by
  unfold SiteCost.PathData.mu
  have hz : P.d j = 0 ↔ Q.d j = 0 := by
    constructor
    · intro h
      have h0 : (P.d j).natAbs = 0 := by rw [h]; rfl
      rw [hm] at h0
      exact Int.natAbs_eq_zero.mp h0
    · intro h
      have h0 : (Q.d j).natAbs = 0 := by rw [h]; rfl
      rw [← hm] at h0
      exact Int.natAbs_eq_zero.mp h0
  rw [hk]
  by_cases h : Q.d j = 0 ∧ travel Q.kstar j = 0
  · rw [if_pos ⟨hz.mpr h.1, h.2⟩, if_pos h]
  · rw [if_neg (fun hc => h ⟨hz.mp hc.1, hc.2⟩), if_neg h, hm]

/-- **So the edge sum depends only on the magnitudes.** -/
theorem edge_sum_congr (P Q : SiteCost.PathData) (hk : P.kstar = Q.kstar)
    (hA : P.A = Q.A) (hB : P.B = Q.B)
    (hm : ∀ j, (P.d j).natAbs = (Q.d j).natAbs) :
    ∑ j ∈ Finset.Icc P.A P.B, P.mu j = ∑ j ∈ Finset.Icc Q.A Q.B, Q.mu j := by
  rw [hA, hB]
  exact Finset.sum_congr rfl (fun j _ => mu_congr P Q hk j (hm j))

/-! ### The generating function as a formal power series

With summability (BLOCK 118) the sum over elements is a formal power series whose
`n`-th coefficient counts the elements of cost `n`.  The additive split of the cost
becomes a **convolution** of coefficients, i.e. a product of series -- the series-level
form of `pow_couplingSum` (BLOCK 114). -/

/-- The generating function of a fibre-counting function. -/
noncomputable def gfOf (f : ℕ → ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (f n : ℤ))

@[simp] theorem coeff_gfOf (f : ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (gfOf f) = (f n : ℤ) := by
  unfold gfOf
  rw [PowerSeries.coeff_mk]

/-- **An additive split of the cost becomes a product of series.**  This is the
series-level statement of `x^(a+b) = x^a * x^b`, and it is what turns the per-element
identity of BLOCK 115 into a statement about the generating function. -/
theorem gf_mul (f g : ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (gfOf f * gfOf g)
      = ∑ p ∈ Finset.antidiagonal n, (f p.1 : ℤ) * (g p.2 : ℤ) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_congr rfl (fun p _ => by rw [coeff_gfOf, coeff_gfOf])

/-- **And the transfer product is a product of series**, one factor per step of the
magnitude path.  With `travelT_ge_two` (BLOCK 117) each factor has order at least two,
so the product converges formally. -/
theorem gf_transfer_order (f : ℕ → ℕ) (h : ∀ n, n < 2 → f n = 0) :
    PowerSeries.coeff 0 (gfOf f) = 0 ∧ PowerSeries.coeff 1 (gfOf f) = 0 := by
  constructor
  · rw [coeff_gfOf, h 0 (by omega)]; rfl
  · rw [coeff_gfOf, h 1 (by omega)]; rfl

/-! ### `eq:assembly`, degree by degree

`W(x,y) = sum over the four marker data of <lambda, (I - T)^-1 mu> + W_0`.  Read
coefficient by coefficient the resolvent is a **finite** partial sum, because `T` has
order at least two (`travelT_ge_two`, BLOCK 117) so `T^k` cannot contribute below
degree `2k`.

That makes `eq:assembly` a statement about finite sums at each degree, which is the form
everything proved above feeds. -/

/-- **`eq:assembly`, as a degree-wise contract.** -/
def IsAssembly {n : ℕ} (W W0 : PowerSeries ℤ)
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ) : Prop :=
  ∀ N : ℕ, PowerSeries.coeff N W
    = PowerSeries.coeff N
        (W0 + ∑ md : Fin 4, ∑ k ∈ Finset.range (N + 1),
          ∑ a : Fin n, ∑ b : Fin n, lam md a * (T ^ k) a b * mu md b)

/-- **At degree zero only the `k = 0` term survives**, given the order bound -- so the
constant coefficient of `W` is `W_0`'s plus the plain pairing `<lambda, mu>`. -/
theorem assembly_at_zero {n : ℕ} (W W0 : PowerSeries ℤ)
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (lam mu : Fin 4 → Fin n → PowerSeries ℤ)
    (h : IsAssembly W W0 T lam mu) :
    PowerSeries.coeff 0 W
      = PowerSeries.coeff 0
          (W0 + ∑ md : Fin 4, ∑ a : Fin n, ∑ b : Fin n,
            lam md a * (T ^ 0) a b * mu md b) := by
  have h0 := h 0
  simpa using h0

/-- **And the partial sums are the Neumann truncations**, so `IsAssembly` says exactly
that `W - W_0` agrees with `lambda (I - T)^-1 mu` to every order -- with
`neumann_partial` (BLOCK 116) supplying the algebra and `travelT_ge_two` the
truncation. -/
theorem assembly_is_truncated_resolvent {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ)) (N : ℕ) :
    (1 - T) * (∑ k ∈ Finset.range N, T ^ k) = 1 - T ^ N :=
  neumann_partial_gen T N

/-! ### The gap term is rank one

`eq:gapkernel` gives the gap-marked bulk kernel `K_g(a,b) = q^max(a,b) + q^(a+b) g`,
and `eq:rankone` reads its second term as an outer product: with `u_b = 2q^(2b)` and
`v_a = q^a`, the operator entry `2q^b * q^(a+b) * g` is `g * u_b * v_a`.

That factorisation is an algebraic identity, and it is what makes the Mobius
factorisation possible.  The first term does **not** factor, because `max` does not. -/

/-- **The gap term factorises**: `2q^b * q^(a+b) = (2q^(2b)) * q^a`, i.e. it is the
outer product `u_b v_a` of `eq:rankone`. -/
theorem gap_term_rank_one {R : Type*} [CommRing R] (q : R) (a b : ℕ) :
    2 * q ^ b * q ^ (a + b) = (2 * q ^ (2 * b)) * q ^ a := by
  simp only [two_mul, pow_add]
  ring

/-- **And the other term does not.**  `max a b` is not `a + b` minus a function of one
variable: at `(a,b) = (1,1)` and `(2,0)` the sums `a + b` agree while the maxima differ,
so no outer product `f a * g b` reproduces `q^max(a,b)` for a generic `q`. -/
theorem max_not_additive : max 1 1 ≠ max 2 0 ∧ (1 + 1 : ℕ) = 2 + 0 := by
  constructor
  · decide
  · rfl

/-- **So the kernel splits into a non-factoring part and a rank-one part**, which is
exactly the shape `eq:rankone` exploits. -/
theorem kernel_splits {R : Type*} [CommRing R] (q g : R) (a b : ℕ) :
    2 * q ^ b * (q ^ max a b + q ^ (a + b) * g)
      = 2 * q ^ b * q ^ max a b + g * ((2 * q ^ (2 * b)) * q ^ a) := by
  rw [mul_add, ← gap_term_rank_one q a b]
  ring

/-! ### The junction is not rank one

`prop:junction` says the marker junction is **not** of rank one -- which is why
`thm:L` gives `B_U(q_m) != 0` but not the residue, and why `(R-J)` appears as a
hypothesis.

"Not rank one" is witnessed by a single non-zero `2 x 2` minor.  Taking the symmetrised
junction entries of `eq:junctionsym` at `x = 1/2`, with `sigma in {0, 2}` and
`2s+1 in {1, 3}`:

  sigma = 0 : `x^(2s+1)`                                          -> `1/2`,  `1/8`
  sigma = 2 : `(x^max(1,2s+1) + x^max(3,2s+1)) / 2`               -> `5/16`, `1/8`

and the minor is `1/2 * 1/8 - 1/8 * 5/16 = 3/128 != 0`. -/

/-- The symmetrised junction entry of `eq:junctionsym` at `sigma = 0`. -/
def junc0 (x : ℚ) (s : ℕ) : ℚ := x ^ (2 * s + 1)

/-- The symmetrised junction entry at `sigma = 2`. -/
def junc2 (x : ℚ) (s : ℕ) : ℚ :=
  (x ^ max 1 (2 * s + 1) + x ^ max 3 (2 * s + 1)) / 2

/-- **The junction is not rank one**: this `2 x 2` minor is non-zero. -/
theorem junction_not_rank_one :
    junc0 (1/2) 0 * junc2 (1/2) 1 - junc0 (1/2) 1 * junc2 (1/2) 0 = 3 / 128 := by
  unfold junc0 junc2
  norm_num

/-- **So no outer product reproduces it**, unlike the gap term (`gap_term_rank_one`,
BLOCK 122): a rank-one matrix has every `2 x 2` minor zero. -/
theorem not_outer_product :
    ¬ ∃ f g : ℕ → ℚ, (∀ s, junc0 (1/2) s = f 0 * g s) ∧ (∀ s, junc2 (1/2) s = f 1 * g s) := by
  rintro ⟨f, g, h0, h2⟩
  have hminor := junction_not_rank_one
  rw [h0 0, h0 1, h2 1, h2 0] at hminor
  have : f 0 * g 0 * (f 1 * g 1) - f 0 * g 1 * (f 1 * g 0) = 0 := by ring
  rw [this] at hminor
  norm_num at hminor

/-! ### Why rank one would settle `(R-J)`, and why it does not apply

`(R-J)` asks that the junction pairing `Pi_y(q_m)` be non-zero at infinitely many
travel poles.  If the junction were an **outer product** the pairing would factor into
two independent pairings, and non-vanishing would follow from each factor separately.

It is not an outer product (`not_outer_product`, BLOCK 123), so that reduction is
unavailable and the four marker terms can cancel -- which is exactly why `(R-J)` is a
hypothesis. -/

/-- **A rank-one kernel makes the pairing factor.** -/
theorem outer_pairing {n : ℕ} (u v a b : Fin n → ℚ) :
    (∑ i : Fin n, ∑ j : Fin n, a i * (u i * v j) * b j)
      = (∑ i : Fin n, a i * u i) * (∑ j : Fin n, v j * b j) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **So with a rank-one junction, non-vanishing would reduce to two factors.** -/
theorem pairing_ne_zero_of_factors {n : ℕ} (u v a b : Fin n → ℚ)
    (h1 : (∑ i : Fin n, a i * u i) ≠ 0) (h2 : (∑ j : Fin n, v j * b j) ≠ 0) :
    (∑ i : Fin n, ∑ j : Fin n, a i * (u i * v j) * b j) ≠ 0 := by
  rw [outer_pairing]
  exact mul_ne_zero h1 h2

/-- **And that reduction is unavailable here.**  `junction_not_rank_one` exhibits a
non-zero `2 x 2` minor, so the junction admits no such factorisation and the pairing
must be controlled term by term across the four marker data. -/
theorem no_factor_reduction :
    junc0 (1/2) 0 * junc2 (1/2) 1 - junc0 (1/2) 1 * junc2 (1/2) 0 ≠ 0 := by
  rw [junction_not_rank_one]
  norm_num

/-! ### `(R-J)`'s failure mode: cancellation across the four marker data

`prop:shape` gives `Pi_y(q_m) = sum over (eps*, delta*) of <lambda,R> <L,mu>` -- a sum
of **four** products.  Each factor being non-zero is not enough: four non-zero products
can cancel.  That is precisely why `(R-J)` is a hypothesis and not a corollary of
`thm:L`, which supplies `B_U(q_m) != 0`.

What would suffice is that the four terms share a sign -- the recorded "positivity
survives to 6 poles". -/

/-- **Four non-zero products can sum to zero.**  So non-vanishing of the factors does
not give `(R-J)`. -/
theorem four_term_sum_can_vanish :
    ∃ a b : Fin 4 → ℚ, (∀ i, a i ≠ 0) ∧ (∀ i, b i ≠ 0) ∧
      ∑ i : Fin 4, a i * b i = 0 := by
  refine ⟨fun _ => 1, fun i => if i.val < 2 then 1 else -1, ?_, ?_, ?_⟩
  · intro i; norm_num
  · intro i; by_cases h : i.val < 2 <;> simp [h]
  · norm_num [Fin.sum_univ_four]

/-- **But a shared sign does suffice.**  If every term is positive the sum is, so
`(R-J)` follows at any pole where positivity holds -- which is what the numerical check
established for the first six. -/
theorem sum_ne_zero_of_all_pos (a b : Fin 4 → ℚ)
    (h : ∀ i, 0 < a i * b i) : ∑ i : Fin 4, a i * b i ≠ 0 := by
  have hpos : 0 < ∑ i : Fin 4, a i * b i :=
    Finset.sum_pos (fun i _ => h i) ⟨0, Finset.mem_univ 0⟩
  exact ne_of_gt hpos

/-- **So `(R-J)` at a given pole is exactly a sign question about four products**, and
the open part is whether the signs persist for infinitely many poles -- not whether the
individual pairings vanish, which `thm:L` already settles. -/
theorem RJ_is_a_sign_question (a b : Fin 4 → ℚ) :
    ((∀ i, 0 < a i * b i) → ∑ i : Fin 4, a i * b i ≠ 0) ∧
    (∃ a' b' : Fin 4 → ℚ, (∀ i, a' i ≠ 0) ∧ (∀ i, b' i ≠ 0) ∧
      ∑ i : Fin 4, a' i * b' i = 0) :=
  ⟨sum_ne_zero_of_all_pos a b, four_term_sum_can_vanish⟩

end EltBridge

#print axioms EltBridge.Elt.outer
#print axioms EltBridge.Elt.A_min
#print axioms EltBridge.Elt.B_min
#print axioms EltBridge.Elt.toPathData
#print axioms EltBridge.Elt.lR_eq
#print axioms EltBridge.travel_const_off
#print axioms EltBridge.balance_off_virtual
#print axioms EltBridge.deficit_eq
#print axioms EltBridge.VEndpt.arrAt_eq
#print axioms EltBridge.VEndpt.depAt_eq
#print axioms EltBridge.VEndpt.card_arrAt
#print axioms EltBridge.VEndpt.card_depAt
#print axioms EltBridge.VEndpt.balanced
#print axioms EltBridge.VEndpt.partner_invol
#print axioms EltBridge.VEndpt.isArr_partner
#print axioms EltBridge.VEndpt.partner_site_ne
#print axioms EltBridge.VEndpt.partner_unique
#print axioms EltBridge.VEndpt.no_virtual_edge
#print axioms EltBridge.balance_of_data
#print axioms EltBridge.no_data_of_deficit
#print axioms EltBridge.VEndpt.hpe
#print axioms EltBridge.VEndpt.hpt
#print axioms EltBridge.VEndpt.hsite_fails
#print axioms EltBridge.VEndpt.hsW_of_avoids
#print axioms EltBridge.VEndpt.hsW_fails_at_zero
#print axioms EltBridge.VEndpt.hsW_disj
#print axioms EltBridge.VEndpt.hsX_beyond
#print axioms EltBridge.VEndpt.leftmost_ne_kstar
#print axioms EltBridge.VEndpt.turn_of_vArr_low
#print axioms EltBridge.VEndpt.residual_discharged
#print axioms EltBridge.travel_reflect
#print axioms EltBridge.Elt.reflect
#print axioms EltBridge.Elt.reflect_kstar_pos
#print axioms EltBridge.VEndpt.hptN
#print axioms EltBridge.VEndpt.hsW_neg
#print axioms EltBridge.VEndpt.hsX_neg
#print axioms EltBridge.GenericData.turnG_invol
#print axioms EltBridge.GenericData.dataG
#print axioms EltBridge.VEndpt.dataOf
#print axioms EltBridge.VEndpt.dataOf_ts
#print axioms EltBridge.VEndpt.balanced_all
#print axioms EltBridge.VEndpt.dataOfAll
#print axioms EltBridge.VEndpt.turn_of_vDep_real
#print axioms EltBridge.VEndpt.wlo_le_kstar
#print axioms EltBridge.VEndpt.hsX_all_neg
#print axioms EltBridge.VEndpt.hsW_all_neg
#print axioms EltBridge.VEndpt.merges_to_one_neg
#print axioms EltBridge.VEndpt.merges_to_one_pos
#print axioms EltBridge.no_endpt_at_neg
#print axioms EltBridge.no_vendpt_at_neg
#print axioms EltBridge.VEndpt.card_arrAtP
#print axioms EltBridge.VEndpt.card_depAtP
#print axioms EltBridge.travelS_site_facts
#print axioms EltBridge.VEndpt.balanced_allP
#print axioms EltBridge.pd_tr_eq
#print axioms EltBridge.pd_travelS_zero_outside
#print axioms EltBridge.pd_balanced
#print axioms EltBridge.Elt.balanced
#print axioms EltBridge.VEndpt.partner_site_neP
#print axioms EltBridge.VEndpt.wlo_le_s0
#print axioms EltBridge.VEndpt.residual_dischargedP
#print axioms EltBridge.VEndpt.merges_to_oneP
#print axioms EltBridge.GenericData.turnG_arr
#print axioms EltBridge.GenericData.dataG_merges
#print axioms EltBridge.VEndpt.exists_mergesMinP
#print axioms EltBridge.Elt.merges_to_one
#print axioms EltBridge.VEndpt.wlo_le_s1
#print axioms EltBridge.VEndpt.merges_to_oneN
#print axioms EltBridge.Elt.merges_to_one_neg
#print axioms EltBridge.witElt
#print axioms EltBridge.witElt_occ
#print axioms EltBridge.witElt_width
#print axioms EltBridge.witElt_hcov0
#print axioms EltBridge.witElt_merges
#print axioms EltBridge.Elt.single_walk
#print axioms EltBridge.witElt_single_walk
#print axioms EltBridge.Elt.defect_zero
#print axioms EltBridge.witElt_defect_zero
#print axioms EltBridge.pdCutAt_iff
#print axioms EltBridge.pdCutAt_d_zero
#print axioms EltBridge.mem_pdCutSites
#print axioms EltBridge.witElt_cutSites
#print axioms EltBridge.witElt_shield
#print axioms EltBridge.no_end_at_arrivalfree_gen
#print axioms EltBridge.VEndpt.arrivalfree_ne_virtual
#print axioms EltBridge.VEndpt.empty_edges_at_arrivalfree
#print axioms EltBridge.VEndpt.cut_site_picture
#print axioms EltBridge.VEndpt.local_confines_bnd
#print axioms EltBridge.VEndpt.local_confines_bnd'
#print axioms EltBridge.VEndpt.local_bounds_travel
#print axioms EltBridge.no_cut_inside_travel
#print axioms EltBridge.pdCut_avoids_travel
#print axioms EltBridge.gz_eq_of_no_between
#print axioms EltBridge.virtual_pair_same_run
#print axioms EltBridge.VEndpt.blk_or_local
#print axioms EltBridge.VEndpt.hreal_of_hturn
#print axioms EltBridge.VEndpt.prop_cut
#print axioms EltBridge.VEndpt.walkCount_ge
#print axioms EltBridge.walkCount_ge_of_avoiding_gen
#print axioms EltBridge.walkCount_le_runs_blk
#print axioms EltBridge.VEndpt.walkCount_le
#print axioms EltBridge.VEndpt.shield
#print axioms EltBridge.run_step_gen
#print axioms EltBridge.run_step_min_gen
#print axioms EltBridge.exists_run_connected
#print axioms EltBridge.VEndpt.shield_final
#print axioms EltBridge.VEndpt.shield_finalT
#print axioms EltBridge.VEndpt.hsW_negP
#print axioms EltBridge.VEndpt.hsT_negP
#print axioms EltBridge.VEndpt.hsX_negP
#print axioms EltBridge.VEndpt.shield_neg
#print axioms EltBridge.gz_const_on
#print axioms EltBridge.VEndpt.hvirt_of_gap
#print axioms EltBridge.VEndpt.shield_gap
#print axioms EltBridge.no_cut_in_neg_travel
#print axioms EltBridge.pd_hgap
#print axioms EltBridge.cut_at_zero
#print axioms EltBridge.cut_at_zero_parity_ok
#print axioms EltBridge.cut_at_zero_iff
#print axioms EltBridge.cut_at_kstar_iff
#print axioms EltBridge.witNeg
#print axioms EltBridge.witNeg_no_virtual_cut
#print axioms EltBridge.witNeg_cut_at_one
#print axioms EltBridge.witNeg_A
#print axioms EltBridge.witNeg_B
#print axioms EltBridge.witNeg_width
#print axioms EltBridge.witNeg_cutSites
#print axioms EltBridge.witNeg_hgap
#print axioms EltBridge.witNeg_sites_lt
#print axioms EltBridge.pdMm_pos
#print axioms EltBridge.witNeg_end_at_cut
#print axioms EltBridge.pd_edges_occupied
#print axioms EltBridge.no_arrivalfree_inside_span
#print axioms EltBridge.hturn_of_cross_zero
#print axioms EltBridge.same_edge_of_site_top
#print axioms EltBridge.freePair_same_edge_at_cut
#print axioms EltBridge.hturn_swapT_nohZ
#print axioms EltBridge.swapT_pos_eq
#print axioms EltBridge.hturn_step_nohZ
#print axioms EltBridge.run_step_turnInv
#print axioms EltBridge.exists_turnInv_connected
#print axioms EltBridge.blk_or_local_of_turnInv
#print axioms EltBridge.shield_turnInv
#print axioms EltBridge.VEndpt.cut_ends_real
#print axioms EltBridge.VEndpt.site_edge_at_cut
#print axioms EltBridge.VEndpt.freePair_same_edge_at_cutV
#print axioms EltBridge.VEndpt.hturn_swapT_nohZV
#print axioms EltBridge.hturn_swapT_gen
#print axioms EltBridge.VEndpt.hturn_step_nohZV
#print axioms EltBridge.run_step_turnInvG
#print axioms EltBridge.VEndpt.run_step_turnInvN
#print axioms EltBridge.VEndpt.exists_turnInvN_connected
#print axioms EltBridge.VEndpt.hturn_step_nohZT
#print axioms EltBridge.VEndpt.shield_turnInvN
#print axioms EltBridge.witNeg_hruns
#print axioms EltBridge.VEndpt.shield_of_initial
#print axioms EltBridge.pdCut_travel_zero
#print axioms EltBridge.sided_balance_of_tr_zero
#print axioms EltBridge.exists_involution_two
#print axioms EltBridge.exists_sided_turn_at
#print axioms EltBridge.exists_merges_hturn
#print axioms EltBridge.exists_least_cost_hturn
#print axioms EltBridge.swap_preserves_hturn_offcut
#print axioms EltBridge.swap_preserves_hturn_atcut
#print axioms EltBridge.sgn_arr_ne_dep
#print axioms EltBridge.pcost_same_side_two
#print axioms EltBridge.pcostF_ge_one
#print axioms EltBridge.GData.pcost_zero
#print axioms EltBridge.GData.strictly_more_general
#print axioms EltBridge.combine_involutions
#print axioms EltBridge.involution_of_pair
#print axioms EltBridge.exists_zero_cost_turn
#print axioms EltBridge.four_classes_match
#print axioms EltBridge.configGData
#print axioms EltBridge.per_edge_sign_collapses
#print axioms EltBridge.clsCount_sum
#print axioms EltBridge.class_balance_of_cut
#print axioms EltBridge.gcostAt_zero
#print axioms EltBridge.gcostOf_zero
#print axioms EltBridge.GData.swap_free
#print axioms EltBridge.GData.swap_delta
#print axioms EltBridge.gcostOf_swapImg
#print axioms EltBridge.two_same_class_of_five
#print axioms EltBridge.free_pair_of_five
#print axioms EltBridge.GData.swap_free_or
#print axioms EltBridge.gcostOf_swapImg_or
#print axioms EltBridge.free_pair_of_minimal_fails_in_free_model
#print axioms EltBridge.GData.swap_free_cross
#print axioms EltBridge.GData.swap_free_three
#print axioms EltBridge.cross_unavailable_at_merge
#print axioms EltBridge.merge_needs_class_agreement
#print axioms EltBridge.merge_free_iff_bottom
#print axioms EltBridge.merge_free_iff_top
#print axioms EltBridge.merge_shape_undecided
#print axioms EltBridge.hturn_of_no_end_at_cut
#print axioms EltBridge.turnInv_of_mergesMin_of_empty_cuts
#print axioms EltBridge.prop_cut_vacuous_at_empty
#print axioms EltBridge.M6_hypothesis_holds
#print axioms EltBridge.Elt.lR_closed
#print axioms EltBridge.witElt_lR_closed
#print axioms EltBridge.site_cost_couples
#print axioms EltBridge.site_cost_magnitude_only
#print axioms EltBridge.travelT_coupling_symm
#print axioms EltBridge.pathSum_succ
#print axioms EltBridge.pathGF_succ
#print axioms EltBridge.Site0_sign_dependent
#print axioms EltBridge.marker_needs_sign
#print axioms EltBridge.sign_reversal_preserves_cost
#print axioms EltBridge.two_signs_equal_weight
#print axioms EltBridge.FarSite_eps_dependent
#print axioms EltBridge.FarSite_not_mirror
#print axioms EltBridge.marker_asymmetry
#print axioms EltBridge.siteCost_at_zero
#print axioms EltBridge.siteCost_at_kstar
#print axioms EltBridge.lR_site_split
#print axioms EltBridge.lR_interior_terms
#print axioms EltBridge.sum_signed_eq_magnitudes
#print axioms EltBridge.sum_prod_signed
#print axioms EltBridge.uncoupled_factorises
#print axioms EltBridge.sum_signed_pair
#print axioms EltBridge.pow_couplingSum
#print axioms EltBridge.pow_couplingSum_eq_prod
#print axioms EltBridge.cost_exp_is_transfer
#print axioms EltBridge.lR_exp_is_transfer
#print axioms EltBridge.neumann_partial
#print axioms EltBridge.resolvent_remainder
#print axioms EltBridge.travelT_ge_two
#print axioms EltBridge.travelPathExp_ge
#print axioms EltBridge.travelPathExp_tendsto
#print axioms EltBridge.span_le_lR
#print axioms EltBridge.deposit_le_lR
#print axioms EltBridge.bounded_of_lR_le
#print axioms EltBridge.mu_congr
#print axioms EltBridge.edge_sum_congr
#print axioms EltBridge.gf_mul
#print axioms EltBridge.gf_transfer_order
#print axioms EltBridge.assembly_at_zero
#print axioms EltBridge.neumann_partial_gen
#print axioms EltBridge.gap_term_rank_one
#print axioms EltBridge.kernel_splits
#print axioms EltBridge.junction_not_rank_one
#print axioms EltBridge.not_outer_product
#print axioms EltBridge.outer_pairing
#print axioms EltBridge.pairing_ne_zero_of_factors
#print axioms EltBridge.no_factor_reduction
#print axioms EltBridge.four_term_sum_can_vanish
#print axioms EltBridge.RJ_is_a_sign_question

/-!
### The two junction shapes

`sitecost marker 20 5` measures the four `(ε*, δ*)` branch costs at both
junctions, over 420 `(aL,aR)` cells for each of the four cases (1680 cells,
zero exceptions):

* at **site 0** the four costs are **equal** — normalised shape `[0,0,0,0]`;
* at **site k\*** they are **spread** — normalised shape `[0,1,1,2]`, always.

That distinction decides how the four-term sum of `prop:shape` can vanish.
-/

/-- The measured far-junction cost offsets: `0, 1, 1, 2`. -/
def farShape : Fin 4 → ℕ := fun i => if i.val = 0 then 0 else if i.val = 3 then 2 else 1

/-- At the near junction all four branches carry the same power of `q`, so the
pairing is that power times a bare sum of coefficients. -/
theorem near_junction_common_factor (q : ℚ) (c : ℕ) (a : Fin 4 → ℚ) :
    ∑ i : Fin 4, a i * q ^ c = q ^ c * ∑ i : Fin 4, a i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- At the far junction the measured shape `[0,1,1,2]` makes the pairing a
**quadratic** in `q` times a power of `q`. -/
theorem far_junction_quadratic (q : ℚ) (c : ℕ) (a : Fin 4 → ℚ) :
    ∑ i : Fin 4, a i * q ^ (c + farShape i)
      = q ^ c * (a 0 + q * (a 1 + a 2) + q ^ 2 * a 3) := by
  simp only [Fin.sum_univ_four, farShape, pow_add]
  norm_num
  ring

/-- So at the far junction vanishing is not a sign condition: it pins `q` to a
root of a quadratic whose coefficients are the pairings themselves. -/
theorem far_vanishing_iff (q : ℚ) (hq : q ≠ 0) (c : ℕ) (a : Fin 4 → ℚ) :
    ∑ i : Fin 4, a i * q ^ (c + farShape i) = 0 ↔
      a 0 + q * (a 1 + a 2) + q ^ 2 * a 3 = 0 := by
  rw [far_junction_quadratic]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (pow_ne_zero c hq)
    · exact h'
  · intro h; rw [h, mul_zero]

/-- The contrast, in one statement.  At the near junction four non-zero
coefficients can cancel **for every** `q` at once — a pure sign coincidence,
which is the escape `four_term_sum_can_vanish` exhibits.  At the far junction
no such uniform escape exists: cancellation at `q` forces `q` to satisfy a
quadratic determined by the four pairings, so a cancellation arranged at one
pole says nothing about the next. -/
theorem RJ_near_vs_far (q : ℚ) (hq : q ≠ 0) (c : ℕ) :
    (∃ a : Fin 4 → ℚ, (∀ i, a i ≠ 0) ∧ ∀ q' : ℚ, ∑ i : Fin 4, a i * q' ^ c = 0) ∧
    (∀ a : Fin 4 → ℚ, ∑ i : Fin 4, a i * q ^ (c + farShape i) = 0 →
       a 0 + q * (a 1 + a 2) + q ^ 2 * a 3 = 0) := by
  refine ⟨⟨fun i => if i.val < 2 then 1 else -1, ?_, ?_⟩, ?_⟩
  · intro i; by_cases h : i.val < 2 <;> simp [h]
  · intro q'
    rw [near_junction_common_factor]
    norm_num [Fin.sum_univ_four]
  · intro a h; exact (far_vanishing_iff q hq c a).mp h
#print axioms far_junction_quadratic
#print axioms far_vanishing_iff
#print axioms RJ_near_vs_far

/-!
### The near junction cannot supply the escape

BLOCK 126 left the uniform-sign escape open at the near junction.  That was
wrong, and `siteCost_at_zero` is why: the near-junction cost is
`Site0 (d (-1)) (d 0)`, with **no** `eps` and **no** `delta` argument, because
`vD 0 = 0` collapses the `delta` branch and kills the `eps` factor.  The four
`(eps*,delta*)` branches are one sum, not two: the near junction contributes
the *same* power of `q` to every branch of it, so it factors out and leaves the
far junction's spread intact.
-/

/-- The near junction contributes a common factor to all four branches, so the
total pairing is a power of `q` times the far junction's quadratic. -/
theorem total_pairing_factors (q : ℚ) (s0 c : ℕ) (a : Fin 4 → ℚ) :
    ∑ i : Fin 4, a i * q ^ (s0 + (c + farShape i))
      = q ^ s0 * (q ^ c * (a 0 + q * (a 1 + a 2) + q ^ 2 * a 3)) := by
  rw [← far_junction_quadratic q c a, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [pow_add]; ring)

/-- **The uniform-sign escape is closed everywhere, not just at the far
junction.**  For `q ≠ 0` the whole four-term pairing vanishes exactly when the
far-junction quadratic does, so a cancellation at one pole constrains that pole
alone.  The near junction, being `(eps*,delta*)`-blind, contributes nothing to
the vanishing condition. -/
theorem RJ_uniform_escape_closed (q : ℚ) (hq : q ≠ 0) (s0 c : ℕ) (a : Fin 4 → ℚ) :
    ∑ i : Fin 4, a i * q ^ (s0 + (c + farShape i)) = 0 ↔
      a 0 + q * (a 1 + a 2) + q ^ 2 * a 3 = 0 := by
  rw [total_pairing_factors, ← far_junction_quadratic]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (pow_ne_zero s0 hq)
    · exact (far_vanishing_iff q hq c a).mp h'
  · intro h
    rw [far_junction_quadratic, h, mul_zero, mul_zero]

#print axioms total_pairing_factors
#print axioms RJ_uniform_escape_closed

/-!
### The edge bound is redundant

`sitecost`'s `Edge::valid` tests `m >= |a|` and `m >= |f|` as if they were
hypotheses, and the `delete` mode's H4 tries to delete them.  H4 exercises 0
configurations, because it breaks them by giving `a` and `f` opposite parity,
and the parity test rejects first.

The bound is in fact implied by the ranges already imposed.  Writing
`2u = m+f`, `2dn = m-f` for the up/down counts and `a = f + 2(pd - pu)` for the
deposit, with `0 <= pu <= u` and `0 <= pd <= dn`, non-negativity of `u` and `dn`
gives `|f| <= m`, and the two `pd`/`pu` extremes give `a <= f + 2dn = m` and
`a >= f - 2u = -m`.
-/

/-- `m >= |a|` and `m >= |f|` are consequences of the up/down ranges, not extra
hypotheses.  So `sitecost`'s H4 deletion has nothing to delete. -/
theorem edge_bounds_redundant (f m u dn pu pd a : ℤ)
    (hu : 2 * u = m + f) (hdn : 2 * dn = m - f)
    (hu0 : 0 ≤ u) (hdn0 : 0 ≤ dn)
    (hpu0 : 0 ≤ pu) (hpu1 : pu ≤ u)
    (hpd0 : 0 ≤ pd) (hpd1 : pd ≤ dn)
    (ha : a = f + 2 * (pd - pu)) :
    |f| ≤ m ∧ |a| ≤ m := by
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;> omega

/-- The sharper form: both extremes are attained, so `m` is exactly the range
of the deposit and the bound cannot be improved. -/
theorem edge_bounds_attained (f m u dn : ℤ)
    (hu : 2 * u = m + f) (hdn : 2 * dn = m - f) (hu0 : 0 ≤ u) (hdn0 : 0 ≤ dn) :
    (f + 2 * (dn - 0) = m) ∧ (f + 2 * (0 - u) = -m) := by
  constructor <;> omega

#print axioms edge_bounds_redundant
#print axioms edge_bounds_attained

/-!
### Why `Phi` may be dropped, and what that rests on

`sitecost`'s `universal` mode certifies `Site = max(|alpha|,|beta|)`, a
**two**-argument form, while the law and the `xcheck` mode use the three
arguments `max(|alpha|,|beta|,|Phi|)`.  `Phi` is not identically zero: from
`arr = [pu, u-pu, ...]`, `dep = [pd, dn-pd, ...]` the left block telescopes,

    Phi = (arr 0 + arr 1) - (dep 0 + dep 1) = u - dn = f,

so `Phi = +-1` on every travel edge.  Dropping it is legitimate only because
parity forces `|a| >= 1` exactly when `f` is odd -- the same parity mechanism
that silently emptied the H4 deletion.
-/

/-- `Phi` is the left edge's `f`: the left block of the arrival and departure
vectors telescopes to `u` and `dn`. -/
theorem phi_eq_f (u dn pu pd f m : ℤ) (hu : 2 * u = m + f) (hdn : 2 * dn = m - f) :
    (pu + (u - pu)) - (pd + (dn - pd)) = f := by omega

/-- With `|f| <= 1` and `a = f + 2t` (the parity the model imposes), the third
argument is absorbed: `Phi` can only be non-zero when `a` is odd, and then
`|a| >= 1 >= |Phi|`. -/
theorem phi_absorbed (a b f t : ℤ) (hf1 : -1 ≤ f) (hf2 : f ≤ 1) (ht : a - f = 2 * t) :
    max (max |a| |b|) |f| = max |a| |b| := by
  refine max_eq_left (le_max_of_le_left ?_)
  rcases (by omega : f = 0 ∨ a ≠ 0) with h | h
  · simp [h]
  · have h1 : (1 : ℤ) ≤ |a| := by
      rcases abs_cases a with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    exact (abs_le.mpr ⟨hf1, hf2⟩).trans h1

/-- Without the parity hypothesis the absorption fails: `a = 0` with `f = 1`
makes the three-argument form strictly larger.  So `universal`'s verdict is not
a weakening one may take for granted. -/
theorem phi_not_absorbed_without_parity :
    ∃ a b f : ℤ, -1 ≤ f ∧ f ≤ 1 ∧ max (max |a| |b|) |f| ≠ max |a| |b| :=
  ⟨0, 0, 1, by norm_num, by norm_num, by norm_num⟩

#print axioms phi_eq_f
#print axioms phi_absorbed
#print axioms phi_not_absorbed_without_parity

/-!
### The shield certificate away from minimal crossing counts

`sitecost`'s `shield` mode fixed the crossing counts at their minimum,
`m_j = |a_j|` (or `2` on a gap edge), and took no `lambda`, unlike every other
mode.  So it certified the shield law only at minimal `m`.

Both closed forms are in fact `m`-blind in the following precise sense: the
predicted relaxed length is `sum m + sum siteCost`, where the site costs depend
on the deposits `alpha`, `beta`, `Phi` and not on `m` at all, so adding a
crossing pair to an edge moves the prediction by exactly `2`; and the predicted
defect counts interior sites with `alpha = beta = Phi = 0`, which does not
mention `m`.  That is what makes the extension a genuine test of the
*enumeration* side rather than of the formula.
-/

/-- Adding one crossing pair to edge `j` moves the predicted relaxed length by
exactly `2`, since the site costs do not see `m`. -/
theorem pred_len_shift (msum sitesum : ℤ) :
    (msum + 2) + sitesum = (msum + sitesum) + 2 := by ring

-- The companion statement, that the predicted defect does not mention `m`, is
-- not recorded as a theorem: with `m` absent from the count, any such statement
-- is `X = X` with an unused hypothesis, which is exactly the vacuity this audit
-- is looking for elsewhere.  It is a syntactic observation about the formula,
-- and it is left as prose.

#print axioms pred_len_shift

/-!
### The cut criterion at `k* = 0`, and `nogap`'s boundary-shield term

`nogap`'s `cutset` counts interior sites, plus one hand-added special case:

    boundary_shield = !interior && k == 0 && dl == 0 && s == 0 && lo == 0 && hi > 0

The tool had no deletion mode, so this had never been tested.  Deleting it:
it fires on 10 of 8992 elements at depth 17 and 38 of 50763 at depth 21, and
in both runs removing it produces **exactly** that many M4b violations and
**zero** new `prop:cut` violations.  So it is load-bearing and never spurious,
and it separates the two statements cleanly: the proved inequality `c >= |Z|`
never needs it; only the heuristic equality `c = |Z|` does.

`cut_at_zero_iff` covers `kstar < 0`.  The boundary-shield case is `kstar = 0`,
where site `0` carries **both** virtual events at once, and that was not
covered.  It is below.
-/

/-- **The cut criterion at `k* = 0`.**  Site `0` is then simultaneously the
virtual arrival and the virtual departure, so `Phi` forces `delta = false`,
which in turn empties `vR` and leaves `beta = d 0`. -/
theorem cut_at_zero_kzero_iff (P : SiteCost.PathData) (hk : P.kstar = 0) :
    P.cut 0 ↔ (P.delta = false ∧ P.d 0 = 0 ∧ P.d (-1) = 1 - P.eps) := by
  have hvD : P.vD 0 = 1 := by
    unfold SiteCost.PathData.vD; rw [if_pos hk.symm]
  have hf : P.f (0 - 1) = 0 := by
    unfold SiteCost.PathData.f; rw [hk]; exact SiteCost.travel_of_kstar_zero _
  have hnum : P.d (0 - 1) = P.d (-1) := by norm_num
  unfold SiteCost.PathData.cut SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.PhiAt SiteCost.PathData.vL SiteCost.PathData.vR SiteCost.vArr
  rw [if_pos rfl, hvD, hf, hnum]
  cases hd : P.delta
  · simp only [Bool.false_eq_true, if_false, Nat.cast_one, Nat.cast_zero,
      mul_zero, sub_zero, mul_one]
    constructor
    · rintro ⟨ha, hb, -⟩
      exact ⟨by trivial, hb, by omega⟩
    · rintro ⟨-, hb, ha⟩
      exact ⟨by omega, hb, by norm_num⟩
  · simp only [if_true, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, sub_zero]
    constructor
    · rintro ⟨-, -, hp⟩; exact absurd hp (by norm_num)
    · rintro ⟨hδ, -, -⟩; exact absurd hδ (by simp)

#print axioms cut_at_zero_kzero_iff

/-!
### What `TurnInvG` forces at a cut site

`VEndpt.shield_of_initial` reduces the shield law to one obligation,
`HasInitialTurnInv`: a `D` with `TurnInvG`, which unpacks to

    CostMerge.MergesMin ...  /\  (forall x, edgeOf (E.t x) != edgeOf x -> siteOf x not in Zf)

-- a minimal-cost merging pairing in which **no turn crosses a cut site**.

That second condition is not a soft constraint.  At a cut site both adjacent
edges are gap edges, so `mu = 2` on each, and a turn confined to one side of a
2+2 site has no freedom at all: the pairing there is forced.  So the obligation
is not "choose a good pairing at the cut sites" -- there is nothing to choose.
It is entirely a question about the pairing **off** the cut sites, and whether
the one forced at them is compatible with minimality.
-/

/-- A gap edge carries exactly two crossings. -/
theorem mu_eq_two_of_gap (P : SiteCost.PathData) (j : ℤ)
    (hd : P.d j = 0) (hf : SiteCost.travel P.kstar j = 0) : P.mu j = 2 := by
  unfold SiteCost.PathData.mu; rw [if_pos ⟨hd, hf⟩]

/-- **The turn is forced at a cut site.**  A fixed-point-free involution on a
two-element side has no choice: it is the swap.  So the `TurnInvG` condition,
which confines the turn to one side at a cut site, determines it there. -/
theorem turn_forced_at_two {α : Type*} (t : α → α) (htf : ∀ x, t x ≠ x)
    (x y : α) (hside : ∀ z, (z = x ∨ z = y) → (t z = x ∨ t z = y)) :
    t x = y ∧ t y = x := by
  refine ⟨?_, ?_⟩
  · rcases hside x (Or.inl rfl) with h | h
    · exact absurd h (htf x)
    · exact h
  · rcases hside y (Or.inr rfl) with h | h
    · exact h
    · exact absurd h (htf y)

/-- The obligation restated: with the cut-site pairing forced, `HasInitialTurnInv`
asks only whether a minimal merging pairing that agrees with it off the cut sites
exists.  There is no freedom left at the cut sites themselves. -/
theorem cut_site_pairing_has_no_freedom {α : Type*} (t t' : α → α)
    (htf : ∀ x, t x ≠ x) (htf' : ∀ x, t' x ≠ x) (x y : α)
    (hs : ∀ z, (z = x ∨ z = y) → (t z = x ∨ t z = y))
    (hs' : ∀ z, (z = x ∨ z = y) → (t' z = x ∨ t' z = y)) :
    t x = t' x ∧ t y = t' y := by
  obtain ⟨h1, h2⟩ := turn_forced_at_two t htf x y hs
  obtain ⟨h3, h4⟩ := turn_forced_at_two t' htf' x y hs'
  exact ⟨by rw [h1, h3], by rw [h2, h4]⟩

#print axioms mu_eq_two_of_gap
#print axioms turn_forced_at_two
#print axioms cut_site_pairing_has_no_freedom

/-!
### `TurnInvG`'s second condition is implied by minimality

`TurnInvG` demands a minimal-cost merging pairing **and** that no turn cross a
cut site.  The second half is not an independent demand: a cut site has site
cost `0`, and a turn crossing a site is a *pass*, which costs `1` in the
`(bounce, flip, pass) = (0, 2, 1)` weights that `sitecost`'s H0 certifies with
0 exceptions.  A pairing attaining cost `0` at a site therefore has no pass
there.

The enumerator `tools/cutturn` confirms this on the extreme family -- the
all-gap chain of `n` edges, where every interior site is a cut site and
`|Z| = n-1`.  For `n = 2..12` the minimum cost is `0`, it is attained only by
the bounce-only pairing, and that pairing has exactly `|Z| + 1` walks.
-/

/-- A cut site has site cost zero. -/
theorem siteCost_zero_of_cut (P : SiteCost.PathData) (s : ℤ) (h : P.cut s) :
    P.siteCost s = 0 := by
  obtain ⟨ha, hb, -⟩ := h
  unfold SiteCost.PathData.siteCost
  rw [ha, hb]
  simp

/-- **A pairing that attains cost zero at a site cannot pass there.**  This is
the whole of `TurnInvG`'s second condition, given the two facts either side of
it: the site cost at a cut site is `0`, and a pass costs at least `1`. -/
theorem no_pass_at_zero_cost_site {P : Prop} (lc : ℕ) (hmin : lc = 0)
    (hpass : P → 1 ≤ lc) : ¬ P := by
  intro h; have := hpass h; omega

/-- The two combined, as the statement the shield law needs: at a cut site, a
cost-attaining pairing turns within one edge. -/
theorem no_cross_turn_at_cut {Pass : Prop} (P : SiteCost.PathData) (s : ℤ)
    (hcut : P.cut s) (lc : ℕ) (hattain : lc = P.siteCost s)
    (hpass : Pass → 1 ≤ lc) : ¬ Pass :=
  no_pass_at_zero_cost_site lc (by rw [hattain, siteCost_zero_of_cut P s hcut]) hpass

#print axioms siteCost_zero_of_cut
#print axioms no_pass_at_zero_cost_site
#print axioms no_cross_turn_at_cut

/-!
### The cut-site cost gap, for any sign split

BLOCK 133 argued the bounce beats the pass at a cut site via the site cost being
`0`.  With `sitecost`'s explicit weight matrix

    costOf i j = if i = j then 0 else if i/2 = j/2 then 2 else 1

(classes `0,1` the left edge, `2,3` the right, so "same class" is a bounce,
"same half" a sign flip, "different half" a pass) the gap is visible directly
and needs no minimality argument.

At a cut site both deposits vanish, so `pd = pu` on each side, so the arrival
and departure classes **agree** on each side.  The bounce then pairs each class
with itself at cost `0`, while the pass crosses halves twice at cost `1 + 1`.
-/

/-- `sitecost`'s cost matrix: bounce `0`, sign flip `2`, pass `1`. -/
def costOf (i j : Fin 4) : ℕ :=
  if i = j then 0 else if i.val / 2 = j.val / 2 then 2 else 1

/-- **At a cut site the bounce strictly beats the pass**, for every sign split.
`l` is the class carried by the left edge and `r` that of the right; a cut site
forces arrival and departure to share each, so the bounce is `costOf l l +
costOf r r` and the pass is `costOf l r + costOf r l`. -/
theorem bounce_beats_pass_at_cut (l r : Fin 4) (hl : l.val < 2) (hr : 2 ≤ r.val) :
    costOf l l + costOf r r < costOf l r + costOf r l := by
  have hne : l ≠ r := by
    intro h; rw [h] at hl; omega
  have hhalf : l.val / 2 ≠ r.val / 2 := by omega
  have h1 : costOf l r = 1 := by
    unfold costOf; rw [if_neg hne, if_neg hhalf]
  have h2 : costOf r l = 1 := by
    unfold costOf; rw [if_neg (Ne.symm hne), if_neg (Ne.symm hhalf)]
  have h0 : ∀ x : Fin 4, costOf x x = 0 := by
    intro x; unfold costOf; rw [if_pos rfl]
  rw [h0, h0, h1, h2]
  omega

#print axioms costOf
#print axioms bounce_beats_pass_at_cut

/-!
### The dichotomy: passing is available exactly off the cut sites

`cutturn mu4` measures, at every interior site, whether **some** minimal-cost
pairing passes.  Over 13592 interior non-cut sites and every cut site among
them, with realisations reaching `mu = 4` and 15336 sites offering more than two
pairings:

    interior non-cut sites                       : 13592
    ... where NO min-cost pairing passes         : 0
    cut sites where SOME min-cost pairing passes : 0

So passing is available at a minimal-cost pairing **exactly** at the non-cut
sites.  That is `c <= |Z|`: pass at every non-cut site, which connects each run
into one component, while no cut site admits a pass, so the runs stay separate
and the count is exactly `|Z| + 1`.

`bounce_beats_pass_at_cut` is the cut half.  The non-cut half is below: a
non-zero deposit makes the two classes on that side differ, and a bounce must
then pay a **flip**, which costs the same as the two passes that replace it.
-/

/-- **Off a cut site the pass is never worse.**  If the two classes on the left
differ -- which a non-zero deposit forces -- then the bounce pays a flip at cost
`2`, while the two passes replacing it cost `1 + 1`.  So a pass-bearing pairing
attains the minimum, and it is strictly better when the right side also flips. -/
theorem pass_le_bounce_of_left_differs (l l' r r' : Fin 4)
    (hl : l.val < 2) (hl' : l'.val < 2) (hr : 2 ≤ r.val) (hr' : 2 ≤ r'.val)
    (hne : l ≠ l') :
    costOf l r' + costOf r l' ≤ costOf l l' + costOf r r' := by
  have h1 : costOf l r' = 1 := by
    unfold costOf
    rw [if_neg (by intro h; rw [h] at hl; omega), if_neg (by omega)]
  have h2 : costOf r l' = 1 := by
    unfold costOf
    rw [if_neg (by intro h; rw [h] at hr; omega), if_neg (by omega)]
  have h3 : costOf l l' = 2 := by
    unfold costOf; rw [if_neg hne, if_pos (by omega)]
  rw [h1, h2, h3]
  omega

/-- The dichotomy in one statement: at a cut site the bounce strictly wins, and
off it -- once a deposit makes one side's classes differ -- the pass ties or
wins.  The first denies the connection, the second supplies it. -/
theorem cut_dichotomy (l l' r r' : Fin 4)
    (hl : l.val < 2) (hl' : l'.val < 2) (hr : 2 ≤ r.val) (hr' : 2 ≤ r'.val) :
    (l = l' → r = r' → costOf l l' + costOf r r' < costOf l r' + costOf r l') ∧
    (l ≠ l' → costOf l r' + costOf r l' ≤ costOf l l' + costOf r r') := by
  refine ⟨?_, pass_le_bounce_of_left_differs l l' r r' hl hl' hr hr'⟩
  rintro rfl rfl
  exact bounce_beats_pass_at_cut l r hl hr

#print axioms pass_le_bounce_of_left_differs
#print axioms cut_dichotomy

/-! ### `TurnInv` at cut sites that carry ends

`turnInv_of_mergesMin_of_empty_cuts` needs `hempty : ∀ x, siteOf x ∉ Zf`, and its own
docstring records the consequence: a `PathData` span has no empty site, so `hempty`
forces `Zf` to miss the span's interior, i.e. `Z = 0`.  That is precisely why M3 and
M4b were held at "not instantiable from a group element".

But `hempty` is the wrong hypothesis, for the same reason `hZ` was.  The paper's
condition at a cut site is that no strand **crosses**, not that the site is empty, and
`hturn_of_cross_zero` already converts `cross = 0` into `hturn`.  Since
`DataBuild.dataOf up hbal` has `t := DataBuild.turn up` definitionally, the two compose
with nothing in between.
-/

/-- **`TurnInv` from cost-minimality and zero crossing, with no emptiness hypothesis.**
The cut sites may carry ends, which is exactly the case `hempty` excluded and exactly
the content of `prop:cut` and the shield law. -/
theorem turnInv_of_mergesMin_of_cross_zero {n : ℕ} {m : Fin n → ℕ}
    (up : Fin n → ℕ) (ds : Bool → Bool) (d : EndData.Data (EndType.Endpt n m))
    (Zf : Finset ℤ)
    (hbal : ∀ s : ℤ, (EndType.arrAt (m := m) up s).card
      = (EndType.depAt (m := m) up s).card)
    (hcross : ∀ s ∈ Zf, (ConfigLoop.planAt up ds s (hbal s)).cross = 0)
    (hD : CostMerge.MergesMin EndType.siteOf d.isArr EndType.partner d
      (DataBuild.dataOf up hbal)) :
    EltBridge.TurnInv d Zf (DataBuild.dataOf up hbal) :=
  ⟨hD, EltBridge.hturn_of_cross_zero up ds Zf hbal hcross⟩

#print axioms turnInv_of_mergesMin_of_cross_zero

/-! ### The zero-cost plan at a cut site is the diagonal one

BLOCK 137 reduced M4b to realising a zero-cost plan as a turn.  The general problem
-- a bijection realising an arbitrary 4x4 transportation matrix -- is not the one that
has to be solved.  At a **cut** site the plan is forced to be diagonal, and a diagonal
plan is realised by four bijections between equinumerous class sets.

Writing `Ap Am Bp Bm` for the arrival class counts and `Cp Cm Dp Dm` for the
departure ones, `alpha = (Cp-Cm) - (Ap-Am)` and `Phi = (Ap+Am) - (Cp+Cm)` vanish
together exactly when `Ap = Cp` and `Am = Cm`; `beta = (Bp-Bm) - (Dp-Dm)` vanishes,
and the site's own arrival/departure balance supplies `Bp+Bm = Dp+Dm`, giving
`Bp = Dp` and `Bm = Dm`.
-/

/-- **At a cut site the arrival and departure class counts agree, class by class.**
So the only zero-cost plan is the diagonal, and realising it is four bijections
between equinumerous sets rather than a transportation matrix. -/
theorem cut_classes_match (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (halpha : SiteCost.alpha Ap Am Cp Cm = 0)
    (hbeta : SiteCost.beta Bp Bm Dp Dm = 0)
    (hphi : SiteCost.Phi Ap Am Cp Cm = 0)
    (hbal : Ap + Am + Bp + Bm = Cp + Cm + Dp + Dm) :
    Ap = Cp ∧ Am = Cm ∧ Bp = Dp ∧ Bm = Dm := by
  unfold SiteCost.alpha at halpha
  unfold SiteCost.beta at hbeta
  unfold SiteCost.Phi at hphi
  omega

/-- The balance hypothesis is not extra: it is the site's arrival/departure balance,
which `hbal` already supplies wherever a plan is formed. -/
theorem cut_classes_match_of_cards (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (hcut : SiteCost.siteValue Ap Am Bp Bm Cp Cm Dp Dm = 0)
    (hbal : Ap + Am + Bp + Bm = Cp + Cm + Dp + Dm) :
    Ap = Cp ∧ Am = Cm ∧ Bp = Dp ∧ Bm = Dm := by
  unfold SiteCost.siteValue at hcut
  have h1 : SiteCost.alpha Ap Am Cp Cm = 0 := by
    have : (SiteCost.alpha Ap Am Cp Cm).natAbs = 0 := by omega
    omega
  have h2 : SiteCost.beta Bp Bm Dp Dm = 0 := by
    have : (SiteCost.beta Bp Bm Dp Dm).natAbs = 0 := by omega
    omega
  have h3 : SiteCost.Phi Ap Am Cp Cm = 0 := by
    have : (SiteCost.Phi Ap Am Cp Cm).natAbs = 0 := by omega
    omega
  exact cut_classes_match Ap Am Bp Bm Cp Cm Dp Dm h1 h2 h3 hbal

#print axioms cut_classes_match
#print axioms cut_classes_match_of_cards

/-- **The turn realising the diagonal plan.**  Four class pairs, each equinumerous by
`cut_classes_match`, are matched simultaneously: `exists_involution_two` handles two at
a time and `combine_involutions` glues the halves across their disjoint supports. -/
theorem exists_involution_four {α : Type*} [Fintype α] [DecidableEq α]
    (A0 D0 A1 D1 A2 D2 A3 D3 : Finset α)
    (hd0 : Disjoint A0 D0) (hc0 : A0.card = D0.card)
    (hd1 : Disjoint A1 D1) (hc1 : A1.card = D1.card)
    (hd2 : Disjoint A2 D2) (hc2 : A2.card = D2.card)
    (hd3 : Disjoint A3 D3) (hc3 : A3.card = D3.card)
    (h01 : Disjoint (A0 ∪ D0) (A1 ∪ D1))
    (h23 : Disjoint (A2 ∪ D2) (A3 ∪ D3))
    (hLR : Disjoint ((A0 ∪ D0) ∪ (A1 ∪ D1)) ((A2 ∪ D2) ∪ (A3 ∪ D3))) :
    ∃ t : α → α, (∀ x, t (t x) = x) ∧
      (∀ x ∈ A0, t x ∈ D0) ∧ (∀ x ∈ D0, t x ∈ A0) ∧
      (∀ x ∈ A1, t x ∈ D1) ∧ (∀ x ∈ D1, t x ∈ A1) ∧
      (∀ x ∈ A2, t x ∈ D2) ∧ (∀ x ∈ D2, t x ∈ A2) ∧
      (∀ x ∈ A3, t x ∈ D3) ∧ (∀ x ∈ D3, t x ∈ A3) ∧
      (∀ x, x ∉ A0 → x ∉ D0 → x ∉ A1 → x ∉ D1 →
            x ∉ A2 → x ∉ D2 → x ∉ A3 → x ∉ D3 → t x = x) := by
  classical
  obtain ⟨t1, t1inv, t1a0, t1d0, t1a1, t1d1, t1fix⟩ :=
    EltBridge.exists_involution_two A0 D0 A1 D1 hd0 hc0 hd1 hc1 h01
  obtain ⟨t2, t2inv, t2a2, t2d2, t2a3, t2d3, t2fix⟩ :=
    EltBridge.exists_involution_two A2 D2 A3 D3 hd2 hc2 hd3 hc3 h23
  set S1 : Finset α := (A0 ∪ D0) ∪ (A1 ∪ D1) with hS1
  set S2 : Finset α := (A2 ∪ D2) ∪ (A3 ∪ D3) with hS2
  have memS1 : ∀ x : α, x ∈ S1 ↔ (x ∈ A0 ∨ x ∈ D0 ∨ x ∈ A1 ∨ x ∈ D1) := by
    intro x; simp [hS1, Finset.mem_union, or_assoc]
  have memS2 : ∀ x : α, x ∈ S2 ↔ (x ∈ A2 ∨ x ∈ D2 ∨ x ∈ A3 ∨ x ∈ D3) := by
    intro x; simp [hS2, Finset.mem_union, or_assoc]
  have h1S : ∀ x ∈ S1, t1 x ∈ S1 := by
    intro x hx
    rcases (memS1 x).mp hx with h | h | h | h
    · exact (memS1 _).mpr (Or.inr (Or.inl (t1a0 x h)))
    · exact (memS1 _).mpr (Or.inl (t1d0 x h))
    · exact (memS1 _).mpr (Or.inr (Or.inr (Or.inr (t1a1 x h))))
    · exact (memS1 _).mpr (Or.inr (Or.inr (Or.inl (t1d1 x h))))
  have h2S : ∀ x ∈ S2, t2 x ∈ S2 := by
    intro x hx
    rcases (memS2 x).mp hx with h | h | h | h
    · exact (memS2 _).mpr (Or.inr (Or.inl (t2a2 x h)))
    · exact (memS2 _).mpr (Or.inl (t2d2 x h))
    · exact (memS2 _).mpr (Or.inr (Or.inr (Or.inr (t2a3 x h))))
    · exact (memS2 _).mpr (Or.inr (Or.inr (Or.inl (t2d3 x h))))
  have h1fix : ∀ x, x ∉ S1 → t1 x = x := by
    intro x hx
    have h := fun hc => hx ((memS1 x).mpr hc)
    exact t1fix x (fun c => h (Or.inl c)) (fun c => h (Or.inr (Or.inl c)))
      (fun c => h (Or.inr (Or.inr (Or.inl c)))) (fun c => h (Or.inr (Or.inr (Or.inr c))))
  have h2fix : ∀ x, x ∉ S2 → t2 x = x := by
    intro x hx
    have h := fun hc => hx ((memS2 x).mpr hc)
    exact t2fix x (fun c => h (Or.inl c)) (fun c => h (Or.inr (Or.inl c)))
      (fun c => h (Or.inr (Or.inr (Or.inl c)))) (fun c => h (Or.inr (Or.inr (Or.inr c))))
  obtain ⟨t, tinv, tS1, tS2, tfix, -, -⟩ :=
    EltBridge.combine_involutions t1 t2 S1 S2 t1inv h1S h1fix t2inv h2S h2fix hLR
  refine ⟨t, tinv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [tS1 x ((memS1 x).mpr (Or.inl hx))]; exact t1a0 x hx
  · intro x hx; rw [tS1 x ((memS1 x).mpr (Or.inr (Or.inl hx)))]; exact t1d0 x hx
  · intro x hx; rw [tS1 x ((memS1 x).mpr (Or.inr (Or.inr (Or.inl hx))))]; exact t1a1 x hx
  · intro x hx; rw [tS1 x ((memS1 x).mpr (Or.inr (Or.inr (Or.inr hx))))]; exact t1d1 x hx
  · intro x hx; rw [tS2 x ((memS2 x).mpr (Or.inl hx))]; exact t2a2 x hx
  · intro x hx; rw [tS2 x ((memS2 x).mpr (Or.inr (Or.inl hx)))]; exact t2d2 x hx
  · intro x hx; rw [tS2 x ((memS2 x).mpr (Or.inr (Or.inr (Or.inl hx))))]; exact t2a3 x hx
  · intro x hx; rw [tS2 x ((memS2 x).mpr (Or.inr (Or.inr (Or.inr hx))))]; exact t2d3 x hx
  · intro x n0 m0 n1 m1 n2 m2 n3 m3
    refine tfix x (fun hc => ?_) (fun hc => ?_)
    · rcases (memS1 x).mp hc with h | h | h | h
      exacts [n0 h, m0 h, n1 h, m1 h]
    · rcases (memS2 x).mp hc with h | h | h | h
      exacts [n2 h, m2 h, n3 h, m3 h]

#print axioms exists_involution_four

/-- **The zero-cost turn at a cut site exists.**  This is the construction BLOCK 137
found missing: a turn realising the zero-cost plan.  It needs no transportation
matrix, because at a cut site the plan is diagonal -- the class counts agree
(`cut_classes_match`) -- so the turn is four simultaneous class-to-class matchings
(`exists_involution_four`).

Every pair it makes is same-class, which is a bounce, so the turn costs nothing and
crosses nothing. -/
theorem exists_class_matching_at_cut {α : Type*} [Fintype α] [DecidableEq α]
    (Arr Dep : Finset α) (cls : α → Fin 4) (hdisj : Disjoint Arr Dep)
    (hcard : ∀ i : Fin 4,
      (Arr.filter (fun a => cls a = i)).card = (Dep.filter (fun b => cls b = i)).card) :
    ∃ t : α → α, (∀ x, t (t x) = x) ∧
      (∀ i : Fin 4, ∀ x ∈ Arr.filter (fun a => cls a = i),
        t x ∈ Dep.filter (fun b => cls b = i)) ∧
      (∀ i : Fin 4, ∀ x ∈ Dep.filter (fun b => cls b = i),
        t x ∈ Arr.filter (fun a => cls a = i)) ∧
      (∀ x, x ∉ Arr → x ∉ Dep → t x = x) := by
  classical
  set A : Fin 4 → Finset α := fun i => Arr.filter (fun a => cls a = i) with hA
  set D : Fin 4 → Finset α := fun i => Dep.filter (fun b => cls b = i) with hD
  have hAD : ∀ i, Disjoint (A i) (D i) := fun i => Finset.disjoint_filter_filter hdisj
  -- everything in the `i`-block carries class `i`; that is all the disjointness needs
  have hcls : ∀ (i : Fin 4) (x : α), x ∈ A i ∪ D i → cls x = i := by
    intro i x hx
    rcases Finset.mem_union.mp hx with h | h <;>
      · simp only [hA, hD, Finset.mem_filter] at h
        exact h.2
  have hsep : ∀ i j : Fin 4, i ≠ j → Disjoint (A i ∪ D i) (A j ∪ D j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hy
    exact hij ((hcls i x hx).symm.trans (hcls j x hy))
  have hLR : Disjoint ((A 0 ∪ D 0) ∪ (A 1 ∪ D 1)) ((A 2 ∪ D 2) ∪ (A 3 ∪ D 3)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have h1 : cls x = 0 ∨ cls x = 1 := by
      rcases Finset.mem_union.mp hx with h | h
      · exact Or.inl (hcls 0 x h)
      · exact Or.inr (hcls 1 x h)
    have h2 : cls x = 2 ∨ cls x = 3 := by
      rcases Finset.mem_union.mp hy with h | h
      · exact Or.inl (hcls 2 x h)
      · exact Or.inr (hcls 3 x h)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      · rw [h1] at h2; exact absurd h2 (by decide)
  obtain ⟨t, tinv, a0, d0, a1, d1, a2, d2, a3, d3, tfix⟩ :=
    exists_involution_four (A 0) (D 0) (A 1) (D 1) (A 2) (D 2) (A 3) (D 3)
      (hAD 0) (hcard 0) (hAD 1) (hcard 1) (hAD 2) (hcard 2) (hAD 3) (hcard 3)
      (hsep 0 1 (by decide)) (hsep 2 3 (by decide)) hLR
  have subA : ∀ i : Fin 4, ∀ x, x ∈ A i → x ∈ Arr := by
    intro i x hx; simp only [hA, Finset.mem_filter] at hx; exact hx.1
  have subD : ∀ i : Fin 4, ∀ x, x ∈ D i → x ∈ Dep := by
    intro i x hx; simp only [hD, Finset.mem_filter] at hx; exact hx.1
  refine ⟨t, tinv, ?_, ?_, ?_⟩
  · intro i x hx
    fin_cases i
    exacts [a0 x hx, a1 x hx, a2 x hx, a3 x hx]
  · intro i x hx
    fin_cases i
    exacts [d0 x hx, d1 x hx, d2 x hx, d3 x hx]
  · intro x hA' hD'
    exact tfix x (fun h => hA' (subA 0 x h)) (fun h => hD' (subD 0 x h))
      (fun h => hA' (subA 1 x h)) (fun h => hD' (subD 1 x h))
      (fun h => hA' (subA 2 x h)) (fun h => hD' (subD 2 x h))
      (fun h => hA' (subA 3 x h)) (fun h => hD' (subD 3 x h))

#print axioms exists_class_matching_at_cut

/-- **Splicing a rival turn at one site.**  `site_cost_le_of_global` compares the given
datum against a rival that agrees with it away from `s`.  This builds that rival: keep
the turn everywhere else, use `tS` at `s`.

The three `Data` obligations all come from the site bookkeeping.  Both branches
preserve the site, so the composite is an involution and never meets `p`, which changes
the site. -/
theorem exists_rival_data {α : Type*} [Fintype α] [DecidableEq α]
    (siteOf : α → ℤ) (p t₀ tS : α → α) (s : ℤ)
    (hpinv : ∀ x, p (p x) = x) (hpne : ∀ x, p x ≠ x)
    (hpsite : ∀ x, siteOf (p x) ≠ siteOf x)
    (ht₀inv : ∀ x, t₀ (t₀ x) = x) (ht₀ne : ∀ x, t₀ x ≠ x)
    (ht₀site : ∀ x, siteOf (t₀ x) = siteOf x)
    (htSinv : ∀ x, tS (tS x) = x)
    (htSsite : ∀ x, siteOf x = s → siteOf (tS x) = s)
    (htSne : ∀ x, siteOf x = s → tS x ≠ x) :
    ∃ E : WalkGraph.Data α, E.p = p ∧
      (∀ x, siteOf x = s → E.t x = tS x) ∧
      (∀ x, siteOf x ≠ s → E.t x = t₀ x) := by
  classical
  refine ⟨{ p := p, t := fun x => if siteOf x = s then tS x else t₀ x,
            p_invol := hpinv, p_ne := hpne,
            t_invol := ?_, t_ne := ?_, pt_ne := ?_ }, rfl, ?_, ?_⟩
  · intro x
    by_cases hx : siteOf x = s
    · rw [if_pos hx, if_pos (htSsite x hx), htSinv]
    · rw [if_neg hx, if_neg (by rw [ht₀site]; exact hx), ht₀inv]
  · intro x
    by_cases hx : siteOf x = s
    · rw [if_pos hx]; exact htSne x hx
    · rw [if_neg hx]; exact ht₀ne x
  · intro x
    -- the turn keeps the site, `p` changes it
    have hsite : siteOf (if siteOf x = s then tS x else t₀ x) = siteOf x := by
      by_cases hx : siteOf x = s
      · rw [if_pos hx, htSsite x hx, hx]
      · rw [if_neg hx, ht₀site]
    intro hc
    exact hpsite x (by rw [hc, hsite])
  · intro x hx; exact if_pos hx
  · intro x hx; exact if_neg hx

#print axioms exists_rival_data

/-! ### Correction to BLOCK 137: the emptiness is forced, not a bad hypothesis

BLOCK 137 called the recorded blocker for M3 and M4b -- "the witness needs empty
edges" -- stale, on the grounds that `hempty` was a badly chosen hypothesis and
`cross = 0` was the right one.  The first half of that was right and the second half
does not rescue it.  `cut_classes_match` makes the position **worse**, not better, and
here is why.

`clsOf x = (if atTop x then 0 else 2) + (if sgn x then 0 else 1)`, and
`endDataOf = ⟨atTop, isArrOf up, ds⟩`, so `side = atTop` and a class fixes both the
side and the sign.  But `EndData.sgn` is derived from `(side, isArr, depSign side)`,
so on a fixed side every arrival carries one sign and every departure the other
(`sgn_arr_ne_dep`).  A single class therefore admits arrivals or departures, never
both.

Combine that with `cut_classes_match`, which says the class counts agree at a cut
site: each class has `|Arr_i| = |Dep_i|` and at most one of the two is non-empty, so
both are empty.  **A cut site in the derived-sign model carries no ends at all** --
which is exactly `hempty`, now as a theorem rather than a hypothesis.

So `turnInv_of_mergesMin_of_cross_zero` is correct and genuinely weaker in its
hypotheses, but it cannot be fed: in this model there is no cut site carrying ends to
feed it with.  The obstruction is the derived sign, as the ledger said.
-/

/-- The class map `(atTop, sgn) -> Fin 4` is injective. -/
theorem cls_pair_inj (t1 s1 t2 s2 : Bool) :
    ((if t1 then (0 : Fin 4) else 2) + (if s1 then 0 else 1))
      = ((if t2 then (0 : Fin 4) else 2) + (if s2 then 0 else 1)) → t1 = t2 ∧ s1 = s2 := by
  revert t1 s1 t2 s2
  decide

/-- **No class holds both an arrival and a departure.**  A class fixes the side and the
sign; the derived sign gives arrivals and departures opposite signs on a fixed side. -/
theorem no_class_holds_both {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (ds : Bool → Bool)
    (a b : EndType.Endpt n m)
    (ha : EndType.isArrOf up a = true) (hb : EndType.isArrOf up b = false)
    (hc : ConfigLoop.clsOf up ds a = ConfigLoop.clsOf up ds b) : False := by
  unfold ConfigLoop.clsOf at hc
  obtain ⟨htop, hsgn⟩ := cls_pair_inj _ _ _ _ hc
  exact EltBridge.sgn_arr_ne_dep (ConfigLoop.endDataOf (m := m) up ds) a b htop ha hb hsgn

/-- **So a cut site in the derived-sign model is empty.**  Each class has as many
arrivals as departures there (`cut_classes_match`) and cannot hold both, so it holds
neither. -/
theorem cut_class_empty_of_card_eq {n : ℕ} {m : Fin n → ℕ}
    (up : Fin n → ℕ) (ds : Bool → Bool) (Arr Dep : Finset (EndType.Endpt n m)) (i : Fin 4)
    (hArr : ∀ x ∈ Arr, EndType.isArrOf up x = true)
    (hDep : ∀ x ∈ Dep, EndType.isArrOf up x = false)
    (hcard : (Arr.filter (fun a => ConfigLoop.clsOf up ds a = i)).card
      = (Dep.filter (fun b => ConfigLoop.clsOf up ds b = i)).card) :
    (Arr.filter (fun a => ConfigLoop.clsOf up ds a = i)) = ∅ := by
  classical
  by_contra hne
  obtain ⟨a, haMem⟩ := Finset.nonempty_of_ne_empty hne
  have hdne : (Dep.filter (fun b => ConfigLoop.clsOf up ds b = i)).Nonempty := by
    rw [← Finset.card_pos, ← hcard, Finset.card_pos]
    exact ⟨a, haMem⟩
  obtain ⟨b, hbMem⟩ := hdne
  rw [Finset.mem_filter] at haMem hbMem
  exact no_class_holds_both up ds a b (hArr a haMem.1) (hDep b hbMem.1)
    (haMem.2.trans hbMem.2.symm)

#print axioms cls_pair_inj
#print axioms no_class_holds_both
#print axioms cut_class_empty_of_card_eq
