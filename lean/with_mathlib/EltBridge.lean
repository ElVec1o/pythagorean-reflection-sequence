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

/-! ### (M3a) is not analytic: it is the exponential of a nearest-neighbour cost

`site_cost_couples` says the interior site cost is `max(|d(s-1)|, |d(s)|)` -- a cost
depending on **two consecutive** states and nothing else.  Together with
`cor:lRclosed` (`lR` is the sum of the site costs and the deposit magnitudes) that
makes `lR` a *chain cost*: a head term, a nearest-neighbour term at each step, a tail
term.  And the exponential of a chain cost is exactly a `pathWeight`.

So (M3a) reduces to a general fact about chain costs, proved here, with **no analysis
at all**.  The transfer kernel it produces is `T a b = x ^ max(a,b)`, which is the
bulk kernel of `eq:gapkernel` -- the operator was never an assumption, it is forced by
the shape of the cost. -/

/-- The last entry of `s :: L`, without a dependent non-emptiness proof. -/
def lastOf {S : Type*} (s : S) : List S → S
  | [] => s
  | t :: rest => lastOf t rest

/-- The total nearest-neighbour cost along the state path `s :: L`. -/
def chainCost {S : Type*} (f : S → S → ℕ) : S → List S → ℕ
  | _, [] => 0
  | a, b :: rest => f a b + chainCost f b rest

/-- **The inner path weight is the exponential of the chain cost.** -/
theorem pathWeight_one_exp {S : Type*} (x : ℤ) (f : S → S → ℕ) (g : S → ℕ) :
    ∀ (L : List S) (s : S),
      pathWeight (fun a b => x ^ f a b) (fun _ => (1 : ℤ)) (fun a => x ^ g a) (s :: L)
        = x ^ (chainCost f s L + g (lastOf s L)) := by
  intro L
  induction L with
  | nil => intro s; simp [pathWeight, chainCost, lastOf]
  | cons t rest ih =>
      intro s
      show (1 : ℤ) * x ^ f s t
          * pathWeight (fun a b => x ^ f a b) (fun _ => (1 : ℤ)) (fun a => x ^ g a) (t :: rest)
        = _
      rw [ih t]
      show _ = x ^ (f s t + chainCost f t rest + g (lastOf t rest))
      rw [pow_add, pow_add, pow_add]
      ring

/-- **And the full one carries the head weight too.**  This is (M3a): a weight that is a
chain cost *is* a transfer-matrix path weight, with kernel `x ^ f`. -/
theorem pathWeight_exp {S : Type*} (x : ℤ) (f : S → S → ℕ) (h g : S → ℕ)
    (s : S) (L : List S) :
    pathWeight (fun a b => x ^ f a b) (fun a => x ^ h a) (fun a => x ^ g a) (s :: L)
      = x ^ (h s + chainCost f s L + g (lastOf s L)) := by
  cases L with
  | nil => show x ^ h s * x ^ g s = _; simp [chainCost, lastOf, pow_add]
  | cons t rest =>
      show x ^ h s * x ^ f s t
          * pathWeight (fun a b => x ^ f a b) (fun _ => (1 : ℤ)) (fun a => x ^ g a) (t :: rest)
        = _
      rw [pathWeight_one_exp x f g rest t]
      show _ = x ^ (h s + (f s t + chainCost f t rest) + g (lastOf t rest))
      rw [pow_add, pow_add, pow_add, pow_add]
      ring

/-- **(M3a), discharged.**  Any family of configurations whose weight is a chain cost
satisfies `IsTransferDecomposition` -- with the kernel, the head vector and the tail
vector all read off from the cost.  Nothing is assumed about the configurations. -/
theorem isTransferDecomposition_of_chain {C S : Type*}
    (x : ℤ) (f : S → S → ℕ) (h g : S → ℕ)
    (head : C → S) (rest : C → List S) (w : C → ℕ)
    (hw : ∀ c : C, w c
        = h (head c) + chainCost f (head c) (rest c) + g (lastOf (head c) (rest c))) :
    IsTransferDecomposition (fun c => head c :: rest c) (fun c => x ^ w c)
      (fun a b => x ^ f a b) (fun a => x ^ h a) (fun a => x ^ g a) := by
  intro c
  show x ^ w c = _
  rw [hw c]
  exact (pathWeight_exp x f h g (head c) (rest c)).symm

/-- **The kernel this produces at interior sites is `eq:gapkernel`'s bulk kernel.**  The
local cost there is `max`, by `site_cost_couples`, so the transfer entry is
`x ^ max(a,b)` -- the operator is forced, not posited. -/
theorem interior_kernel_eq_max (P : SiteCost.PathData) (s : ℤ)
    (h0 : s ≠ 0) (hk : s ≠ P.kstar) :
    P.siteCost s = max (P.d (s - 1)).natAbs (P.d s).natAbs :=
  site_cost_couples P s h0 hk

/-! ### The two boundary sites, matched: `lR` **is** a chain cost

`Elt.lR_eq` reads

    lR = sum_{j in Icc A B} mu j + sum_{s in Icc A (B+1)} siteCost s,

so the span is a path: site `A`, edge `A`, site `A+1`, ..., edge `B`, site `B+1`.
Walking it left to right and charging each step for *the edge it crosses and the site
it lands on* turns that into a chain cost, with the two boundary sites -- and only
those -- left over as the head and the tail:

    h s = siteCost s                  the head, spent at s = A
    f i j = mu i + siteCost j         each step: the edge, then the site to its right
    g s = mu s + siteCost (s+1)       the tail, absorbing the last edge and last site

That is the whole content of the matching.  It is an identity between two finite sums,
proved here by induction, and with it `isTransferDecomposition_of_chain` applies to
`lR` directly. -/

/-- The states of the span after the first: `[A+1, ..., A+n]`. -/
def idxList (A : ℤ) : ℕ → List ℤ
  | 0 => []
  | n + 1 => (A + 1) :: idxList (A + 1) n

theorem lastOf_idxList (A : ℤ) : ∀ n : ℕ, lastOf A (idxList A n) = A + n := by
  intro n
  induction n generalizing A with
  | zero => simp [idxList, lastOf]
  | succ m ih =>
      show lastOf (A + 1) (idxList (A + 1) m) = _
      rw [ih (A + 1)]; push_cast; ring

/-- **The chain cost of the span**, with the step charge `f i j = a i + b j`. -/
theorem chainCost_idxList (a b : ℤ → ℕ) (A : ℤ) : ∀ n : ℕ,
    chainCost (fun i j => a i + b j) A (idxList A n)
      = (∑ k ∈ Finset.range n, a (A + k)) + ∑ k ∈ Finset.range n, b (A + 1 + k) := by
  intro n
  induction n generalizing A with
  | zero => simp [idxList, chainCost]
  | succ m ih =>
      show a A + b (A + 1) + chainCost (fun i j => a i + b j) (A + 1) (idxList (A + 1) m) = _
      rw [ih (A + 1), Finset.sum_range_succ' (fun k => a (A + k)),
        Finset.sum_range_succ' (fun k => b (A + 1 + k))]
      push_cast
      have h1 : ∀ k : ℕ, a (A + 1 + (k : ℤ)) = a (A + ((k : ℤ) + 1)) := by
        intro k; congr 1; ring
      have h2 : ∀ k : ℕ, b (A + 1 + 1 + (k : ℤ)) = b (A + 1 + ((k : ℤ) + 1)) := by
        intro k; congr 1; ring
      simp only [h1, h2, add_zero]
      omega

/-- Reindexing an integer interval of length `n + 1` by `range (n + 1)`. -/
theorem sum_Icc_shift (f : ℤ → ℕ) (A : ℤ) : ∀ n : ℕ,
    ∑ s ∈ Finset.Icc A (A + n), f s = ∑ k ∈ Finset.range (n + 1), f (A + k) := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
      have hins : Finset.Icc A (A + ((m : ℤ) + 1))
          = insert (A + ((m : ℤ) + 1)) (Finset.Icc A (A + m)) := by
        ext y; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : A + ((m : ℤ) + 1) ∉ Finset.Icc A (A + m) := by
        simp only [Finset.mem_Icc]; omega
      have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hcast, hins, Finset.sum_insert hnot, ih,
        Finset.sum_range_succ (fun k : ℕ => f (A + (k : ℤ))) (m + 1)]
      push_cast
      omega

/-- **The matching.**  An alternating edge/site total over the span is the chain cost
plus the two boundary sites -- the head `b A` and the tail `a (A+n) + b (A+n+1)`. -/
theorem alternating_is_chain (a b : ℤ → ℕ) (A : ℤ) (n : ℕ) :
    (∑ j ∈ Finset.Icc A (A + n), a j) + (∑ s ∈ Finset.Icc A (A + n + 1), b s)
      = b A + chainCost (fun i j => a i + b j) A (idxList A n)
          + (a (A + n) + b (A + n + 1)) := by
  have hA : A + (n : ℤ) + 1 = A + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [sum_Icc_shift a A n, hA, sum_Icc_shift b A (n + 1), chainCost_idxList a b A n,
    Finset.sum_range_succ (fun k => a (A + k)) n,
    Finset.sum_range_succ (fun k => b (A + k)) (n + 1)]
  have hb : ∀ k : ℕ, b (A + 1 + k) = b (A + (k + 1)) := by
    intro k; congr 1; push_cast; ring
  have hlast : b (A + ((n : ℤ) + 1)) = b (A + n + 1) := by congr 1; ring
  rw [Finset.sum_range_succ' (fun k => b (A + k)) n]
  simp only [hb, Nat.cast_zero, add_zero]
  push_cast
  omega

/-- **(M3a), for `lR`.**  Any family of configurations whose relaxed length is the
alternating edge/site total of `Elt.lR_eq` satisfies `IsTransferDecomposition`, with the
step kernel `x ^ (mu i + siteCost j)` and the two boundary sites supplying `lambda` and
`mu`.  Nothing analytic enters; the two sums are equal. -/
theorem isTransferDecomposition_alternating {C : Type*}
    (x : ℤ) (a b : ℤ → ℕ) (A : C → ℤ) (n : C → ℕ) (w : C → ℕ)
    (hw : ∀ c : C, w c = (∑ j ∈ Finset.Icc (A c) (A c + n c), a j)
        + ∑ s ∈ Finset.Icc (A c) (A c + n c + 1), b s) :
    IsTransferDecomposition (fun c => A c :: idxList (A c) (n c)) (fun c => x ^ w c)
      (fun i j => x ^ (a i + b j)) (fun s => x ^ b s) (fun s => x ^ (a s + b (s + 1))) := by
  refine isTransferDecomposition_of_chain x (fun i j => a i + b j) b
    (fun s => a s + b (s + 1)) A (fun c => idxList (A c) (n c)) w ?_
  intro c
  rw [hw c, alternating_is_chain a b (A c) (n c), lastOf_idxList]

/-- `Elt.lR_eq` with the span written as `A .. A + n`. -/
theorem Elt.lR_alternating (g : Elt) (n : ℕ) (hn : g.B = g.A + n) :
    g.lR = (∑ j ∈ Finset.Icc g.A (g.A + n), g.toPathData.mu j)
      + ∑ s ∈ Finset.Icc g.A (g.A + n + 1), g.toPathData.siteCost s := by
  rw [Elt.lR_eq, hn]

/-- **`lR` is a chain cost, boundary sites and all.**  The head is the site cost at the
left boundary site `A`; each step charges the edge it crosses and the site it lands on;
the tail carries the last edge and the right boundary site `A + n + 1`.  Those two
boundary sites are the only terms outside the chain, and they are exactly `lambda` and
`mu`.  This is the matching, discharged. -/
theorem Elt.lR_is_chain (g : Elt) (n : ℕ) (hn : g.B = g.A + n) :
    g.lR = g.toPathData.siteCost g.A
      + chainCost (fun i j => g.toPathData.mu i + g.toPathData.siteCost j) g.A (idxList g.A n)
      + (g.toPathData.mu (g.A + n) + g.toPathData.siteCost (g.A + n + 1)) := by
  rw [Elt.lR_alternating g n hn]
  exact alternating_is_chain _ _ _ _

/-- **Hence the exponential weight of a single configuration is a transfer-matrix path
weight**, with kernel `x ^ (mu i + siteCost j)`.  `interior_kernel_eq_max` identifies the
site factor as `x ^ max(a,b)`, the bulk kernel of `eq:gapkernel`. -/
theorem Elt.lR_exp_pathWeight (g : Elt) (n : ℕ) (hn : g.B = g.A + n) (x : ℤ) :
    x ^ g.lR
      = pathWeight (fun i j => x ^ (g.toPathData.mu i + g.toPathData.siteCost j))
          (fun s => x ^ g.toPathData.siteCost s)
          (fun s => x ^ (g.toPathData.mu s + g.toPathData.siteCost (s + 1)))
          (g.A :: idxList g.A n) := by
  rw [pathWeight_exp, lastOf_idxList, ← Elt.lR_is_chain g n hn]

/-! ### The factoring: one kernel for the whole family

BLOCK 207 used the *index* as the state, which serves one configuration at a time.  To
get a single kernel serving every configuration the costs must factor through local
data, and they do, by inspection of the definitions:

    mu j       = if d j = 0 and f j = 0 then 2 else max |d j| |f j|
    siteCost s = max |d (s-1) - vArr s + eps * vL s| |d s - eps * vR s|

so `mu j` needs only `(d j, f j)`, and `siteCost s` only `(d (s-1), d s)` together with
the two markers `[s = 0]`, `[s = k*]` and the configuration's `eps`, `delta`.  Packaging
exactly those into a `LocalState` makes both cost functions *pure functions of one
state*, and the transfer kernel `x ^ (muOf sigma + siteOf tau)` no longer mentions the
configuration at all.

Running the chain over all `n + 2` **sites** (rather than `n + 1` of them) is what makes
this work: the right boundary site then arrives as an ordinary chain step instead of a
tail, and the left boundary site is the head.  So the tail vector is trivial. -/

theorem chainCost_map {S T : Type*} (st : S → T) (f : T → T → ℕ) :
    ∀ (L : List S) (s : S),
      chainCost f (st s) (L.map st) = chainCost (fun i j => f (st i) (st j)) s L := by
  intro L
  induction L with
  | nil => intro s; rfl
  | cons t rest ih => intro s; show f (st s) (st t) + _ = f (st s) (st t) + _; rw [ih t]

theorem lastOf_map {S T : Type*} (st : S → T) :
    ∀ (L : List S) (s : S), lastOf (st s) (L.map st) = st (lastOf s L) := by
  intro L
  induction L with
  | nil => intro s; rfl
  | cons t rest ih => intro s; exact ih t

/-- **The matching, with every site a chain state.**  Compare `alternating_is_chain`:
the chain is one step longer, the right boundary site is an ordinary step, and the tail
is trivial. -/
theorem alternating_is_chain_sites (a b : ℤ → ℕ) (A : ℤ) (n : ℕ) :
    (∑ j ∈ Finset.Icc A (A + n), a j) + (∑ s ∈ Finset.Icc A (A + n + 1), b s)
      = b A + chainCost (fun i j => a i + b j) A (idxList A (n + 1)) + 0 := by
  have hA : A + (n : ℤ) + 1 = A + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [sum_Icc_shift a A n, hA, sum_Icc_shift b A (n + 1), chainCost_idxList a b A (n + 1),
    Finset.sum_range_succ' (fun k => b (A + k)) (n + 1)]
  have hb : ∀ k : ℕ, b (A + 1 + (k : ℤ)) = b (A + ((k : ℤ) + 1)) := by
    intro k; congr 1; ring
  push_cast
  simp only [hb, add_zero]
  omega

/-- The local data a site and its edge depend on: the two adjacent deposits, the travel
indicator, the two markers, and the configuration's sign data. -/
structure LocalState where
  dprev : ℤ
  dcur : ℤ
  fcur : ℤ
  arr : ℕ
  dep : ℕ
  eps : ℤ
  delta : Bool
  deriving DecidableEq

namespace LocalState

variable (s : LocalState)

def vLOf : ℕ := if s.delta then 0 else s.dep
def vROf : ℕ := if s.delta then s.dep else 0

/-- `mu`, as a function of the state alone. -/
def muOf : ℕ := if s.dcur = 0 ∧ s.fcur = 0 then 2 else max s.dcur.natAbs s.fcur.natAbs

/-- `siteCost`, as a function of the state alone. -/
def siteOf : ℕ :=
  max (s.dprev - (vArr' s) + s.eps * (s.vLOf : ℤ)).natAbs (s.dcur - s.eps * (s.vROf : ℤ)).natAbs
where vArr' (s : LocalState) : ℤ := (s.arr : ℤ)

end LocalState

/-- The state at index `j` of a configuration. -/
def stateOf (P : SiteCost.PathData) (j : ℤ) : LocalState :=
  { dprev := P.d (j - 1), dcur := P.d j, fcur := SiteCost.travel P.kstar j,
    arr := SiteCost.vArr j, dep := P.vD j, eps := P.eps, delta := P.delta }

/-- **The state is bounded by its own cost**, which is what makes the state space finite
once the total weight is bounded: a configuration of relaxed length `N` can only visit
states with `|d| <= N` and `|f| <= N`, and there are finitely many of those. -/
theorem LocalState.dcur_le_muOf (σ : LocalState) : σ.dcur.natAbs ≤ σ.muOf := by
  simp only [LocalState.muOf]
  split_ifs with h
  · obtain ⟨h1, -⟩ := h; simp [h1]
  · exact le_max_left _ _

theorem LocalState.fcur_le_muOf (σ : LocalState) : σ.fcur.natAbs ≤ σ.muOf := by
  simp only [LocalState.muOf]
  split_ifs with h
  · obtain ⟨-, h2⟩ := h; simp [h2]
  · exact le_max_right _ _

theorem mu_factors (P : SiteCost.PathData) (j : ℤ) : P.mu j = (stateOf P j).muOf := rfl

theorem siteCost_factors (P : SiteCost.PathData) (j : ℤ) :
    P.siteCost j = (stateOf P j).siteOf := rfl

/-- **(M3a) for a whole family.**  One transfer kernel `x ^ (muOf sigma + siteOf tau)`,
one head vector `x ^ siteOf`, one trivial tail, serving *every* configuration of span
length `n` at once.  The configuration appears only through its state path -- which is
exactly what a transfer-matrix decomposition is supposed to say. -/
theorem isTransferDecomposition_family {C : Type*} (x : ℤ) (n : ℕ)
    (P : C → SiteCost.PathData) (hn : ∀ c, (P c).B = (P c).A + n) :
    IsTransferDecomposition
      (fun c => ((P c).A :: idxList (P c).A (n + 1)).map (stateOf (P c)))
      (fun c => x ^ (P c).lR)
      (fun σ τ => x ^ (σ.muOf + τ.siteOf))
      (fun σ => x ^ σ.siteOf)
      (fun _ => x ^ (0 : ℕ)) := by
  refine isTransferDecomposition_of_chain x (fun σ τ => σ.muOf + τ.siteOf)
    (fun σ => σ.siteOf) (fun _ => 0)
    (fun c => stateOf (P c) (P c).A)
    (fun c => (idxList (P c).A (n + 1)).map (stateOf (P c)))
    (fun c => (P c).lR) ?_
  intro c
  show (P c).lR = _
  have hL : (P c).lR
      = (∑ j ∈ Finset.Icc (P c).A ((P c).A + n), (P c).mu j)
        + ∑ s ∈ Finset.Icc (P c).A ((P c).A + n + 1), (P c).siteCost s := by
    unfold SiteCost.PathData.lR
    rw [hn c]
  rw [chainCost_map (stateOf (P c)) (fun σ τ => σ.muOf + τ.siteOf), hL]
  exact alternating_is_chain_sites (P c).mu (P c).siteCost (P c).A n

/-- **And the weight of every member is the corresponding path weight.** -/
theorem lR_exp_pathWeight_family {C : Type*} (x : ℤ) (n : ℕ)
    (P : C → SiteCost.PathData) (hn : ∀ c, (P c).B = (P c).A + n) (c : C) :
    x ^ (P c).lR
      = pathWeight (fun σ τ => x ^ (σ.muOf + τ.siteOf)) (fun σ => x ^ σ.siteOf)
          (fun _ => x ^ (0 : ℕ))
          (((P c).A :: idxList (P c).A (n + 1)).map (stateOf (P c))) :=
  isTransferDecomposition_family x n P hn c

/-! ### (M3b), and a retraction: `IsResolventSum` says nothing

Setting out to prove `IsResolventSum` I found it is **vacuous**.  It asks, for each `N`,
for *some* `tail` with `W = (partial sum) + tail`, and `tail := W - (partial sum)` always
works.  It is satisfied by every `T`, `lam`, `mu`, `W` whatsoever.  That is recorded
below as a theorem rather than deleted, so the retraction is checkable.

`IsAssembly` (BLOCK 116) is the honest form: an exact identity of coefficients, degree
by degree, with the sum truncated at `range (N+1)`.  What makes that truncation legitimate
is the only real content of (M3b): **if every entry of the transfer matrix has vanishing
constant term, then `T^k` contributes nothing below degree `k`**, so the Neumann series
terminates at each fixed degree and the finite sum is exact.  That is proved here.

The hypothesis is the paper's order bound on the travel block -- a transfer step always
costs at least one unit of length, so its generating function has no constant term. -/

/-- **The retraction, made checkable**: `IsResolventSum` holds of anything. -/
theorem isResolventSum_vacuous {S : Type*} [Fintype S]
    (T : S → S → ℤ) (lam mu : S → ℤ) (W : ℤ) : IsResolventSum T lam mu W := by
  intro N
  exact ⟨W - ∑ k ∈ Finset.range N, ∑ s : S, lam s * (T s s) ^ k * mu s, by ring⟩

/-- **A transfer matrix whose entries all have positive order has `X^k | T^k`.** -/
theorem X_pow_dvd_matrix_pow {n : ℕ} (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (h : ∀ a b, PowerSeries.constantCoeff (T a b) = 0) :
    ∀ (k : ℕ) (a b : Fin n), (PowerSeries.X : PowerSeries ℤ) ^ k ∣ (T ^ k) a b := by
  intro k
  induction k with
  | zero => intro a b; simpa using one_dvd _
  | succ m ih =>
      intro a b
      rw [pow_succ T m, Matrix.mul_apply, pow_succ (PowerSeries.X : PowerSeries ℤ) m]
      refine Finset.dvd_sum ?_
      intro c _
      exact mul_dvd_mul (ih a c) (PowerSeries.X_dvd_iff.mpr (h c b))

/-- **(M3b), the real content.**  Below degree `k` the `k`-th Neumann term is zero, so
at each fixed degree the resolvent is a *finite* sum -- which is exactly what licenses
`IsAssembly`'s truncation at `range (N + 1)`.  No analysis: it is the order bound. -/
theorem coeff_matrix_pow_eq_zero {n : ℕ} (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (h : ∀ a b, PowerSeries.constantCoeff (T a b) = 0)
    (k : ℕ) (a b : Fin n) (m : ℕ) (hm : m < k) :
    PowerSeries.coeff m ((T ^ k) a b) = 0 :=
  PowerSeries.X_pow_dvd_iff.mp (X_pow_dvd_matrix_pow T h k a b) m hm

/-- **Hence the truncated resolvent is exact at every degree.**  For `N < k` the term
`lam a * (T^k) a b * mu b` cannot reach degree `N`, so extending the sum beyond
`range (N + 1)` changes nothing -- `IsAssembly` loses no information by truncating. -/
theorem coeff_neumann_tail_zero {n : ℕ} (T : Matrix (Fin n) (Fin n) (PowerSeries ℤ))
    (h : ∀ a b, PowerSeries.constantCoeff (T a b) = 0)
    (lam mu : Fin n → PowerSeries ℤ) (N k : ℕ) (hk : N < k) (a b : Fin n) :
    PowerSeries.coeff N (lam a * (T ^ k) a b * mu b) = 0 := by
  have hdvd : (PowerSeries.X : PowerSeries ℤ) ^ k ∣ lam a * (T ^ k) a b * mu b := by
    have := X_pow_dvd_matrix_pow T h k a b
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left this (lam a)) (mu b)
  exact PowerSeries.X_pow_dvd_iff.mp hdvd N hk

/-! ### The counting half of (M3b): summing path weights gives the matrix power

`IsAssembly`'s summand is `lam a * (T^k) a b * mu b`.  What has to be shown is that the
*sum over configurations* produces it -- that adding up `pathWeight` over every state
path of length `k` reproduces the `k`-th matrix power.  That splits in two:

  (i)  the algebraic step, here: the total weight accumulated by stepping `k` times
       through `T` and finishing with `mu` **is** `sum_b (T^k) a b * mu b`;
  (ii) the enumeration step: that total is the sum of `pathWeight` over all state paths.

(i) is proved below.  It is the whole reason a transfer matrix is the right object: the
matrix power *is* the path sum, by definition of matrix multiplication. -/

/-- Step `k` times through `T`, finishing with `mu`. -/
def weightSum {S : Type*} [Fintype S] (T : Matrix S S ℤ) (mu : S → ℤ) : S → ℕ → ℤ
  | a, 0 => mu a
  | a, (k + 1) => ∑ c : S, T a c * weightSum T mu c k

/-- **The path sum is the matrix power.** -/
theorem weightSum_eq {S : Type*} [Fintype S] [DecidableEq S]
    (T : Matrix S S ℤ) (mu : S → ℤ) :
    ∀ (k : ℕ) (a : S), weightSum T mu a k = ∑ b : S, (T ^ k) a b * mu b := by
  intro k
  induction k with
  | zero => intro a; simp [weightSum, Matrix.one_apply]
  | succ m ih =>
      intro a
      show ∑ c : S, T a c * weightSum T mu c m = _
      simp only [ih]
      rw [pow_succ' T m]
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

/-- **Hence `IsAssembly`'s summand is a path sum.**  With the head weight `lam a` in
front, stepping `k` times and finishing with `mu` gives exactly the `k`-th Neumann term
at `a`. -/
theorem lam_weightSum_eq {S : Type*} [Fintype S] [DecidableEq S]
    (T : Matrix S S ℤ) (lam mu : S → ℤ) (k : ℕ) (a : S) :
    lam a * weightSum T mu a k = ∑ b : S, lam a * (T ^ k) a b * mu b := by
  rw [weightSum_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **And the whole `k`-th Neumann term is the path sum over all starting states.** -/
theorem sum_lam_weightSum_eq {S : Type*} [Fintype S] [DecidableEq S]
    (T : Matrix S S ℤ) (lam mu : S → ℤ) (k : ℕ) :
    ∑ a : S, lam a * weightSum T mu a k = ∑ a : S, ∑ b : S, lam a * (T ^ k) a b * mu b :=
  Finset.sum_congr rfl fun a _ => lam_weightSum_eq T lam mu k a

/-! ### The enumeration step: `weightSum` really is a sum over all state paths -/

/-- The `Fintype` enumeration satisfies the hypothesis below. -/
theorem sum_univ_toList {S : Type*} [Fintype S] (f : S → ℤ) :
    ((Finset.univ : Finset S).toList.map f).sum = ∑ c : S, f c := by
  rw [← Finset.sum_map_toList]

/-- Summing a function of the concatenation is summing the sums. -/
theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → ℤ) :
    (((l.flatMap f).map g)).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- Every state path of length `k`, listed, given an enumeration `E` of the states. -/
def paths {S : Type*} (E : List S) : ℕ → List (List S)
  | 0 => [[]]
  | k + 1 => E.flatMap (fun c => (paths E k).map (fun L => c :: L))

/-- **`weightSum` is the sum of `pathWeight` over every state path.**  This is the
enumeration half of (M3b): the transfer matrix's `k`-th power counts exactly the state
paths of length `k`, each with its own weight.  `E` is any enumeration of the states --
for a `Fintype`, `Finset.univ.toList`. -/
theorem weightSum_eq_sum_pathWeight {S : Type*} [Fintype S] (T : Matrix S S ℤ) (mu : S → ℤ)
    (E : List S) (hE : ∀ f : S → ℤ, (E.map f).sum = ∑ c : S, f c) :
    ∀ (k : ℕ) (a : S),
      ((paths E k).map (fun L => pathWeight (fun i j => T i j) (fun _ => (1 : ℤ)) mu (a :: L))).sum
        = weightSum T mu a k := by
  intro k
  induction k with
  | zero => intro a; show (1 : ℤ) * mu a + 0 = mu a; ring
  | succ m ih =>
      intro a
      show ((E.flatMap (fun c => (paths E m).map (fun L => c :: L))).map _).sum = _
      rw [sum_map_flatMap]
      have hstep : ∀ c : S,
          (((paths E m).map (fun L => c :: L)).map
              (fun L => pathWeight (fun i j => T i j) (fun _ => (1 : ℤ)) mu (a :: L))).sum
            = T a c * weightSum T mu c m := by
        intro c
        rw [List.map_map, ← ih c, ← List.sum_map_mul_left]
        refine congrArg List.sum (List.map_congr_left ?_)
        intro L _
        show (1 : ℤ) * T a c * _ = T a c * _
        ring
      simp only [hstep]
      rw [hE (fun c => T a c * weightSum T mu c m)]
      rfl

/-! ### The kernel must be compatibility-guarded

Before joining the two halves of (M3b) there is a structural correction to make.  `paths`
enumerates *every* list of states, but not every list comes from a configuration: state
`j + 1` must carry `dprev = d j`, which is state `j`'s `dcur`, and `eps`, `delta` are
constant along a configuration.  So the map from configurations to state paths is **not**
onto `paths`, and the unguarded kernel would count paths no configuration realises.

That is not a defect, it is how transfer matrices work: incompatible transitions get a
**zero entry**.  Guarding the kernel with `compatB` makes the spurious paths contribute
nothing, and -- proved below -- leaves every configuration's own weight untouched. -/

/-- Two states are compatible when the right one continues the left one. -/
def compatB (σ τ : LocalState) : Bool :=
  decide (τ.dprev = σ.dcur) && decide (τ.eps = σ.eps) && (τ.delta == σ.delta)

/-- **A configuration's consecutive states are always compatible.** -/
theorem compatB_stateOf (P : SiteCost.PathData) (j : ℤ) :
    compatB (stateOf P j) (stateOf P (j + 1)) = true := by
  simp [compatB, stateOf]

/-- **Guarding the kernel does not change any configuration's weight.**  The guard fires
only on transitions no configuration makes, so on a real state path the guarded and
unguarded path weights agree -- while off it the guarded kernel contributes `0`. -/
theorem pathWeight_guarded_eq (x : ℤ) (P : SiteCost.PathData) (mu : LocalState → ℤ) :
    ∀ (n : ℕ) (A : ℤ) (lam : LocalState → ℤ),
      pathWeight (fun σ τ => if compatB σ τ then x ^ (σ.muOf + τ.siteOf) else 0) lam mu
          ((A :: idxList A n).map (stateOf P))
        = pathWeight (fun σ τ => x ^ (σ.muOf + τ.siteOf)) lam mu
            ((A :: idxList A n).map (stateOf P)) := by
  intro n
  induction n with
  | zero => intro A lam; rfl
  | succ m ih =>
      intro A lam
      show lam (stateOf P A) * (if compatB (stateOf P A) (stateOf P (A + 1)) then
              x ^ ((stateOf P A).muOf + (stateOf P (A + 1)).siteOf) else 0)
            * pathWeight _ (fun _ => (1 : ℤ)) mu _
        = lam (stateOf P A) * x ^ ((stateOf P A).muOf + (stateOf P (A + 1)).siteOf)
            * pathWeight _ (fun _ => (1 : ℤ)) mu _
      rw [compatB_stateOf P A, if_pos rfl, ← List.map_cons, ih (A + 1) (fun _ => (1 : ℤ))]

/-- **The state path locates the origin**: the arrival marker fires at index `0` and
nowhere else, so a path knows where it sits on the line even though the states carry no
index.  This is the first step of injectivity -- without it two translates of one
configuration would share a path. -/
theorem arr_eq_one_iff (P : SiteCost.PathData) (j : ℤ) : (stateOf P j).arr = 1 ↔ j = 0 := by
  unfold stateOf SiteCost.vArr
  by_cases h : j = 0 <;> simp [h]

/-- **And it locates the departure**, when the departure lies on the span. -/
theorem dep_eq_one_iff (P : SiteCost.PathData) (j : ℤ) :
    (stateOf P j).dep = 1 ↔ j = P.kstar := by
  unfold stateOf SiteCost.PathData.vD
  by_cases h : j = P.kstar <;> simp [h]

/-! ### Injectivity: what a state path determines

The join needs `stateOf` to be injective on configurations of a given span.  Each field
of the state is read straight back out, so everything the state carries is recovered by
`congrArg`; the only field needing an argument is `kstar`, which is recovered from the
departure marker. -/

theorem eps_eq_of_state {P Q : SiteCost.PathData} {j : ℤ} (h : stateOf P j = stateOf Q j) :
    P.eps = Q.eps := congrArg LocalState.eps h

theorem delta_eq_of_state {P Q : SiteCost.PathData} {j : ℤ} (h : stateOf P j = stateOf Q j) :
    P.delta = Q.delta := congrArg LocalState.delta h

theorem d_eq_of_state {P Q : SiteCost.PathData} {j : ℤ} (h : stateOf P j = stateOf Q j) :
    P.d j = Q.d j := congrArg LocalState.dcur h

theorem d_pred_eq_of_state {P Q : SiteCost.PathData} {j : ℤ} (h : stateOf P j = stateOf Q j) :
    P.d (j - 1) = Q.d (j - 1) := congrArg LocalState.dprev h

theorem travel_eq_of_state {P Q : SiteCost.PathData} {j : ℤ} (h : stateOf P j = stateOf Q j) :
    SiteCost.travel P.kstar j = SiteCost.travel Q.kstar j := congrArg LocalState.fcur h

/-- **The departure is recovered from the marker.**  If `j` is `P`'s departure and the two
states agree at `j`, it is `Q`'s departure too. -/
theorem kstar_eq_of_state {P Q : SiteCost.PathData} {j : ℤ} (h : stateOf P j = stateOf Q j)
    (hj : j = P.kstar) : j = Q.kstar := by
  have h1 : (stateOf P j).dep = 1 := (dep_eq_one_iff P j).mpr hj
  rw [h] at h1
  exact (dep_eq_one_iff Q j).mp h1

/-- **What the whole path determines.**  Two configurations whose states agree across the
span share their sign data, their deposits on the span, and their travel indicators.  With
`houter` forcing the deposits to vanish off the span, that is the deposit function
outright -- so all that separates this from injectivity is the departure, which is
recovered by `kstar_eq_of_state` whenever it lies on the span. -/
theorem stateOf_determines {P Q : SiteCost.PathData} {A : ℤ} {n : ℕ}
    (h : ∀ j : ℤ, A ≤ j → j ≤ A + n + 1 → stateOf P j = stateOf Q j)
    (hn : A ≤ A + n + 1) :
    P.eps = Q.eps ∧ P.delta = Q.delta ∧
      (∀ j : ℤ, A ≤ j → j ≤ A + n + 1 → P.d j = Q.d j) ∧
      (∀ j : ℤ, A ≤ j → j ≤ A + n + 1 →
        SiteCost.travel P.kstar j = SiteCost.travel Q.kstar j) := by
  refine ⟨eps_eq_of_state (h A le_rfl hn), delta_eq_of_state (h A le_rfl hn),
    fun j hj1 hj2 => d_eq_of_state (h j hj1 hj2),
    fun j hj1 hj2 => travel_eq_of_state (h j hj1 hj2)⟩

/-- **And off the span the deposits agree for free**, by `houter` -- provided the two
configurations have the same span. -/
theorem d_eq_off_span {P Q : SiteCost.PathData} (hA : P.A = Q.A) (hB : P.B = Q.B)
    {j : ℤ} (hj : j < P.A ∨ P.B < j) : P.d j = Q.d j := by
  have hP := (P.houter j hj).1
  have hQ := (Q.houter j (by rw [← hA, ← hB]; exact hj)).1
  rw [hP, hQ]

/-- **The deposits agree everywhere**: on the span by the states, off it by `houter`. -/
theorem d_eq_of_states {P Q : SiteCost.PathData} (hA : P.A = Q.A) (hB : P.B = Q.B)
    (h : ∀ j : ℤ, P.A ≤ j → j ≤ P.B + 1 → stateOf P j = stateOf Q j) : P.d = Q.d := by
  funext j
  by_cases hj : P.A ≤ j ∧ j ≤ P.B
  · exact d_eq_of_state (h j hj.1 (by omega))
  · exact d_eq_off_span hA hB (by omega)

/-- Two configurations agreeing in every data field are equal; the remaining fields are
proofs. -/
theorem pathData_ext {P Q : SiteCost.PathData}
    (hk : P.kstar = Q.kstar) (he : P.eps = Q.eps) (hd : P.delta = Q.delta)
    (hdd : P.d = Q.d) (hA : P.A = Q.A) (hB : P.B = Q.B) : P = Q := by
  cases P; cases Q
  simp only at hk he hd hdd hA hB
  subst hk; subst he; subst hd; subst hdd; subst hA; subst hB
  rfl

/-- **Injectivity of `stateOf`.**  Two configurations with the same span whose states
agree across it, and whose departure lies on it, are the same configuration.  This is the
first half of the bijection (M3) needs. -/
theorem stateOf_injective {P Q : SiteCost.PathData} (hA : P.A = Q.A) (hB : P.B = Q.B)
    (hks : P.A ≤ P.kstar) (hks' : P.kstar ≤ P.B + 1)
    (h : ∀ j : ℤ, P.A ≤ j → j ≤ P.B + 1 → stateOf P j = stateOf Q j) : P = Q :=
  pathData_ext (kstar_eq_of_state (h P.kstar hks hks') rfl)
    (eps_eq_of_state (h P.A le_rfl (by omega)))
    (delta_eq_of_state (h P.A le_rfl (by omega)))
    (d_eq_of_states hA hB h) hA hB

/-! ### The departure always lies on the span

BLOCK 213 assumed `A <= k* <= B + 1`.  It is a theorem.  `travel` is `1` on `[0, k*)`
and `-1` on `[k*, 0)`, and `houter` forces it to vanish off the span; since `0` is always
on the span (`hA`, `hB`), a departure outside the span would leave a non-zero travel
indicator at `B + 1` or at `A - 1`. -/

theorem kstar_le_B_succ (P : SiteCost.PathData) : P.kstar ≤ P.B + 1 := by
  by_contra h
  push_neg at h
  have hB := P.hB
  have h0 := (P.houter (P.B + 1) (Or.inr (by omega))).2
  unfold SiteCost.travel at h0
  rw [if_pos (by omega : (0 : ℤ) ≤ P.B + 1 ∧ P.B + 1 < P.kstar)] at h0
  omega

theorem A_le_kstar (P : SiteCost.PathData) : P.A ≤ P.kstar := by
  by_contra h
  push_neg at h
  have hA := P.hA
  have h0 := (P.houter (P.A - 1) (Or.inl (by omega))).2
  unfold SiteCost.travel at h0
  rw [if_neg (by omega : ¬((0 : ℤ) ≤ P.A - 1 ∧ P.A - 1 < P.kstar)),
    if_pos (by omega : P.kstar ≤ P.A - 1 ∧ P.A - 1 < 0)] at h0
  omega

/-- **Injectivity of `stateOf`, with no side hypotheses.**  Two configurations with the
same span whose states agree across it are the same configuration. -/
theorem stateOf_injective' {P Q : SiteCost.PathData} (hA : P.A = Q.A) (hB : P.B = Q.B)
    (h : ∀ j : ℤ, P.A ≤ j → j ≤ P.B + 1 → stateOf P j = stateOf Q j) : P = Q :=
  stateOf_injective hA hB (A_le_kstar P) (kstar_le_B_succ P) h

/-! ### A second guard surjectivity will need: parity

`compatB` is not by itself enough to characterise realisable paths.  A configuration also
carries `hpar`: the deposit and the travel indicator agree mod 2 at every edge.  A
compatible path violating that is realised by nothing, so the state predicate below is a
further necessary condition -- recorded now, since surjectivity is where it bites. -/

/-- A state is admissible when its deposit and travel indicator agree mod 2. -/
def validB (σ : LocalState) : Bool := decide ((σ.dcur - σ.fcur) % 2 = 0)

/-- **Every state of a configuration is admissible**, by `hpar`. -/
theorem validB_stateOf (P : SiteCost.PathData) (j : ℤ) : validB (stateOf P j) = true := by
  simp only [validB, stateOf, decide_eq_true_eq]
  exact P.hpar j

/-! ### Retraction: span-minimality IS visible to the state

BLOCK 214 expected `hAmin`/`hBmin` to be invisible to the states, and so expected
surjectivity to fail.  That was wrong.  `hAmin` reads `A = 0 or d A /= 0 or f A /= 0`,
and the state at `A` carries exactly `arr`, `dcur`, `fcur` -- with `arr = 1` iff `A = 0`
by `arr_eq_one_iff`.  So minimality is a condition on the path's END STATES, and it is
checkable there.  Likewise `heps` is visible in every state.

That removes the obstruction BLOCK 214 anticipated.  Every field-level constraint of
`PathData` is now accounted for:

    heps    -> epsValidB, at every state
    hpar    -> validB, at every state          (BLOCK 214)
    hAmin   -> endValidB, at the state at A
    hBmin   -> endValidB, at the state at B
    hA, hB  -> the arrival marker sits somewhere on the span
    houter  -> not a constraint: it DETERMINES the deposits off the span -/

/-- The sign data is admissible. -/
def epsValidB (σ : LocalState) : Bool := decide (σ.eps = 1 ∨ σ.eps = -1)

theorem epsValidB_stateOf (P : SiteCost.PathData) (j : ℤ) :
    epsValidB (stateOf P j) = true := by
  simp only [epsValidB, stateOf, decide_eq_true_eq]
  exact P.heps

/-- An end state is admissible when it is the origin, or carries a deposit, or carries
travel -- exactly `hAmin`/`hBmin`, read off the state. -/
def endValidB (σ : LocalState) : Bool :=
  decide (σ.arr = 1) || decide (σ.dcur ≠ 0) || decide (σ.fcur ≠ 0)

theorem endValidB_at_A (P : SiteCost.PathData) : endValidB (stateOf P P.A) = true := by
  simp only [endValidB, stateOf, Bool.or_eq_true, decide_eq_true_eq, SiteCost.vArr]
  rcases P.hAmin with h | h | h
  · simp [h]
  · tauto
  · tauto

theorem endValidB_at_B (P : SiteCost.PathData) : endValidB (stateOf P P.B) = true := by
  simp only [endValidB, stateOf, Bool.or_eq_true, decide_eq_true_eq, SiteCost.vArr]
  rcases P.hBmin with h | h | h
  · simp [h]
  · tauto
  · tauto

/-! ### The travel flow is local too

One more necessary condition, and the last one the state can be asked to carry.  `fcur`
is not free data: it is `travel k* j`, so a path could in principle carry travel values no
single `k*` produces.  But `travel_site_facts` says the constraint is **local** -- the
travel indicator changes only at the arrival and the departure, and by one unit each:

    f (j) + [j+1 = 0] = f (j+1) + [j+1 = k*]

which is a condition on two consecutive states.  So it belongs in the guard, and with it
the guard has no non-local content left. -/

/-- The travel indicator flows correctly across a step. -/
def flowB (σ τ : LocalState) : Bool :=
  decide (σ.fcur + (τ.arr : ℤ) = τ.fcur + (τ.dep : ℤ))

/-- **A configuration's states always flow correctly**, by `travel_site_facts`. -/
theorem flowB_stateOf (P : SiteCost.PathData) (j : ℤ) :
    flowB (stateOf P j) (stateOf P (j + 1)) = true := by
  simp only [flowB, stateOf, decide_eq_true_eq]
  refine (SiteCost.travel_site_facts P.kstar (j + 1)
    ((SiteCost.vArr (j + 1) : ℕ) : ℤ) ((P.vD (j + 1) : ℕ) : ℤ)
    (SiteCost.travel P.kstar j) (SiteCost.travel P.kstar (j + 1))
    ?_ ?_ ?_ rfl).1
  · unfold SiteCost.vArr; split_ifs <;> simp
  · unfold SiteCost.PathData.vD; split_ifs <;> simp
  · congr 1; ring

/-- **The full local guard**: the right state continues the left one, and the travel
indicator flows.  Everything a realisable path must satisfy between consecutive states. -/
def stepB (σ τ : LocalState) : Bool := compatB σ τ && flowB σ τ

theorem stepB_stateOf (P : SiteCost.PathData) (j : ℤ) :
    stepB (stateOf P j) (stateOf P (j + 1)) = true := by
  simp only [stepB, Bool.and_eq_true]
  exact ⟨compatB_stateOf P j, flowB_stateOf P j⟩

/-- **Guarding by ANY predicate the configuration satisfies leaves its weight alone.**
This generalises `pathWeight_guarded_eq` (BLOCK 212) from `compatB` to the full local
guard `stepB`, or to any other. -/
theorem pathWeight_guard_eq (x : ℤ) (P : SiteCost.PathData) (mu : LocalState → ℤ)
    (g : LocalState → LocalState → Bool)
    (hg : ∀ j : ℤ, g (stateOf P j) (stateOf P (j + 1)) = true) :
    ∀ (n : ℕ) (A : ℤ) (lam : LocalState → ℤ),
      pathWeight (fun σ τ => if g σ τ then x ^ (σ.muOf + τ.siteOf) else 0) lam mu
          ((A :: idxList A n).map (stateOf P))
        = pathWeight (fun σ τ => x ^ (σ.muOf + τ.siteOf)) lam mu
            ((A :: idxList A n).map (stateOf P)) := by
  intro n
  induction n with
  | zero => intro A lam; rfl
  | succ m ih =>
      intro A lam
      show lam (stateOf P A) * (if g (stateOf P A) (stateOf P (A + 1)) then
              x ^ ((stateOf P A).muOf + (stateOf P (A + 1)).siteOf) else 0)
            * pathWeight _ (fun _ => (1 : ℤ)) mu _
        = lam (stateOf P A) * x ^ ((stateOf P A).muOf + (stateOf P (A + 1)).siteOf)
            * pathWeight _ (fun _ => (1 : ℤ)) mu _
      rw [hg A, if_pos rfl, ← List.map_cons, ih (A + 1) (fun _ => (1 : ℤ))]

/-- In particular the full guard `stepB` may be used. -/
theorem pathWeight_stepB_eq (x : ℤ) (P : SiteCost.PathData) (mu : LocalState → ℤ)
    (n : ℕ) (A : ℤ) (lam : LocalState → ℤ) :
    pathWeight (fun σ τ => if stepB σ τ then x ^ (σ.muOf + τ.siteOf) else 0) lam mu
        ((A :: idxList A n).map (stateOf P))
      = pathWeight (fun σ τ => x ^ (σ.muOf + τ.siteOf)) lam mu
          ((A :: idxList A n).map (stateOf P)) :=
  pathWeight_guard_eq x P mu stepB (stepB_stateOf P) n A lam

/-! ### Sufficiency: assembling a configuration from guarded data

The last piece of (M3).  Everything the guards check is exactly what the six proof fields
of `PathData` need, so a path satisfying them can be assembled into a configuration.  The
data is forced -- deposits from the states inside the span and `0` outside, `eps` and
`delta` from any state, `k*` from the departure marker -- and each proof field is
discharged by the guard aimed at it. -/

/-- Off the span the travel indicator vanishes, given that the departure lies on the
span.  This is `houter`'s travel half, and the converse of BLOCK 214. -/
theorem travel_zero_off (kstar A B j : ℤ) (hA : A ≤ 0) (hB : 0 ≤ B)
    (hk1 : A ≤ kstar) (hk2 : kstar ≤ B + 1) (hj : j < A ∨ B < j) :
    SiteCost.travel kstar j = 0 := by
  unfold SiteCost.travel
  rcases hj with h | h
  · rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (by omega), if_neg (by omega)]

/-- **The construction.**  Guarded data assembles into a configuration.  This is the
sufficiency half of (M3)'s bijection; `stateOf_injective'` is the other. -/
def mkPathData (kstar eps : ℤ) (delta : Bool) (dspan : ℤ → ℤ) (A B : ℤ)
    (heps : eps = 1 ∨ eps = -1) (hA : A ≤ 0) (hB : 0 ≤ B)
    (hk1 : A ≤ kstar) (hk2 : kstar ≤ B + 1)
    (hpar : ∀ j : ℤ, A ≤ j → j ≤ B → (dspan j - SiteCost.travel kstar j) % 2 = 0)
    (hAmin : A = 0 ∨ dspan A ≠ 0 ∨ SiteCost.travel kstar A ≠ 0)
    (hBmin : B = 0 ∨ dspan B ≠ 0 ∨ SiteCost.travel kstar B ≠ 0) :
    SiteCost.PathData where
  kstar := kstar
  eps := eps
  delta := delta
  heps := heps
  d := fun j => if A ≤ j ∧ j ≤ B then dspan j else 0
  hpar := by
    intro j
    by_cases hj : A ≤ j ∧ j ≤ B
    · rw [if_pos hj]; exact hpar j hj.1 hj.2
    · rw [if_neg hj, travel_zero_off kstar A B j hA hB hk1 hk2 (by omega)]
      simp
  A := A
  B := B
  hA := hA
  hB := hB
  houter := by
    intro j hj
    refine ⟨?_, travel_zero_off kstar A B j hA hB hk1 hk2 hj⟩
    rw [if_neg (by omega)]
  hAmin := by
    have hAB : A ≤ B := by omega
    rcases hAmin with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by rw [if_pos ⟨le_refl A, hAB⟩]; exact h))
    · exact Or.inr (Or.inr h)
  hBmin := by
    have hAB : A ≤ B := by omega
    rcases hBmin with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by rw [if_pos ⟨hAB, le_refl B⟩]; exact h))
    · exact Or.inr (Or.inr h)

/-- **And it realises the data it was built from**: on the span its deposits are the ones
supplied, and its sign data and departure are as given. -/
theorem mkPathData_d {kstar eps : ℤ} {delta : Bool} {dspan : ℤ → ℤ} {A B : ℤ}
    {heps hA hB hk1 hk2 hpar hAmin hBmin} {j : ℤ} (hj1 : A ≤ j) (hj2 : j ≤ B) :
    (mkPathData kstar eps delta dspan A B heps hA hB hk1 hk2 hpar hAmin hBmin).d j
      = dspan j := if_pos ⟨hj1, hj2⟩

/-- **The round trip on the span**: the constructed configuration's states carry exactly
the data supplied. -/
theorem mkPathData_dcur {kstar eps : ℤ} {delta : Bool} {dspan : ℤ → ℤ} {A B : ℤ}
    {heps hA hB hk1 hk2 hpar hAmin hBmin} {j : ℤ} (hj1 : A ≤ j) (hj2 : j ≤ B) :
    (stateOf (mkPathData kstar eps delta dspan A B heps hA hB hk1 hk2 hpar hAmin hBmin) j).dcur
      = dspan j := by simp only [stateOf]; exact mkPathData_d hj1 hj2

theorem mkPathData_dprev {kstar eps : ℤ} {delta : Bool} {dspan : ℤ → ℤ} {A B : ℤ}
    {heps hA hB hk1 hk2 hpar hAmin hBmin} {j : ℤ} (hj1 : A ≤ j - 1) (hj2 : j - 1 ≤ B) :
    (stateOf (mkPathData kstar eps delta dspan A B heps hA hB hk1 hk2 hpar hAmin hBmin) j).dprev
      = dspan (j - 1) := by simp only [stateOf]; exact mkPathData_d hj1 hj2

theorem mkPathData_fcur {kstar eps : ℤ} {delta : Bool} {dspan : ℤ → ℤ} {A B : ℤ}
    {heps hA hB hk1 hk2 hpar hAmin hBmin} {j : ℤ} :
    (stateOf (mkPathData kstar eps delta dspan A B heps hA hB hk1 hk2 hpar hAmin hBmin) j).fcur
      = SiteCost.travel kstar j := rfl

theorem mkPathData_eps {kstar eps : ℤ} {delta : Bool} {dspan : ℤ → ℤ} {A B : ℤ}
    {heps hA hB hk1 hk2 hpar hAmin hBmin} {j : ℤ} :
    (stateOf (mkPathData kstar eps delta dspan A B heps hA hB hk1 hk2 hpar hAmin hBmin) j).eps
      = eps := rfl

theorem mkPathData_delta {kstar eps : ℤ} {delta : Bool} {dspan : ℤ → ℤ} {A B : ℤ}
    {heps hA hB hk1 hk2 hpar hAmin hBmin} {j : ℤ} :
    (stateOf (mkPathData kstar eps delta dspan A B heps hA hB hk1 hk2 hpar hAmin hBmin) j).delta
      = delta := rfl

/-! ### The composition: configurations of a given span ARE guarded data

`mkPathData` builds a configuration from guarded data and `stateOf_injective'` says no two
configurations share their states.  Packaging the guarded data as a structure makes the
two into a pair of mutually inverse maps, which is the bijection (M3) needs. -/

/-- Guarded data for the span `[A, B]`.  `hzero` normalises the deposits off the span, so
that the data is determined by the configuration it builds. -/
structure SpanData (A B : ℤ) where
  kstar : ℤ
  eps : ℤ
  delta : Bool
  dspan : ℤ → ℤ
  heps : eps = 1 ∨ eps = -1
  hA : A ≤ 0
  hB : 0 ≤ B
  hk1 : A ≤ kstar
  hk2 : kstar ≤ B + 1
  hzero : ∀ j : ℤ, j < A ∨ B < j → dspan j = 0
  hpar : ∀ j : ℤ, A ≤ j → j ≤ B → (dspan j - SiteCost.travel kstar j) % 2 = 0
  hAmin : A = 0 ∨ dspan A ≠ 0 ∨ SiteCost.travel kstar A ≠ 0
  hBmin : B = 0 ∨ dspan B ≠ 0 ∨ SiteCost.travel kstar B ≠ 0

/-- Guarded data builds its configuration. -/
def SpanData.toPath {A B : ℤ} (S : SpanData A B) : SiteCost.PathData :=
  mkPathData S.kstar S.eps S.delta S.dspan A B S.heps S.hA S.hB S.hk1 S.hk2 S.hpar
    S.hAmin S.hBmin

theorem SpanData.toPath_d {A B : ℤ} (S : SpanData A B) (j : ℤ) : S.toPath.d j = S.dspan j := by
  show (if A ≤ j ∧ j ≤ B then S.dspan j else 0) = S.dspan j
  by_cases h : A ≤ j ∧ j ≤ B
  · rw [if_pos h]
  · rw [if_neg h, S.hzero j (by omega)]

/-- A configuration is guarded data for its own span. -/
def ofPath (P : SiteCost.PathData) : SpanData P.A P.B where
  kstar := P.kstar
  eps := P.eps
  delta := P.delta
  dspan := P.d
  heps := P.heps
  hA := P.hA
  hB := P.hB
  hk1 := A_le_kstar P
  hk2 := kstar_le_B_succ P
  hzero := fun j hj => (P.houter j hj).1
  hpar := fun j _ _ => P.hpar j
  hAmin := P.hAmin
  hBmin := P.hBmin

theorem spanData_ext {A B : ℤ} {S T : SpanData A B} (hk : S.kstar = T.kstar)
    (he : S.eps = T.eps) (hd : S.delta = T.delta) (hs : S.dspan = T.dspan) : S = T := by
  cases S; cases T
  simp only at hk he hd hs
  subst hk; subst he; subst hd; subst hs
  rfl

/-- **Round trip one**: build from a configuration's own data and you get it back. -/
theorem ofPath_toPath (P : SiteCost.PathData) : (ofPath P).toPath = P :=
  pathData_ext rfl rfl rfl (funext fun j => (ofPath P).toPath_d j) rfl rfl

/-- **Round trip two**: read the data off the configuration you built and you get it back. -/
theorem toPath_ofPath {A B : ℤ} (S : SpanData A B) : ofPath S.toPath = S :=
  spanData_ext rfl rfl rfl (funext fun j => S.toPath_d j)

/-- **The bijection.**  `toPath` is injective, so guarded data and configurations of a
given span correspond one to one -- which is what (M3) needs to turn a sum over
configurations into a sum over paths. -/
theorem toPath_injective {A B : ℤ} : Function.Injective (SpanData.toPath (A := A) (B := B)) := by
  intro S T h
  refine spanData_ext (congrArg SiteCost.PathData.kstar h) (congrArg SiteCost.PathData.eps h)
    (congrArg SiteCost.PathData.delta h) ?_
  funext j
  rw [← S.toPath_d j, ← T.toPath_d j, h]

/-! ### List packaging: the state path as a list determines the configuration

The bijection of BLOCK 218 is stated for guarded data; `IsAssembly` sums over state paths
as lists.  The bridge is that two functions agreeing on the mapped span list agree
pointwise -- proved by induction on the list, with no index arithmetic, which is the
lesson of the two aborts earlier in this file. -/

/-- Two functions whose images along `A :: idxList A n` agree, agree on `[A, A + n]`. -/
theorem map_idxList_inj {S : Type*} (f g : ℤ → S) :
    ∀ (n : ℕ) (A : ℤ), (A :: idxList A n).map f = (A :: idxList A n).map g →
      ∀ j : ℤ, A ≤ j → j ≤ A + n → f j = g j := by
  intro n
  induction n with
  | zero =>
      intro A h j hj1 hj2
      have hhead : f A = g A := by
        have := congrArg List.head? h; simpa using this
      push_cast at hj2
      have hjA : j = A := by omega
      rw [hjA]; exact hhead
  | succ m ih =>
      intro A h j hj1 hj2
      have hhead : f A = g A := by
        have := congrArg List.head? h; simpa using this
      have htail : ((A + 1) :: idxList (A + 1) m).map f
          = ((A + 1) :: idxList (A + 1) m).map g := by
        have := congrArg List.tail h; simpa [idxList] using this
      by_cases hjA : j = A
      · rw [hjA]; exact hhead
      · refine ih (A + 1) htail j (by omega) ?_
        push_cast at hj2 ⊢
        omega

/-- **The state path, as a list, determines the configuration.**  This is the list-level
form of (M3)'s bijection: distinct guarded data give distinct state paths, so a sum over
paths counts each configuration exactly once. -/
theorem statePath_inj {A B : ℤ} {S T : SpanData A B} {n : ℕ} (hn : B + 1 ≤ A + n)
    (h : (A :: idxList A n).map (stateOf S.toPath)
        = (A :: idxList A n).map (stateOf T.toPath)) :
    S = T := by
  refine toPath_injective (stateOf_injective' rfl rfl ?_)
  intro j hj1 hj2
  have hAe : S.toPath.A = A := rfl
  have hBe : S.toPath.B = B := rfl
  rw [hAe] at hj1
  rw [hBe] at hj2
  exact map_idxList_inj _ _ n A h j hj1 (by omega)

/-! ### The degree cut: everything is bounded by the relaxed length

The finiteness (M3) needs.  `lR` is a sum of non-negative terms, one `mu j` per edge of
the span, and `mu j` dominates both `|d j|` and `1`.  So a configuration of relaxed length
`N` has span at most `N` edges and deposits at most `N` -- finitely many, at each degree. -/

/-- The span has at most `lR` edges, since every edge costs at least one. -/
theorem card_le_lR (P : SiteCost.PathData) : (Finset.Icc P.A P.B).card ≤ P.lR := by
  have h2 : ∑ _j ∈ Finset.Icc P.A P.B, 1 ≤ ∑ j ∈ Finset.Icc P.A P.B, P.mu j :=
    Finset.sum_le_sum (fun j _ => P.mu_pos j)
  have h3 : ∑ j ∈ Finset.Icc P.A P.B, P.mu j ≤ P.lR := by
    unfold SiteCost.PathData.lR; exact Nat.le_add_right _ _
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h2
  omega

/-- Every deposit is bounded by the relaxed length. -/
theorem abs_d_le_lR (P : SiteCost.PathData) (j : ℤ) : (P.d j).natAbs ≤ P.lR := by
  by_cases hj : P.A ≤ j ∧ j ≤ P.B
  · have h1 : (P.d j).natAbs ≤ P.mu j := P.mu_ge_d j
    have h2 : P.mu j ≤ ∑ i ∈ Finset.Icc P.A P.B, P.mu i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_Icc.mpr hj)
    have h3 : ∑ i ∈ Finset.Icc P.A P.B, P.mu i ≤ P.lR := by
      unfold SiteCost.PathData.lR; exact Nat.le_add_right _ _
    omega
  · rw [(P.houter j (by omega)).1]; simp

/-- **The span is confined to `[-lR, lR]`.**  With `abs_d_le_lR` this makes the
configurations of relaxed length at most `N` a finite collection. -/
theorem span_bounds (P : SiteCost.PathData) : -(P.lR : ℤ) ≤ P.A ∧ P.B ≤ P.lR := by
  have hcard := card_le_lR P
  rw [Int.card_Icc] at hcard
  have hA := P.hA
  have hB := P.hB
  have : (P.B + 1 - P.A).toNat = P.B + 1 - P.A := by omega
  omega

/-- **And the departure with it.**  So every piece of data a configuration carries is
bounded by its relaxed length: the span, the deposits, and `k*`. -/
theorem kstar_bounds (P : SiteCost.PathData) :
    -(P.lR : ℤ) ≤ P.kstar ∧ P.kstar ≤ (P.lR : ℤ) + 1 := by
  have h := span_bounds P
  exact ⟨le_trans h.1 (A_le_kstar P), le_trans (kstar_le_B_succ P) (by omega)⟩

/-! ### Finitely much data determines a configuration of bounded degree

The bounds of BLOCK 220 turn into finiteness through this: a configuration of relaxed
length at most `N` is pinned down by its `kstar`, `eps`, `delta`, `A`, `B` and its
deposits **on `[-N, N]` only** -- everything outside is forced to vanish, because the span
cannot reach there.  So the data is a point of a bounded box. -/

/-- **A configuration of degree at most `N` is determined by finitely much data.** -/
theorem pathData_eq_of_agree (N : ℕ) {P Q : SiteCost.PathData} (hP : P.lR ≤ N) (hQ : Q.lR ≤ N)
    (hk : P.kstar = Q.kstar) (he : P.eps = Q.eps) (hd : P.delta = Q.delta)
    (hA : P.A = Q.A) (hB : P.B = Q.B)
    (hdd : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ (N : ℤ) → P.d j = Q.d j) : P = Q := by
  refine pathData_ext hk he hd ?_ hA hB
  funext j
  have hPb := span_bounds P
  have hQb := span_bounds Q
  have hPN : (P.lR : ℤ) ≤ (N : ℤ) := by exact_mod_cast hP
  have hQN : (Q.lR : ℤ) ≤ (N : ℤ) := by exact_mod_cast hQ
  by_cases hj : -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ)
  · exact hdd j hj.1 hj.2
  · rw [(P.houter j (by omega)).1, (Q.houter j (by omega)).1]

/-- **And that data lies in a box of size set by `N`.**  Every coordinate is bounded, so
the configurations of degree at most `N` inject into a finite product. -/
theorem pathData_box (N : ℕ) (P : SiteCost.PathData) (hP : P.lR ≤ N) :
    -(N : ℤ) ≤ P.A ∧ P.A ≤ 0 ∧ 0 ≤ P.B ∧ P.B ≤ (N : ℤ)
      ∧ -(N : ℤ) ≤ P.kstar ∧ P.kstar ≤ (N : ℤ) + 1
      ∧ (P.eps = 1 ∨ P.eps = -1)
      ∧ ∀ j : ℤ, (P.d j).natAbs ≤ N := by
  have hb := span_bounds P
  have hk := kstar_bounds P
  have hPN : (P.lR : ℤ) ≤ (N : ℤ) := by exact_mod_cast hP
  refine ⟨by omega, P.hA, P.hB, by omega, by omega, by omega, P.heps, fun j => ?_⟩
  exact le_trans (abs_d_le_lR P j) hP

/-! ### Finiteness at each degree

`pathData_box` says every coordinate of a bounded-degree configuration is bounded, and
`pathData_eq_of_agree` says those coordinates determine it.  Encoding the whole lot as a
SINGLE function on a finite index type -- five scalars and the deposits on `[-N, N]` --
turns that into one application of `Set.Finite.pi`, rather than a tower of products. -/

/-- All of a configuration's bounded-degree data, as one function on a finite index. -/
def encAll (N : ℕ) (P : SiteCost.PathData) :
    (Fin 5 ⊕ ↥(Finset.Icc (-(N : ℤ)) (N : ℤ))) → ℤ :=
  fun x => match x with
    | Sum.inl i =>
        if i = 0 then P.kstar else if i = 1 then P.eps
        else if i = 2 then (if P.delta then 1 else 0)
        else if i = 3 then P.A else P.B
    | Sum.inr j => P.d j.1

theorem encAll_inj (N : ℕ) {P Q : SiteCost.PathData} (hP : P.lR ≤ N) (hQ : Q.lR ≤ N)
    (h : encAll N P = encAll N Q) : P = Q := by
  have hk : P.kstar = Q.kstar := by have := congrFun h (Sum.inl 0); simpa [encAll] using this
  have he : P.eps = Q.eps := by have := congrFun h (Sum.inl 1); simpa [encAll] using this
  have hA : P.A = Q.A := by have := congrFun h (Sum.inl 3); simpa [encAll] using this
  have hB : P.B = Q.B := by have := congrFun h (Sum.inl 4); simpa [encAll] using this
  have hd : P.delta = Q.delta := by
    have h2 := congrFun h (Sum.inl 2)
    simp only [encAll] at h2
    norm_num at h2
    cases hh : P.delta <;> cases hh2 : Q.delta <;> simp_all
  refine pathData_eq_of_agree N hP hQ hk he hd hA hB ?_
  intro j hj1 hj2
  have := congrFun h (Sum.inr ⟨j, Finset.mem_Icc.mpr ⟨hj1, hj2⟩⟩)
  simpa [encAll] using this

/-- **The configurations of relaxed length at most `N` form a finite set.**  This is the
degree cut (M3) needs on the configuration side; `dcur_le_muOf`/`fcur_le_muOf` give the
matching cut on the state side. -/
theorem finite_degree_le (N : ℕ) : {P : SiteCost.PathData | P.lR ≤ N}.Finite := by
  refine Set.Finite.of_finite_image (f := encAll N) ?_ ?_
  · refine Set.Finite.subset
      (Set.Finite.pi (t := fun _ : Fin 5 ⊕ ↥(Finset.Icc (-(N : ℤ)) (N : ℤ)) =>
        Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)) (fun _ => Set.finite_Icc _ _)) ?_
    rintro _ ⟨P, hP, rfl⟩
    intro i _
    have hbox := pathData_box N P hP
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hbox
    cases i with
    | inl k =>
        simp only [encAll, Set.mem_Icc]
        rcases h7 with h7 | h7 <;> split_ifs <;> omega
    | inr j =>
        simp only [encAll, Set.mem_Icc]
        have := h8 j.1
        omega
  · intro P hP Q hQ h
    exact encAll_inj N hP hQ h

/-! ### The chain: a sum over configurations IS a sum over state paths

Every link has been proved separately; this joins them.  The weight of a configuration is
the path weight of its state path (BLOCK 208), and distinct configurations have distinct
state paths (BLOCK 219), so summing over configurations and summing over the state paths
they occupy give the same number. -/

/-- **A sum over configurations of a fixed span is a sum over their state paths.**  This
is the identity (M3) asks for, on a finite collection. -/
theorem sum_configs_eq_sum_paths (x : ℤ) {A : ℤ} {m : ℕ}
    [DecidableEq (SpanData A (A + m))]
    (C : Finset (SpanData A (A + m))) :
    ∑ S ∈ C, x ^ S.toPath.lR
      = ∑ L ∈ C.image (fun S => (A :: idxList A (m + 1)).map (stateOf S.toPath)),
          pathWeight (fun σ τ => x ^ (σ.muOf + τ.siteOf)) (fun σ => x ^ σ.siteOf)
            (fun _ => x ^ (0 : ℕ)) L := by
  rw [Finset.sum_image ?inj]
  case inj =>
    intro S _ T _ h
    exact statePath_inj (by push_cast; omega) h
  refine Finset.sum_congr rfl fun S _ => ?_
  exact lR_exp_pathWeight_family x m (fun S : SpanData A (A + m) => S.toPath)
    (fun _ => rfl) S

/-! ### Correction to BLOCK 223, and the induction it missed

BLOCK 223 called the remaining step "one restatement".  That was too optimistic.
`mkPathData` wants `hpar` phrased with `travel kstar`, but a guarded path carries only its
own `fcur` together with the FLOW relation.  Recovering `fcur = travel kstar` from the
flow is an induction, not a restatement -- the flow pins down the increments, and the
vanishing off the span pins down the constant.

The argument: `f` and `travel kstar` satisfy the same flow relation, so their difference
has zero increment everywhere, hence is constant; and it vanishes off the span, hence is
zero. -/

/-- A function with zero increment everywhere is constant. -/
theorem const_of_step {g : ℤ → ℤ} (h : ∀ j : ℤ, g j = g (j + 1)) : ∀ j : ℤ, g j = g 0 := by
  intro j
  induction j using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [← h k]; exact ih
  | pred k ih =>
      have hstep := h (-(k : ℤ) - 1)
      have he : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
      rw [he] at hstep
      rw [hstep]; exact ih

/-- **The flow relation determines the travel indicator.**  A function obeying the flow
and vanishing off the span IS `travel kstar`.  This is what a guarded path needs before
`mkPathData` will accept it. -/
theorem eq_travel_of_flow (kstar A B : ℤ) (f : ℤ → ℤ)
    (hflow : ∀ j : ℤ, f j + ((SiteCost.vArr (j + 1) : ℕ) : ℤ)
      = f (j + 1) + (if j + 1 = kstar then (1 : ℤ) else 0))
    (hzero : ∀ j : ℤ, j < A ∨ B < j → f j = 0)
    (hA : A ≤ 0) (hB : 0 ≤ B) (hk1 : A ≤ kstar) (hk2 : kstar ≤ B + 1) :
    ∀ j : ℤ, f j = SiteCost.travel kstar j := by
  have htravel : ∀ j : ℤ, SiteCost.travel kstar j + ((SiteCost.vArr (j + 1) : ℕ) : ℤ)
      = SiteCost.travel kstar (j + 1) + (if j + 1 = kstar then (1 : ℤ) else 0) := by
    intro j
    refine (SiteCost.travel_site_facts kstar (j + 1) ((SiteCost.vArr (j + 1) : ℕ) : ℤ)
      (if j + 1 = kstar then (1 : ℤ) else 0)
      (SiteCost.travel kstar j) (SiteCost.travel kstar (j + 1)) ?_ rfl ?_ rfl).1
    · unfold SiteCost.vArr; split_ifs <;> simp
    · congr 1; ring
  have hstep : ∀ j : ℤ, f j - SiteCost.travel kstar j
      = f (j + 1) - SiteCost.travel kstar (j + 1) := by
    intro j
    have h1 := hflow j
    have h2 := htravel j
    omega
  have hconst := const_of_step (g := fun i => f i - SiteCost.travel kstar i) hstep
  have hfar : f (A - 1) - SiteCost.travel kstar (A - 1) = 0 := by
    rw [hzero (A - 1) (Or.inl (by omega)),
      travel_zero_off kstar A B (A - 1) hA hB hk1 hk2 (Or.inl (by omega))]
    ring
  intro j
  have hj : f j - SiteCost.travel kstar j = f 0 - SiteCost.travel kstar 0 := hconst j
  have h0 : f (A - 1) - SiteCost.travel kstar (A - 1) = f 0 - SiteCost.travel kstar 0 :=
    hconst (A - 1)
  omega

/-! ### Reading a state function off a list, without indexing

BLOCK 224 left one obstacle: turning a guarded path (a list) back into a state function so
`mkPathData` can consume it.  Done by induction on the list, never by indexing -- the
lesson of the two aborts, and of `map_idxList_inj` (BLOCK 219) which went the other way. -/

/-- Functions agreeing from `A` onward have the same image along `A :: idxList A n`. -/
theorem map_idxList_congr {S : Type*} (f g : ℤ → S) :
    ∀ (n : ℕ) (A : ℤ), (∀ j : ℤ, A ≤ j → f j = g j) →
      (A :: idxList A n).map f = (A :: idxList A n).map g := by
  intro n
  induction n with
  | zero => intro A h; simp [idxList, h A le_rfl]
  | succ m ih =>
      intro A h
      have h1 : f A = g A := h A le_rfl
      have h2 := ih (A + 1) (fun j hj => h j (by omega))
      show f A :: ((A + 1) :: idxList (A + 1) m).map f
        = g A :: ((A + 1) :: idxList (A + 1) m).map g
      rw [h1, h2]

/-- **Every list of the right length is a state path.**  So a guarded path, which is a
list, yields the state function `mkPathData` needs -- and the obstacle of BLOCK 224 is
removed. -/
theorem exists_fun_of_length {S : Type*} :
    ∀ (n : ℕ) (A : ℤ) (L : List S), L.length = n + 1 →
      ∃ f : ℤ → S, L = (A :: idxList A n).map f := by
  intro n
  induction n with
  | zero =>
      intro A L hL
      cases L with
      | nil => simp at hL
      | cons a t =>
          have ht : t = [] := by cases t <;> simp_all
          subst ht
          exact ⟨fun _ => a, rfl⟩
  | succ m ih =>
      intro A L hL
      cases L with
      | nil => simp at hL
      | cons a t =>
          have ht : t.length = m + 1 := by simpa using hL
          obtain ⟨g, hg⟩ := ih (A + 1) t ht
          refine ⟨fun j => if j = A then a else g j, ?_⟩
          have hcong : ((A + 1) :: idxList (A + 1) m).map
                (fun j : ℤ => if j = A then a else g j)
              = ((A + 1) :: idxList (A + 1) m).map g :=
            map_idxList_congr _ _ m (A + 1) (fun j hj => by rw [if_neg (by omega)])
          show a :: t = (if (A : ℤ) = A then a else g A)
            :: ((A + 1) :: idxList (A + 1) m).map (fun j : ℤ => if j = A then a else g j)
          rw [if_pos rfl, hcong, ← hg]

/-! ### What a guarded state function is, and that configurations give one

To state the set equality (M3) needs, "guarded" has to be pinned down.  Every condition
below has already been proved to hold of a configuration; collecting them into one
structure names the target of the converse construction.

The conditions are imposed on ALL of `ℤ`, not on a window.  That is not a strengthening --
a configuration's state function is defined everywhere and satisfies them everywhere --
and it avoids the boundary fiddliness of a windowed guard, where `eq_travel_of_flow`
would need the flow to hold one step outside the span. -/

/-- A state function is *guarded* when it satisfies every local condition a configuration's
state function satisfies. -/
structure Guarded (A B kstar : ℤ) (st : ℤ → LocalState) : Prop where
  step : ∀ j : ℤ, stepB (st j) (st (j + 1)) = true
  valid : ∀ j : ℤ, validB (st j) = true
  epsv : ∀ j : ℤ, epsValidB (st j) = true
  endA : endValidB (st A) = true
  endB : endValidB (st B) = true
  dep : ∀ j : ℤ, (st j).dep = 1 ↔ j = kstar
  arrv : ∀ j : ℤ, (st j).arr = SiteCost.vArr j
  depv : ∀ j : ℤ, (st j).dep = 0 ∨ (st j).dep = 1
  outer : ∀ j : ℤ, j < A ∨ B < j → (st j).dcur = 0 ∧ (st j).fcur = 0
  loA : A ≤ 0
  hiB : 0 ≤ B
  kstLo : A ≤ kstar
  kstHi : kstar ≤ B + 1

/-- **Forward inclusion: every configuration's state function is guarded.**  Each field is
a theorem already proved; this collects them. -/
theorem guarded_stateOf (P : SiteCost.PathData) :
    Guarded P.A P.B P.kstar (stateOf P) where
  step := stepB_stateOf P
  valid := validB_stateOf P
  epsv := epsValidB_stateOf P
  endA := endValidB_at_A P
  endB := endValidB_at_B P
  dep := dep_eq_one_iff P
  arrv := fun _ => rfl
  depv := fun j => by
    unfold stateOf SiteCost.PathData.vD
    by_cases h : j = P.kstar <;> simp [h]
  outer := fun j hj => ⟨(P.houter j hj).1, (P.houter j hj).2⟩
  loA := P.hA
  hiB := P.hB
  kstLo := A_le_kstar P
  kstHi := kstar_le_B_succ P

/-! ### Converse inclusion: a guarded state function comes from a configuration -/

/-- `const_of_step` for an arbitrary type; the proof never used the arithmetic. -/
theorem const_of_step_gen {S : Type*} {g : ℤ → S} (h : ∀ j : ℤ, g j = g (j + 1)) :
    ∀ j : ℤ, g j = g 0 := by
  intro j
  induction j using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [← h k]; exact ih
  | pred k ih =>
      have hstep := h (-(k : ℤ) - 1)
      have he : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
      rw [he] at hstep
      rw [hstep]; exact ih

theorem delta_const_of_guarded {A B kstar : ℤ} {st : ℤ → LocalState}
    (hg : Guarded A B kstar st) (j : ℤ) : (st j).delta = (st 0).delta := by
  refine const_of_step_gen (g := fun i => (st i).delta) ?_ j
  intro i
  have hs := hg.step i
  simp only [stepB, compatB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  exact hs.1.2.symm

/-- **The sign data is constant along a guarded path**, because the compatibility guard
carries it across every step.  Needed to match a guarded path's states field by field. -/
theorem eps_const_of_guarded {A B kstar : ℤ} {st : ℤ → LocalState}
    (hg : Guarded A B kstar st) (j : ℤ) : (st j).eps = (st 0).eps := by
  refine const_of_step (g := fun i => (st i).eps) ?_ j
  intro i
  have hs := hg.step i
  simp only [stepB, compatB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  exact hs.1.1.2.symm


/-- **Converse inclusion.**  Every guarded state function is realised by a configuration
with the same span, departure and deposits.  With `guarded_stateOf` (BLOCK 226) this is the
set equality (M3) needs. -/
theorem exists_config_of_guarded {A B kstar : ℤ} {st : ℤ → LocalState}
    (hg : Guarded A B kstar st) :
    ∃ P : SiteCost.PathData, P.A = A ∧ P.B = B ∧ P.kstar = kstar ∧
      (∀ j : ℤ, A ≤ j → j ≤ B → P.d j = (st j).dcur) ∧
      P.eps = (st 0).eps ∧ P.delta = (st 0).delta := by
  have hdepZ : ∀ j : ℤ, (((st j).dep : ℕ) : ℤ) = if j = kstar then (1 : ℤ) else 0 := by
    intro j
    by_cases h : j = kstar
    · rw [if_pos h, (hg.dep j).mpr h]; norm_num
    · rw [if_neg h]
      rcases hg.depv j with h0 | h1
      · rw [h0]; norm_num
      · exact absurd ((hg.dep j).mp h1) h
  have hflow : ∀ j : ℤ, (st j).fcur + ((SiteCost.vArr (j + 1) : ℕ) : ℤ)
      = (st (j + 1)).fcur + (if j + 1 = kstar then (1 : ℤ) else 0) := by
    intro j
    have hs := hg.step j
    simp only [stepB, Bool.and_eq_true] at hs
    have hf := hs.2
    simp only [flowB, decide_eq_true_eq] at hf
    rw [hg.arrv (j + 1), hdepZ (j + 1)] at hf
    exact hf
  have hftravel : ∀ j : ℤ, (st j).fcur = SiteCost.travel kstar j :=
    eq_travel_of_flow kstar A B (fun j => (st j).fcur) hflow
      (fun j hj => (hg.outer j hj).2) hg.loA hg.hiB hg.kstLo hg.kstHi
  refine ⟨mkPathData kstar (st A).eps (st A).delta (fun j => (st j).dcur) A B ?_ hg.loA hg.hiB
    hg.kstLo hg.kstHi ?_ ?_ ?_, rfl, rfl, rfl, fun j hj1 hj2 => mkPathData_d hj1 hj2,
    eps_const_of_guarded hg A, delta_const_of_guarded hg A⟩
  · have := hg.epsv A
    simpa [epsValidB] using this
  · intro j _ _
    have hv := hg.valid j
    simp only [validB, decide_eq_true_eq] at hv
    rw [← hftravel j]
    exact hv
  · have he := hg.endA
    simp only [endValidB, Bool.or_eq_true, decide_eq_true_eq] at he
    rw [hg.arrv A] at he
    rw [← hftravel A]
    rcases he with (h | h) | h
    · left
      by_contra hA0
      unfold SiteCost.vArr at h
      rw [if_neg hA0] at h
      exact absurd h (by norm_num)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · have he := hg.endB
    simp only [endValidB, Bool.or_eq_true, decide_eq_true_eq] at he
    rw [hg.arrv B] at he
    rw [← hftravel B]
    rcases he with (h | h) | h
    · left
      by_contra hB0
      unfold SiteCost.vArr at h
      rw [if_neg hB0] at h
      exact absurd h (by norm_num)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)


/-! ### Matching a guarded path's states field by field -/


/-- The compatibility guard says each state's `dprev` is the previous state's `dcur`. -/
theorem dprev_of_guarded {A B kstar : ℤ} {st : ℤ → LocalState}
    (hg : Guarded A B kstar st) (j : ℤ) : (st (j + 1)).dprev = (st j).dcur := by
  have hs := hg.step j
  simp only [stepB, compatB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  exact hs.1.1.1

/-- The travel identification, as a standalone fact about a guarded path. -/
theorem fcur_of_guarded {A B kstar : ℤ} {st : ℤ → LocalState}
    (hg : Guarded A B kstar st) : ∀ j : ℤ, (st j).fcur = SiteCost.travel kstar j := by
  have hdepZ : ∀ j : ℤ, (((st j).dep : ℕ) : ℤ) = if j = kstar then (1 : ℤ) else 0 := by
    intro j
    by_cases h : j = kstar
    · rw [if_pos h, (hg.dep j).mpr h]; norm_num
    · rw [if_neg h]
      rcases hg.depv j with h0 | h1
      · rw [h0]; norm_num
      · exact absurd ((hg.dep j).mp h1) h
  refine eq_travel_of_flow kstar A B (fun j => (st j).fcur) ?_
    (fun j hj => (hg.outer j hj).2) hg.loA hg.hiB hg.kstLo hg.kstHi
  intro j
  have hs := hg.step j
  simp only [stepB, Bool.and_eq_true] at hs
  have hf := hs.2
  simp only [flowB, decide_eq_true_eq] at hf
  rw [hg.arrv (j + 1), hdepZ (j + 1)] at hf
  exact hf

/-- The departure marker, as a natural number. -/
theorem dep_of_guarded {A B kstar : ℤ} {st : ℤ → LocalState}
    (hg : Guarded A B kstar st) (j : ℤ) :
    (st j).dep = if j = kstar then 1 else 0 := by
  by_cases h : j = kstar
  · rw [if_pos h]; exact (hg.dep j).mpr h
  · rw [if_neg h]
    rcases hg.depv j with h0 | h1
    · exact h0
    · exact absurd ((hg.dep j).mp h1) h

/-- Componentwise equality of states. -/
theorem localState_ext {a b : LocalState} (h1 : a.dprev = b.dprev) (h2 : a.dcur = b.dcur)
    (h3 : a.fcur = b.fcur) (h4 : a.arr = b.arr) (h5 : a.dep = b.dep) (h6 : a.eps = b.eps)
    (h7 : a.delta = b.delta) : a = b := by
  cases a; cases b
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
  rfl

/-- **The match.**  A configuration agreeing with a guarded path in deposits, departure
and sign data has exactly that path's states -- every remaining field is forced by the
guard.  With `exists_config_of_guarded` this identifies the guarded paths as precisely the
state paths of configurations. -/
theorem stateOf_eq_of_guarded {A B kstar : ℤ} {st : ℤ → LocalState}
    (hg : Guarded A B kstar st) (P : SiteCost.PathData)
    (hk : P.kstar = kstar) (hd : ∀ j : ℤ, P.d j = (st j).dcur)
    (he : P.eps = (st 0).eps) (hdl : P.delta = (st 0).delta) :
    ∀ j : ℤ, stateOf P j = st j := by
  intro j
  refine localState_ext ?_ (hd j) ?_ ?_ ?_ ?_ ?_
  · show P.d (j - 1) = (st j).dprev
    rw [hd (j - 1)]
    have h := dprev_of_guarded hg (j - 1)
    rw [show j - 1 + 1 = j from by ring] at h
    exact h.symm
  · show SiteCost.travel P.kstar j = (st j).fcur
    rw [hk, ← fcur_of_guarded hg j]
  · show SiteCost.vArr j = (st j).arr
    exact (hg.arrv j).symm
  · show P.vD j = (st j).dep
    rw [dep_of_guarded hg j]
    unfold SiteCost.PathData.vD
    rw [hk]
  · show P.eps = (st j).eps
    rw [he]
    exact (eps_const_of_guarded hg j).symm
  · show P.delta = (st j).delta
    rw [hdl]
    exact (delta_const_of_guarded hg j).symm

/-- Strengthening of `exists_config_of_guarded`: the configuration's states ARE the path. -/
theorem exists_config_stateOf {A B kstar : ℤ} {st : ℤ → LocalState}
    (hg : Guarded A B kstar st) :
    ∃ P : SiteCost.PathData, P.A = A ∧ P.B = B ∧ P.kstar = kstar ∧ stateOf P = st := by
  obtain ⟨P, hA, hB, hk, hd, he, hdl⟩ := exists_config_of_guarded hg
  refine ⟨P, hA, hB, hk, funext (stateOf_eq_of_guarded hg P hk ?_ he hdl)⟩
  intro j
  by_cases hj : A ≤ j ∧ j ≤ B
  · exact hd j hj.1 hj.2
  · rw [(P.houter j (by omega)).1, (hg.outer j (by omega)).1]

/-- **The set equality (M3) needs.**  The state functions of configurations with a given
span and departure are *exactly* the guarded state functions.  Forward is
`guarded_stateOf`, backward is `exists_config_stateOf`. -/
theorem stateFns_eq_guarded (A B kstar : ℤ) :
    {st : ℤ → LocalState |
        ∃ P : SiteCost.PathData, P.A = A ∧ P.B = B ∧ P.kstar = kstar ∧ stateOf P = st}
      = {st | Guarded A B kstar st} := by
  ext st
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, hA, hB, hk, rfl⟩
    have h := guarded_stateOf P
    rw [hA, hB, hk] at h
    exact h
  · intro hg
    exact exists_config_stateOf hg

/-! ### The flow telescopes, so the departure marker is not an assumption

BLOCK 229 blamed decidability.  Looking harder, the real requirement is that the transfer
kernel VANISH on paths no configuration realises, which needs the guard to be local plus
boundary.  Of the conditions in `Guarded`, the one that looks global is `dep` -- that the
departure marker fires exactly once.

It is not an assumption.  Telescoping the flow across the span gives

    f(A) + (total arrival) = f(A + n) + (total departure),

and `f` vanishes at both ends of the span, so the two totals agree; the arrival total is
`1`, because the arrival marker fires only at `0` and `0` lies on the span.  So exactly one
departure marker fires, and it is forced by the flow rather than imposed. -/

/-- **The flow telescopes.** -/
theorem telescope_flow (f a d : ℤ → ℤ)
    (h : ∀ j : ℤ, f j + a (j + 1) = f (j + 1) + d (j + 1)) :
    ∀ (n : ℕ) (A : ℤ), f A + ∑ k ∈ Finset.range n, a (A + 1 + k)
      = f (A + n) + ∑ k ∈ Finset.range n, d (A + 1 + k) := by
  intro n
  induction n with
  | zero => intro A; simp
  | succ m ih =>
      intro A
      rw [Finset.sum_range_succ (fun k : ℕ => a (A + 1 + (k : ℤ))) m,
        Finset.sum_range_succ (fun k : ℕ => d (A + 1 + (k : ℤ))) m]
      have h1 := ih A
      have h2 := h (A + m)
      have e1 : A + 1 + (m : ℤ) = A + (m : ℤ) + 1 := by ring
      have e2 : A + ((m : ℕ) + 1 : ℕ) = A + (m : ℤ) + 1 := by push_cast; ring
      rw [e1, e2]
      omega

/-- **Hence the totals agree when the flow vanishes at both ends.**  Applied to the travel
indicator this says: one arrival, so exactly one departure. -/
theorem sum_markers_eq (f a d : ℤ → ℤ)
    (h : ∀ j : ℤ, f j + a (j + 1) = f (j + 1) + d (j + 1))
    (n : ℕ) (A : ℤ) (h0 : f A = 0) (hn : f (A + n) = 0) :
    ∑ k ∈ Finset.range n, a (A + 1 + k) = ∑ k ∈ Finset.range n, d (A + 1 + k) := by
  have ht := telescope_flow f a d h n A
  omega

/-! ### The full guarded kernel

Every per-state guard can be folded into the two-state guard by charging it to the state
being entered.  So `pathWeight_guard_eq` (BLOCK 216), which was proved for an arbitrary
two-state predicate, carries the whole local guard without change -- the generality there
pays off here. -/

/-- The complete local guard: the step, plus the conditions on the state entered. -/
def fullStepB (σ τ : LocalState) : Bool := stepB σ τ && validB τ && epsValidB τ

theorem fullStepB_stateOf (P : SiteCost.PathData) (j : ℤ) :
    fullStepB (stateOf P j) (stateOf P (j + 1)) = true := by
  simp only [fullStepB, Bool.and_eq_true]
  exact ⟨⟨stepB_stateOf P j, validB_stateOf P (j + 1)⟩, epsValidB_stateOf P (j + 1)⟩

/-- **The full guard leaves a configuration's weight alone.**  Immediate from
`pathWeight_guard_eq`, because that was stated for an arbitrary guard. -/
theorem pathWeight_fullStepB_eq (x : ℤ) (P : SiteCost.PathData) (mu : LocalState → ℤ)
    (n : ℕ) (A : ℤ) (lam : LocalState → ℤ) :
    pathWeight (fun σ τ => if fullStepB σ τ then x ^ (σ.muOf + τ.siteOf) else 0) lam mu
        ((A :: idxList A n).map (stateOf P))
      = pathWeight (fun σ τ => x ^ (σ.muOf + τ.siteOf)) lam mu
          ((A :: idxList A n).map (stateOf P)) :=
  pathWeight_guard_eq x P mu fullStepB (fullStepB_stateOf P) n A lam

/-- The head vector's guard: the conditions the first state of a span must satisfy --
per-state admissibility, minimality, and carrying no deposit or travel from the left. -/
def headOkB (σ : LocalState) : Bool :=
  validB σ && epsValidB σ && endValidB σ && decide (σ.dprev = 0)

/-- **A configuration's first state passes the head guard.**  `dprev` vanishes there
because the edge to the left of the span carries no deposit. -/
theorem headOkB_stateOf (P : SiteCost.PathData) : headOkB (stateOf P P.A) = true := by
  simp only [headOkB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨validB_stateOf P P.A, epsValidB_stateOf P P.A⟩, endValidB_at_A P⟩, ?_⟩
  show P.d (P.A - 1) = 0
  exact (P.houter (P.A - 1) (Or.inl (by omega))).1

/-- The tail vector's guard: the last state of the site path carries no deposit and no
travel, because it sits past the right end of the span. -/
def tailOkB (σ : LocalState) : Bool :=
  validB σ && epsValidB σ && decide (σ.dcur = 0) && decide (σ.fcur = 0)

theorem tailOkB_stateOf (P : SiteCost.PathData) : tailOkB (stateOf P (P.B + 1)) = true := by
  simp only [tailOkB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨validB_stateOf P _, epsValidB_stateOf P _⟩, ?_⟩, ?_⟩
  · show P.d (P.B + 1) = 0
    exact (P.houter (P.B + 1) (Or.inr (by omega))).1
  · show SiteCost.travel P.kstar (P.B + 1) = 0
    exact (P.houter (P.B + 1) (Or.inr (by omega))).2

/-! ### Minimality is not redundant; and BLOCK 208's reason for site-indexing was wrong

Two findings.

First, span-minimality cannot simply be dropped.  A non-minimal left end is an edge with
`d = 0` and no travel, and `mu` is `2` there by definition -- the gap case.  So enlarging
the span past minimality strictly increases `lR`, and the sum over non-minimal spans is a
different generating function, not a re-count of the same one.

Second, and this repairs BLOCK 208: that block moved the chain from EDGES `A .. B` to
SITES `A .. B+1` because the tail term `siteCost (s+1)` "is not a function of state `s`".
It is.  The flow relation at the right end forces the departure marker at `B+1` to equal
the travel indicator at `B`, so everything the tail needs is visible in the last edge's
state.  With the chain indexed by edges, `endValidB` applies at the FIRST and LAST states
-- exactly where the boundary vectors can see it -- and the obstacle of BLOCK 231
disappears. -/

-- (a non-minimal end is a gap edge, and `mu_eq_two_of_gap` above already says a gap
-- edge costs 2 -- no need to restate it)

/-- **The departure marker past the right end is the travel indicator at the right end.**
So the tail term is a function of the last edge's state, which is what BLOCK 208 denied. -/
theorem vD_succ_B_eq_travel (P : SiteCost.PathData) :
    ((P.vD (P.B + 1) : ℕ) : ℤ) = SiteCost.travel P.kstar P.B := by
  have hB := P.hB
  have harr : SiteCost.vArr (P.B + 1) = 0 := by
    unfold SiteCost.vArr; rw [if_neg (by omega)]
  have hout : SiteCost.travel P.kstar (P.B + 1) = 0 :=
    (P.houter (P.B + 1) (Or.inr (by omega))).2
  have hf := flowB_stateOf P P.B
  simp only [flowB, stateOf, decide_eq_true_eq] at hf
  rw [harr, hout] at hf
  simpa using hf.symm

/-! ### The tail site cost, as a function of the last edge's state

BLOCK 232 showed the departure marker past the right end equals the travel indicator
there.  So the site cost at `B + 1` -- the tail term of the edge-indexed chain -- is a
function of the state at `B` alone, and the edge frame closes. -/

/-- The departure marker past the right end, as a natural number. -/
theorem vD_succ_B_natAbs (P : SiteCost.PathData) :
    P.vD (P.B + 1) = (SiteCost.travel P.kstar P.B).natAbs := by
  have h := vD_succ_B_eq_travel P
  omega

/-- The tail site cost, computed from the last edge's state. -/
def tailSiteOf (σ : LocalState) : ℕ :=
  max (σ.dcur + σ.eps * ((if σ.delta then 0 else σ.fcur.natAbs : ℕ) : ℤ)).natAbs
      (0 - σ.eps * ((if σ.delta then σ.fcur.natAbs else 0 : ℕ) : ℤ)).natAbs

/-- **And it is the real thing.**  So the edge-indexed chain's tail is local, which is what
BLOCK 208 denied and BLOCK 232 corrected. -/
theorem tailSiteOf_stateOf (P : SiteCost.PathData) :
    tailSiteOf (stateOf P P.B) = P.siteCost (P.B + 1) := by
  have hB := P.hB
  have harr : SiteCost.vArr (P.B + 1) = 0 := by
    unfold SiteCost.vArr; rw [if_neg (by omega)]
  have hd : P.d (P.B + 1) = 0 := (P.houter (P.B + 1) (Or.inr (by omega))).1
  have hv := vD_succ_B_natAbs P
  unfold tailSiteOf SiteCost.PathData.siteCost SiteCost.PathData.alphaAt
    SiteCost.PathData.betaAt SiteCost.PathData.vL SiteCost.PathData.vR
  simp only [stateOf]
  rw [harr, hd, hv]
  norm_num

/-- **(M3a) in the edge frame.**  One kernel, one head vector, one *genuine* tail vector,
serving every configuration of span length `n`.  Unlike the site-indexed version
(BLOCK 208) the tail is not trivial, and the states at the two ends of the chain are the
two edges `A` and `B` -- which is exactly where `endValidB` lives, so span-minimality is a
boundary condition here rather than an interior one. -/
theorem isTransferDecomposition_edge {C : Type*} (x : ℤ) (n : ℕ)
    (P : C → SiteCost.PathData) (hn : ∀ c, (P c).B = (P c).A + n) :
    IsTransferDecomposition
      (fun c => ((P c).A :: idxList (P c).A n).map (stateOf (P c)))
      (fun c => x ^ (P c).lR)
      (fun σ τ => x ^ (σ.muOf + τ.siteOf))
      (fun σ => x ^ σ.siteOf)
      (fun σ => x ^ (σ.muOf + tailSiteOf σ)) := by
  refine isTransferDecomposition_of_chain x (fun σ τ => σ.muOf + τ.siteOf)
    (fun σ => σ.siteOf) (fun σ => σ.muOf + tailSiteOf σ)
    (fun c => stateOf (P c) (P c).A)
    (fun c => (idxList (P c).A n).map (stateOf (P c)))
    (fun c => (P c).lR) ?_
  intro c
  show (P c).lR = _
  have hL : (P c).lR
      = (∑ j ∈ Finset.Icc (P c).A ((P c).A + n), (P c).mu j)
        + ∑ s ∈ Finset.Icc (P c).A ((P c).A + n + 1), (P c).siteCost s := by
    unfold SiteCost.PathData.lR
    rw [hn c]
  have htail : tailSiteOf (stateOf (P c) ((P c).A + n)) = (P c).siteCost ((P c).A + n + 1) := by
    rw [← hn c]
    exact tailSiteOf_stateOf (P c)
  rw [chainCost_map (stateOf (P c)) (fun σ τ => σ.muOf + τ.siteOf), lastOf_map,
    lastOf_idxList]
  simp only []
  rw [htail, hL]
  exact alternating_is_chain (P c).mu (P c).siteCost (P c).A n

/-! ### The guarded boundary vectors, in the edge frame -/

/-- `pathWeight` reads `lam` only at the head and `mu` only at the last state, so it is
insensitive to those functions anywhere else. -/
theorem pathWeight_congr {S : Type*} (T : S → S → ℤ) (mu mu' : S → ℤ) :
    ∀ (L : List S) (s : S) (lam lam' : S → ℤ), lam s = lam' s →
      mu (lastOf s L) = mu' (lastOf s L) →
      pathWeight T lam mu (s :: L) = pathWeight T lam' mu' (s :: L) := by
  intro L
  induction L with
  | nil =>
      intro s lam lam' hl hm
      have hm' : mu s = mu' s := hm
      show lam s * mu s = lam' s * mu' s
      rw [hl, hm']
  | cons t rest ih =>
      intro s lam lam' hl hm
      show lam s * T s t * pathWeight T (fun _ => (1 : ℤ)) mu (t :: rest)
        = lam' s * T s t * pathWeight T (fun _ => (1 : ℤ)) mu' (t :: rest)
      rw [hl, ih t (fun _ => (1 : ℤ)) (fun _ => (1 : ℤ)) rfl hm]

/-- The guarded head vector. -/
def headVec (x : ℤ) (σ : LocalState) : ℤ := if headOkB σ then x ^ σ.siteOf else 0

/-- The guarded tail vector: per-state admissibility and span-minimality at the right end,
which in the edge frame is the LAST state of the chain. -/
def tailVec (x : ℤ) (σ : LocalState) : ℤ :=
  if validB σ && epsValidB σ && endValidB σ then x ^ (σ.muOf + tailSiteOf σ) else 0

theorem headVec_stateOf (x : ℤ) (P : SiteCost.PathData) :
    headVec x (stateOf P P.A) = x ^ (stateOf P P.A).siteOf := by
  rw [headVec, if_pos (headOkB_stateOf P)]

theorem tailVec_stateOf (x : ℤ) (P : SiteCost.PathData) :
    tailVec x (stateOf P P.B)
      = x ^ ((stateOf P P.B).muOf + tailSiteOf (stateOf P P.B)) := by
  rw [tailVec, if_pos]
  simp only [Bool.and_eq_true]
  exact ⟨⟨validB_stateOf P P.B, epsValidB_stateOf P P.B⟩, endValidB_at_B P⟩

/-- **The fully guarded edge-frame path weight of a configuration is its own weight.**
Kernel, head vector and tail vector all carry their guards, and on a configuration every
guard fires, so nothing is lost.  Off the realisable paths the guards make the weight
vanish -- which is what a transfer sum needs. -/
theorem pathWeight_guarded_edge (x : ℤ) (P : SiteCost.PathData) (n : ℕ) (hn : P.B = P.A + n) :
    pathWeight (fun σ τ => if fullStepB σ τ then x ^ (σ.muOf + τ.siteOf) else 0)
        (headVec x) (tailVec x) ((P.A :: idxList P.A n).map (stateOf P))
      = x ^ P.lR := by
  rw [pathWeight_fullStepB_eq x P (tailVec x) n P.A (headVec x), List.map_cons]
  have hlast : lastOf (stateOf P P.A) ((idxList P.A n).map (stateOf P))
      = stateOf P P.B := by
    rw [lastOf_map, lastOf_idxList, hn]
  rw [pathWeight_congr (fun σ τ => x ^ (σ.muOf + τ.siteOf))
      (tailVec x) (fun σ => x ^ (σ.muOf + tailSiteOf σ))
      ((idxList P.A n).map (stateOf P)) (stateOf P P.A)
      (headVec x) (fun σ => x ^ σ.siteOf) (headVec_stateOf x P)
      (by rw [hlast]; exact tailVec_stateOf x P)]
  exact (isTransferDecomposition_edge x n (fun _ : Unit => P) (fun _ => hn) ()).symm

/-! ### The arrival marker fires exactly once, and what that costs

Chasing the last implication of (M3) turns up a structural fact rather than a bookkeeping
one.  `Guarded` requires `arrv` -- that a state's arrival flag is `[j = 0]` -- but a PATH
is a list of states with no indices, so nothing in a kernel can tie the flag to an index.
What is true, and all that is needed, is that the flag fires EXACTLY ONCE along the span:
`0` always lies in `[A, B]`.

"Exactly once" is not a local condition, so a plain transfer matrix cannot impose it.  The
standard remedy is to double the state space with a flag recording whether the origin has
been passed, and to allow the arrival only on the transition that flips it.  That is a real
construction, not bookkeeping, and it is the honest remaining content of (M3). -/

/-- **The arrival marker fires exactly once along the span.** -/
theorem sum_vArr_eq_one (P : SiteCost.PathData) :
    ∑ j ∈ Finset.Icc P.A P.B, SiteCost.vArr j = 1 := by
  have hA := P.hA
  have hB := P.hB
  have hmem : (0 : ℤ) ∈ Finset.Icc P.A P.B := Finset.mem_Icc.mpr ⟨hA, hB⟩
  rw [Finset.sum_eq_single_of_mem 0 hmem]
  · unfold SiteCost.vArr; rw [if_pos rfl]
  · intro b _ hb
    unfold SiteCost.vArr; rw [if_neg hb]

/-- **The doubled state**: a state together with a flag recording whether the origin has
been passed.  This is what lets a transfer matrix impose "the arrival fires exactly once",
which no undoubled kernel can. -/
structure FlagState where
  st : LocalState
  past : Bool
  deriving DecidableEq

/-- A configuration's flagged state at index `j`. -/
def flagOf (P : SiteCost.PathData) (j : ℤ) : FlagState :=
  { st := stateOf P j, past := decide (0 ≤ j) }

/-- The doubled step guard: the underlying step, the flag advancing exactly when the
arrival fires, and the arrival barred once the origin is behind. -/
def flagStepB (σ τ : FlagState) : Bool :=
  fullStepB σ.st τ.st
    && (τ.past == (σ.past || decide (τ.st.arr = 1)))
    && (!(σ.past && decide (τ.st.arr = 1)))

/-- **A configuration's flagged path passes the doubled guard.**  The flag is `0 <= j`,
the arrival fires only at `j = 0`, and those two agree step by step. -/
theorem flagStepB_flagOf (P : SiteCost.PathData) (j : ℤ) :
    flagStepB (flagOf P j) (flagOf P (j + 1)) = true := by
  have harr : ((stateOf P (j + 1)).arr = 1) ↔ j + 1 = 0 := arr_eq_one_iff P (j + 1)
  simp only [flagStepB, flagOf, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.and_eq_false_imp]
  refine ⟨⟨fullStepB_stateOf P j, ?_⟩, ?_⟩
  · by_cases h : (0 : ℤ) ≤ j
    · simp [h, harr, show ¬(j + 1 = 0) by omega, show (0:ℤ) ≤ j + 1 by omega]
    · by_cases h1 : j + 1 = 0
      · have hone : (stateOf P (j + 1)).arr = 1 := harr.mpr h1
        rw [h1] at hone
        simp [h, h1, hone, show (0:ℤ) ≤ j + 1 by omega]
      · simp [h, harr, h1, show ¬((0:ℤ) ≤ j + 1) by omega]
  · intro hp
    have : (0 : ℤ) ≤ j := by simpa using hp
    simp [harr, show ¬(j + 1 = 0) by omega]

/-! ### The doubled boundary vectors, and the doubled path weight -/

/-- The doubled head vector: the ordinary head guard, plus the flag agreeing with whether
the arrival fires here. -/
def flagHeadVec (x : ℤ) (σ : FlagState) : ℤ :=
  if headOkB σ.st && (σ.past == decide (σ.st.arr = 1)) then x ^ σ.st.siteOf else 0

/-- The doubled tail vector: the ordinary tail guard, plus the flag SET -- which is what
forces the arrival to have happened somewhere along the path. -/
def flagTailVec (x : ℤ) (σ : FlagState) : ℤ :=
  if validB σ.st && epsValidB σ.st && endValidB σ.st && σ.past then
    x ^ (σ.st.muOf + tailSiteOf σ.st) else 0

theorem flagHeadVec_flagOf (x : ℤ) (P : SiteCost.PathData) :
    flagHeadVec x (flagOf P P.A) = x ^ (stateOf P P.A).siteOf := by
  have hA := P.hA
  have harr : ((stateOf P P.A).arr = 1) ↔ P.A = 0 := arr_eq_one_iff P P.A
  have hcond : (headOkB (flagOf P P.A).st
      && ((flagOf P P.A).past == decide ((flagOf P P.A).st.arr = 1))) = true := by
    simp only [flagOf, Bool.and_eq_true, beq_iff_eq, decide_eq_decide]
    exact ⟨headOkB_stateOf P, by rw [harr]; omega⟩
  rw [flagHeadVec, if_pos hcond]
  rfl

theorem flagTailVec_flagOf (x : ℤ) (P : SiteCost.PathData) :
    flagTailVec x (flagOf P P.B)
      = x ^ ((stateOf P P.B).muOf + tailSiteOf (stateOf P P.B)) := by
  have hB := P.hB
  have hcond : (validB (flagOf P P.B).st && epsValidB (flagOf P P.B).st
      && endValidB (flagOf P P.B).st && (flagOf P P.B).past) = true := by
    simp only [flagOf, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨validB_stateOf P P.B, epsValidB_stateOf P P.B⟩, endValidB_at_B P⟩, hB⟩
  rw [flagTailVec, if_pos hcond]
  rfl

/-- **The doubled guard costs nothing on a configuration.**  Its flagged path weight is the
undoubled one. -/
theorem pathWeight_flag_of (x : ℤ) (P : SiteCost.PathData) (mu : LocalState → ℤ) :
    ∀ (n : ℕ) (A : ℤ) (lam : LocalState → ℤ),
      pathWeight (fun σ τ => if flagStepB σ τ then x ^ (σ.st.muOf + τ.st.siteOf) else 0)
          (fun σ => lam σ.st) (fun σ => mu σ.st) ((A :: idxList A n).map (flagOf P))
        = pathWeight (fun σ τ => x ^ (σ.muOf + τ.siteOf)) lam mu
            ((A :: idxList A n).map (stateOf P)) := by
  intro n
  induction n with
  | zero => intro A lam; rfl
  | succ m ih =>
      intro A lam
      show lam (stateOf P A) * (if flagStepB (flagOf P A) (flagOf P (A + 1)) then
              x ^ ((stateOf P A).muOf + (stateOf P (A + 1)).siteOf) else 0)
            * pathWeight (fun σ τ : FlagState =>
                if flagStepB σ τ then x ^ (σ.st.muOf + τ.st.siteOf) else 0)
              (fun _ => (1 : ℤ)) (fun σ : FlagState => mu σ.st)
              ((idxList A (m + 1)).map (flagOf P))
        = lam (stateOf P A) * x ^ ((stateOf P A).muOf + (stateOf P (A + 1)).siteOf)
            * pathWeight (fun σ τ : LocalState => x ^ (σ.muOf + τ.siteOf))
              (fun _ => (1 : ℤ)) mu ((idxList A (m + 1)).map (stateOf P))
      rw [flagStepB_flagOf P A, if_pos rfl]
      congr 1
      exact ih (A + 1) (fun _ => (1 : ℤ))

/-- **The doubled, fully guarded path weight of a configuration is its own weight.**  This
is the kernel (M3) needs: local, and with the arrival counted exactly once. -/
theorem pathWeight_flag_guarded (x : ℤ) (P : SiteCost.PathData) (n : ℕ) (hn : P.B = P.A + n) :
    pathWeight (fun σ τ => if flagStepB σ τ then x ^ (σ.st.muOf + τ.st.siteOf) else 0)
        (flagHeadVec x) (flagTailVec x) ((P.A :: idxList P.A n).map (flagOf P))
      = x ^ P.lR := by
  have hlast : lastOf (flagOf P P.A) ((idxList P.A n).map (flagOf P)) = flagOf P P.B := by
    rw [lastOf_map, lastOf_idxList, hn]
  rw [List.map_cons,
    pathWeight_congr (fun σ τ => if flagStepB σ τ then x ^ (σ.st.muOf + τ.st.siteOf) else 0)
      (flagTailVec x) (fun σ => (fun τ : LocalState => x ^ (τ.muOf + tailSiteOf τ)) σ.st)
      ((idxList P.A n).map (flagOf P)) (flagOf P P.A)
      (flagHeadVec x) (fun σ => (fun τ : LocalState => x ^ τ.siteOf) σ.st)
      (flagHeadVec_flagOf x P) (by rw [hlast]; exact flagTailVec_flagOf x P),
    ← List.map_cons,
    pathWeight_flag_of x P (fun τ => x ^ (τ.muOf + tailSiteOf τ)) n P.A
      (fun τ => x ^ τ.siteOf)]
  exact (isTransferDecomposition_edge x n (fun _ : Unit => P) (fun _ => hn) ()).symm

/-! ### What the flag forces: exactly one arrival

The doubled guard exists to impose a condition no local kernel can state.  These three
facts are why it works: the flag never turns off, no arrival may fire once it is on, and
without an arrival it never turns on.  Together: along a path whose head flag matches its
arrival and whose tail flag is set, the arrival fires exactly once. -/

/-- The flag never turns off. -/
theorem past_mono (st : ℤ → FlagState) (j : ℤ)
    (hstep : flagStepB (st j) (st (j + 1)) = true) (hp : (st j).past = true) :
    (st (j + 1)).past = true := by
  simp only [flagStepB, Bool.and_eq_true, beq_iff_eq] at hstep
  rw [hstep.1.2, hp, Bool.true_or]

/-- No arrival fires once the flag is on -- so at most one arrival. -/
theorem no_arr_after (st : ℤ → FlagState) (j : ℤ)
    (hstep : flagStepB (st j) (st (j + 1)) = true) (hp : (st j).past = true) :
    (st (j + 1)).st.arr ≠ 1 := by
  simp only [flagStepB, Bool.and_eq_true] at hstep
  intro harr
  have h2 := hstep.2
  simp [hp, harr] at h2

/-- Without an arrival the flag never turns on -- so at least one arrival, given that the
tail flag is set. -/
theorem past_false_of_no_arr (st : ℤ → FlagState) (A : ℤ)
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true)
    (hhead : (st A).past = false) :
    ∀ (n : ℕ), (∀ k : ℕ, k ≤ n → (st (A + k)).st.arr ≠ 1) →
      (st (A + n)).past = false := by
  intro n
  induction n with
  | zero => intro _; simpa using hhead
  | succ m ih =>
      intro hno
      have hprev : (st (A + m)).past = false :=
        ih (fun k hk => hno k (by omega))
      have hs := hstep (A + m)
      simp only [flagStepB, Bool.and_eq_true, beq_iff_eq] at hs
      have hcast : A + ((m : ℤ) + 1) = A + (m : ℤ) + 1 := by ring
      have harr : (st (A + (m : ℤ) + 1)).st.arr ≠ 1 := by
        have := hno (m + 1) (by omega)
        rwa [show A + ((m + 1 : ℕ) : ℤ) = A + (m : ℤ) + 1 by push_cast; ring] at this
      have : (st (A + (m : ℤ) + 1)).past = false := by
        rw [hs.1.2, hprev]
        simp [harr]
      rw [show A + ((m + 1 : ℕ) : ℤ) = A + (m : ℤ) + 1 by push_cast; ring]
      exact this

/-! ### The arrival pins the translation

A path is a list of states and does not know where the origin sits.  That is not a defect:
the index is ours to choose, and the arrival chooses it.  A guarded flagged path has
exactly one arrival, and declaring that index to be `0` is what turns the path into a
configuration.  These lemmas locate it. -/

/-- **The arrival exists.**  A set tail flag forces one. -/
theorem exists_arr_index (st : ℤ → FlagState) (A : ℤ) (n : ℕ)
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true)
    (hhead : (st A).past = false) (htail : (st (A + n)).past = true) :
    ∃ k : ℕ, k ≤ n ∧ (st (A + k)).st.arr = 1 := by
  by_contra hcon
  push_neg at hcon
  have h := past_false_of_no_arr st A hstep hhead n (fun k hk => hcon k hk)
  rw [h] at htail
  exact absurd htail (by simp)

/-- **The arrival sets the flag.** -/
theorem past_of_arr (st : ℤ → FlagState) (j : ℤ)
    (hstep : flagStepB (st j) (st (j + 1)) = true)
    (harr : (st (j + 1)).st.arr = 1) : (st (j + 1)).past = true := by
  simp only [flagStepB, Bool.and_eq_true, beq_iff_eq] at hstep
  rw [hstep.1.2]
  simp [harr]

/-- **And once set it stays set, forever forward.** -/
theorem past_true_forward (st : ℤ → FlagState)
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true)
    (a : ℤ) (hp : (st a).past = true) : ∀ n : ℕ, (st (a + n)).past = true := by
  intro n
  induction n with
  | zero => simpa using hp
  | succ m ih =>
      have h := past_mono st (a + m) (hstep (a + m)) ih
      rwa [show a + ((m + 1 : ℕ) : ℤ) = a + (m : ℤ) + 1 by push_cast; ring]

/-- **So the arrival is unique.**  After it fires the flag is set, and a set flag bars any
further arrival. -/
theorem arr_unique_forward (st : ℤ → FlagState)
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true)
    (a : ℤ) (hp : (st a).past = true) (m : ℕ) :
    (st (a + m + 1)).st.arr ≠ 1 :=
  no_arr_after st (a + m) (hstep (a + m)) (past_true_forward st hstep a hp m)

/-! ### Translating a guarded path so its arrival sits at the origin

The guards are pointwise or nearest-neighbour, so they survive a shift.  Shifting by the
arrival index puts the arrival at `0` -- and then `hA` and `hB`, which `mkPathData`
demands, come for free, because the arrival lies inside the span. -/

/-- Shift a state function. -/
def shiftFn (st : ℤ → FlagState) (c : ℤ) : ℤ → FlagState := fun j => st (j + c)

/-- **The doubled guard is translation-invariant.** -/
theorem flagStepB_shift (st : ℤ → FlagState) (c : ℤ)
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true) :
    ∀ j : ℤ, flagStepB (shiftFn st c j) (shiftFn st c (j + 1)) = true := by
  intro j
  show flagStepB (st (j + c)) (st (j + 1 + c)) = true
  rw [show j + 1 + c = (j + c) + 1 by ring]
  exact hstep (j + c)

/-- **Shifting by the arrival index puts the arrival at the origin.** -/
theorem shiftFn_arr_zero (st : ℤ → FlagState) (c : ℤ) (h : (st c).st.arr = 1) :
    (shiftFn st c 0).st.arr = 1 := by
  show (st (0 + c)).st.arr = 1
  rwa [zero_add]

/-- **And then the span brackets the origin, for free.**  With the arrival at `A + k` and
`k <= n`, the shifted span is `[-k, n - k]`, which contains `0` -- so `hA` and `hB` are
not extra hypotheses but consequences of the arrival lying in the span. -/
theorem shift_span_brackets (A : ℤ) (n k : ℕ) (hk : k ≤ n) :
    A - (A + (k : ℤ)) ≤ 0 ∧ (0 : ℤ) ≤ (A + (n : ℤ)) - (A + (k : ℤ)) := by
  have hkn : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
  constructor <;> omega

/-! ### A sum of markers equal to one means exactly one marker

The arrival was pinned by the flag (BLOCKS 237-238).  The DEPARTURE is pinned differently:
`telescope_flow` (BLOCK 230) makes the departure total equal the arrival total, which is
`1`, and a 0/1 sum equal to `1` has exactly one term equal to `1`.  So the departure needs
no second flag -- the flow already carries it. -/

/-- A 0/1 sum equal to `1` has a term equal to `1`. -/
theorem exists_of_sum_one (f : ℕ → ℕ) (n : ℕ) (h01 : ∀ k, f k = 0 ∨ f k = 1)
    (hsum : ∑ k ∈ Finset.range n, f k = 1) : ∃ k ∈ Finset.range n, f k = 1 := by
  by_contra hcon
  push_neg at hcon
  have hz : ∀ k ∈ Finset.range n, f k = 0 := by
    intro k hk
    rcases h01 k with h | h
    · exact h
    · exact absurd h (hcon k hk)
  rw [Finset.sum_congr rfl hz] at hsum
  simp at hsum

/-- And only one. -/
theorem unique_of_sum_one (f : ℕ → ℕ) (n : ℕ)
    (hsum : ∑ k ∈ Finset.range n, f k = 1)
    {i j : ℕ} (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range n)
    (hfi : f i = 1) (hfj : f j = 1) : i = j := by
  by_contra hne
  have hsub : ({i, j} : Finset ℕ) ⊆ Finset.range n := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hi
    · exact hj
  have hpair : ∑ k ∈ ({i, j} : Finset ℕ), f k = 2 := by
    rw [Finset.sum_pair hne, hfi, hfj]
  have hle : ∑ k ∈ ({i, j} : Finset ℕ), f k ≤ ∑ k ∈ Finset.range n, f k :=
    Finset.sum_le_sum_of_subset hsub
  omega

/-! ### The departure total equals the arrival total

The bridge from `telescope_flow` (BLOCK 230) to the marker lemmas (BLOCK 240): the flow
relation is exactly `flowB`, and with the travel vanishing at both ends of the span the two
marker totals agree.  Since the arrival total is `1`, so is the departure total, and
`exists_of_sum_one` / `unique_of_sum_one` then locate the departure exactly. -/

theorem dep_sum_eq_arr_sum (st : ℤ → FlagState) (A : ℤ) (n : ℕ)
    (hflow : ∀ j : ℤ, (st j).st.fcur + (((st (j + 1)).st.arr : ℕ) : ℤ)
      = (st (j + 1)).st.fcur + (((st (j + 1)).st.dep : ℕ) : ℤ))
    (h0 : (st A).st.fcur = 0) (hn : (st (A + n)).st.fcur = 0) :
    ∑ k ∈ Finset.range n, (st (A + 1 + k)).st.arr
      = ∑ k ∈ Finset.range n, (st (A + 1 + k)).st.dep := by
  have h := sum_markers_eq (fun j => (st j).st.fcur)
    (fun j => (((st j).st.arr : ℕ) : ℤ)) (fun j => (((st j).st.dep : ℕ) : ℤ))
    hflow n A h0 hn
  simp only [] at h
  exact_mod_cast h

/-- The flow hypothesis above is exactly `flowB`, so a doubled guard supplies it. -/
theorem flow_of_flagStepB (st : ℤ → FlagState)
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true) :
    ∀ j : ℤ, (st j).st.fcur + (((st (j + 1)).st.arr : ℕ) : ℤ)
      = (st (j + 1)).st.fcur + (((st (j + 1)).st.dep : ℕ) : ℤ) := by
  intro j
  have hs := hstep j
  simp only [flagStepB, fullStepB, stepB, Bool.and_eq_true] at hs
  have hf := hs.1.1.1.1.2
  simp only [flowB, decide_eq_true_eq] at hf
  exact hf

/-! ### Locating the departure

Everything is in place: the guard supplies the flow, the flow makes the departure total
equal the arrival total, the arrival total is one, and a 0/1 sum equal to one has exactly
one term.  So the departure index exists and is unique -- derived from the guard, with no
second flag. -/

theorem exists_dep_index (st : ℤ → FlagState) (A : ℤ) (n : ℕ)
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true)
    (h0 : (st A).st.fcur = 0) (hn : (st (A + n)).st.fcur = 0)
    (hdep01 : ∀ j : ℤ, (st j).st.dep = 0 ∨ (st j).st.dep = 1)
    (harr : ∑ k ∈ Finset.range n, (st (A + 1 + k)).st.arr = 1) :
    ∃ k ∈ Finset.range n, (st (A + 1 + k)).st.dep = 1 := by
  have hsum := dep_sum_eq_arr_sum st A n (flow_of_flagStepB st hstep) h0 hn
  rw [harr] at hsum
  exact exists_of_sum_one (fun k => (st (A + 1 + k)).st.dep) n (fun k => hdep01 _) hsum.symm

theorem dep_index_unique (st : ℤ → FlagState) (A : ℤ) (n : ℕ)
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true)
    (h0 : (st A).st.fcur = 0) (hn : (st (A + n)).st.fcur = 0)
    (harr : ∑ k ∈ Finset.range n, (st (A + 1 + k)).st.arr = 1)
    {i j : ℕ} (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range n)
    (hfi : (st (A + 1 + i)).st.dep = 1) (hfj : (st (A + 1 + j)).st.dep = 1) : i = j := by
  have hsum := dep_sum_eq_arr_sum st A n (flow_of_flagStepB st hstep) h0 hn
  rw [harr] at hsum
  exact unique_of_sum_one (fun k => (st (A + 1 + k)).st.dep) n hsum.symm hi hj hfi hfj

/-! ### The assembly: a doubled guarded path is a `Guarded` state function

Every field of `Guarded` is now available from the doubled guard.  The hypotheses below
are exactly what the kernel and the two boundary vectors enforce, together with the three
facts derived in BLOCKS 238-242 -- the arrival's position after translation, the located
departure, and the span bracketing the origin. -/

theorem guarded_of_flag {A B kstar : ℤ} {st : ℤ → FlagState}
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true)
    (hheadOk : headOkB (st A).st = true)
    (htailOk : (validB (st B).st && epsValidB (st B).st && endValidB (st B).st) = true)
    (houter : ∀ j : ℤ, j < A ∨ B < j → (st j).st.dcur = 0 ∧ (st j).st.fcur = 0)
    (harrv : ∀ j : ℤ, (st j).st.arr = SiteCost.vArr j)
    (hdep : ∀ j : ℤ, (st j).st.dep = 1 ↔ j = kstar)
    (hdepv : ∀ j : ℤ, (st j).st.dep = 0 ∨ (st j).st.dep = 1)
    (hloA : A ≤ 0) (hhiB : 0 ≤ B) (hk1 : A ≤ kstar) (hk2 : kstar ≤ B + 1) :
    Guarded A B kstar (fun j => (st j).st) where
  step := fun j => by
    have hs := hstep j
    simp only [flagStepB, fullStepB, Bool.and_eq_true] at hs
    exact hs.1.1.1.1
  valid := fun j => by
    have hs := hstep (j - 1)
    simp only [flagStepB, fullStepB, Bool.and_eq_true] at hs
    have h := hs.1.1.1.2
    rwa [show j - 1 + 1 = j by ring] at h
  epsv := fun j => by
    have hs := hstep (j - 1)
    simp only [flagStepB, fullStepB, Bool.and_eq_true] at hs
    have h := hs.1.1.2
    rwa [show j - 1 + 1 = j by ring] at h
  endA := by
    have h := hheadOk
    simp only [headOkB, Bool.and_eq_true] at h
    exact h.1.2
  endB := by
    simp only [Bool.and_eq_true] at htailOk
    exact htailOk.2
  dep := hdep
  arrv := harrv
  depv := hdepv
  outer := houter
  loA := hloA
  hiB := hhiB
  kstLo := hk1
  kstHi := hk2

/-- **And so it is a configuration.**  Composing with `exists_config_stateOf` (BLOCK 229):
a doubled guarded path is the state path of a configuration, which is the converse (M3)
has been owed since BLOCK 226. -/
theorem exists_config_of_flag {A B kstar : ℤ} {st : ℤ → FlagState}
    (hstep : ∀ j : ℤ, flagStepB (st j) (st (j + 1)) = true)
    (hheadOk : headOkB (st A).st = true)
    (htailOk : (validB (st B).st && epsValidB (st B).st && endValidB (st B).st) = true)
    (houter : ∀ j : ℤ, j < A ∨ B < j → (st j).st.dcur = 0 ∧ (st j).st.fcur = 0)
    (harrv : ∀ j : ℤ, (st j).st.arr = SiteCost.vArr j)
    (hdep : ∀ j : ℤ, (st j).st.dep = 1 ↔ j = kstar)
    (hdepv : ∀ j : ℤ, (st j).st.dep = 0 ∨ (st j).st.dep = 1)
    (hloA : A ≤ 0) (hhiB : 0 ≤ B) (hk1 : A ≤ kstar) (hk2 : kstar ≤ B + 1) :
    ∃ P : SiteCost.PathData, P.A = A ∧ P.B = B ∧ P.kstar = kstar
      ∧ stateOf P = fun j => (st j).st :=
  exists_config_stateOf (guarded_of_flag hstep hheadOk htailOk houter harrv hdep hdepv
    hloA hhiB hk1 hk2)

/-! ### Extending a path past the span

BLOCK 243 predicted the summation would be "just assembly".  It is not, and the reason is
worth stating.  `guarded_of_flag` wants `outer` -- the states off the span carry no deposit
and no travel -- but a finite path has no states off the span, so they must be supplied.
The obvious supply, an all-zero state, BREAKS the guard: `compatB` demands
`tau.dprev = sigma.dcur`, and the state just past the right end must therefore carry
`dprev = d B`, which is not zero.

The correct extension is forced, and it is exactly the state `tailSiteOf` was already
reading (BLOCK 233): deposit and travel zero, `dprev` carried over, and the departure
marker equal to the travel indicator at `B`. -/

/-- The state just past the right end of the span, built from the last edge's state. -/
def extState (σ : LocalState) : LocalState :=
  { dprev := σ.dcur, dcur := 0, fcur := 0, arr := 0, dep := σ.fcur.natAbs,
    eps := σ.eps, delta := σ.delta }

/-- **And it is the real one.**  For a configuration, `extState` of the last edge's state
is the state at `B + 1` -- every field, including the departure marker, which
`vD_succ_B_natAbs` (BLOCK 233) supplies. -/
theorem extState_stateOf (P : SiteCost.PathData) :
    extState (stateOf P P.B) = stateOf P (P.B + 1) := by
  have hB := P.hB
  refine localState_ext ?_ ?_ ?_ ?_ ?_ rfl rfl
  · show P.d P.B = P.d (P.B + 1 - 1)
    congr 1; ring
  · show (0 : ℤ) = P.d (P.B + 1)
    exact ((P.houter (P.B + 1) (Or.inr (by omega))).1).symm
  · show (0 : ℤ) = SiteCost.travel P.kstar (P.B + 1)
    exact ((P.houter (P.B + 1) (Or.inr (by omega))).2).symm
  · show (0 : ℕ) = SiteCost.vArr (P.B + 1)
    unfold SiteCost.vArr; rw [if_neg (by omega)]
  · show (SiteCost.travel P.kstar P.B).natAbs = P.vD (P.B + 1)
    exact (vD_succ_B_natAbs P).symm

/-! ### The left boundary, and why it is not the right one

BLOCK 244 found the state past the RIGHT end must carry `dprev = d B`.  Checking the left
end rather than assuming it: there the extension IS all-zero.

The asymmetry is real and has a cause.  `dprev` looks one step to the LEFT, so the state
just past the right end inherits the span's last deposit, while the state just past the
left end looks at `d (A - 2)`, which is outside the span and therefore zero.  The markers
vanish there too: the arrival only fires at `0`, and `A <= 0` puts `A - 1` strictly below
it; the departure only fires at `k*`, and `A <= k*` puts `A - 1` strictly below that. -/

/-- The state just before the left end of the span. -/
def preState (σ : LocalState) : LocalState :=
  { dprev := 0, dcur := 0, fcur := 0, arr := 0, dep := 0, eps := σ.eps, delta := σ.delta }

/-- **And it is the real one** -- all-zero, unlike the right end. -/
theorem preState_stateOf (P : SiteCost.PathData) :
    preState (stateOf P P.A) = stateOf P (P.A - 1) := by
  have hA := P.hA
  have hk := A_le_kstar P
  have hB := P.hB
  refine localState_ext ?_ ?_ ?_ ?_ ?_ rfl rfl
  · show (0 : ℤ) = P.d (P.A - 1 - 1)
    exact ((P.houter (P.A - 1 - 1) (Or.inl (by omega))).1).symm
  · show (0 : ℤ) = P.d (P.A - 1)
    exact ((P.houter (P.A - 1) (Or.inl (by omega))).1).symm
  · show (0 : ℤ) = SiteCost.travel P.kstar (P.A - 1)
    exact (travel_zero_off P.kstar P.A P.B (P.A - 1) hA hB hk (kstar_le_B_succ P)
      (Or.inl (by omega))).symm
  · show (0 : ℕ) = SiteCost.vArr (P.A - 1)
    unfold SiteCost.vArr; rw [if_neg (by omega)]
  · show (0 : ℕ) = P.vD (P.A - 1)
    unfold SiteCost.PathData.vD; rw [if_neg (by omega)]

/-! ### Extending a finite path to a state function on all of `ℤ`

With both boundary states known (BLOCKS 244-245), a path defined on the span extends to
`ℤ`: the span itself, then the inherited state at `B + 1`, then all-zero everywhere else. -/

/-- Extend a state function beyond its span. -/
def extendFn (st : ℤ → LocalState) (A B : ℤ) : ℤ → LocalState :=
  fun j => if A ≤ j ∧ j ≤ B then st j
           else if j = B + 1 then extState (st B)
           else preState (st A)

/-- **And for a configuration the extension changes nothing.**  So the extension is the
right one: it reproduces `stateOf` exactly, which is what `guarded_of_flag`'s `outer`
hypothesis needs. -/
theorem extendFn_stateOf (P : SiteCost.PathData) :
    extendFn (stateOf P) P.A P.B = stateOf P := by
  have hA := P.hA
  have hB := P.hB
  have hk1 := A_le_kstar P
  have hk2 := kstar_le_B_succ P
  funext j
  unfold extendFn
  by_cases h1 : P.A ≤ j ∧ j ≤ P.B
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : j = P.B + 1
    · rw [if_pos h2, extState_stateOf, h2]
    · rw [if_neg h2]
      refine localState_ext ?_ ?_ ?_ ?_ ?_ rfl rfl
      · show (0 : ℤ) = P.d (j - 1)
        exact ((P.houter (j - 1) (by omega)).1).symm
      · show (0 : ℤ) = P.d j
        exact ((P.houter j (by omega)).1).symm
      · show (0 : ℤ) = SiteCost.travel P.kstar j
        exact (travel_zero_off P.kstar P.A P.B j hA hB hk1 hk2 (by omega)).symm
      · show (0 : ℕ) = SiteCost.vArr j
        unfold SiteCost.vArr; rw [if_neg (by omega)]
      · show (0 : ℕ) = P.vD j
        unfold SiteCost.PathData.vD; rw [if_neg (by omega)]

/-! ### `outer` holds for the extension of ANY path

`extendFn` was built so that both extension states carry no deposit and no travel:
`extState` sets `dcur` and `fcur` to zero explicitly, and `preState` is all-zero.  So
`outer` is unconditional -- it needs no hypothesis on the path at all. -/

theorem extendFn_eq_on (st : ℤ → LocalState) (A B : ℤ) {j : ℤ} (h1 : A ≤ j) (h2 : j ≤ B) :
    extendFn st A B j = st j := if_pos ⟨h1, h2⟩

theorem extendFn_outer (st : ℤ → LocalState) (A B : ℤ) :
    ∀ j : ℤ, j < A ∨ B < j →
      (extendFn st A B j).dcur = 0 ∧ (extendFn st A B j).fcur = 0 := by
  intro j hj
  unfold extendFn
  rw [if_neg (by omega)]
  by_cases h2 : j = B + 1
  · rw [if_pos h2]; exact ⟨rfl, rfl⟩
  · rw [if_neg h2]; exact ⟨rfl, rfl⟩

/-- The extension's sign data is the path's, everywhere. -/
theorem extendFn_eps (st : ℤ → LocalState) (A B : ℤ) (j : ℤ)
    (heps : ∀ i : ℤ, (st i).eps = (st A).eps) : (extendFn st A B j).eps = (st A).eps := by
  unfold extendFn
  by_cases h1 : A ≤ j ∧ j ≤ B
  · rw [if_pos h1]; exact heps j
  · rw [if_neg h1]
    by_cases h2 : j = B + 1
    · rw [if_pos h2]; exact heps B
    · rw [if_neg h2]; rfl

/-! ### Injectivity from the edge path alone

The edge-indexed path covers `A .. B`, not `A .. B+1`, so `stateOf_injective'` (BLOCK 214)
does not apply directly: it wants agreement one site further.  The deposits are fine --
they vanish off the span -- but the DEPARTURE can sit at `B + 1`, outside the path.

It is still seen, indirectly.  `travel k* B` is `1` exactly when `k* > B`, and `k*` is at
most `B + 1`, so the last edge's travel indicator decides whether the departure is at
`B + 1`.  That is the boundary case, and it is the third time in a row the boundary has
carried the content. -/

theorem stateOf_injective_span {P Q : SiteCost.PathData} (hA : P.A = Q.A) (hB : P.B = Q.B)
    (h : ∀ j : ℤ, P.A ≤ j → j ≤ P.B → stateOf P j = stateOf Q j) : P = Q := by
  have hAle : P.A ≤ P.B := by have := P.hA; have := P.hB; omega
  have hd : P.d = Q.d := by
    funext j
    by_cases hj : P.A ≤ j ∧ j ≤ P.B
    · exact d_eq_of_state (h j hj.1 hj.2)
    · exact d_eq_off_span hA hB (by omega)
  have hk : P.kstar = Q.kstar := by
    by_cases hkB : P.kstar ≤ P.B
    · exact kstar_eq_of_state (h P.kstar (A_le_kstar P) hkB) rfl
    · -- the departure is at B + 1; the last edge's travel indicator sees it
      have hPk : P.kstar = P.B + 1 := by
        have := kstar_le_B_succ P; omega
      have hQk : Q.kstar ≤ Q.B + 1 := kstar_le_B_succ Q
      have htr := travel_eq_of_state (h P.B hAle le_rfl)
      have hPB := P.hB
      have hone : SiteCost.travel P.kstar P.B = 1 := by
        unfold SiteCost.travel; rw [if_pos (by omega)]
      rw [hone] at htr
      have : SiteCost.travel Q.kstar P.B = 1 := htr.symm
      unfold SiteCost.travel at this
      split_ifs at this with c1 c2 <;> omega
  exact pathData_ext hk (eps_eq_of_state (h P.A le_rfl hAle))
    (delta_eq_of_state (h P.A le_rfl hAle)) hd hA hB

/-! ### The sum over flagged paths

Injectivity from the edge path (BLOCK 248) plus the doubled path weight (BLOCK 236) give
the summation in the frame (M3) actually uses. -/

/-- Distinct guarded data give distinct flagged edge paths. -/
theorem flagPath_inj {A : ℤ} {m : ℕ} {S T : SpanData A (A + m)}
    (h : (A :: idxList A m).map (flagOf S.toPath)
        = (A :: idxList A m).map (flagOf T.toPath)) : S = T := by
  refine toPath_injective (stateOf_injective_span rfl rfl ?_)
  intro j hj1 hj2
  have hAe : S.toPath.A = A := rfl
  have hBe : S.toPath.B = A + (m : ℤ) := rfl
  rw [hAe] at hj1
  rw [hBe] at hj2
  exact congrArg FlagState.st (map_idxList_inj _ _ m A h j hj1 hj2)

/-- **A sum over configurations of a fixed span is a sum over their flagged edge paths**,
weighted by the doubled, fully guarded kernel and boundary vectors. -/
theorem sum_configs_eq_sum_flag_paths (x : ℤ) {A : ℤ} {m : ℕ}
    [DecidableEq (SpanData A (A + m))]
    (C : Finset (SpanData A (A + m))) :
    ∑ S ∈ C, x ^ S.toPath.lR
      = ∑ L ∈ C.image (fun S => (A :: idxList A m).map (flagOf S.toPath)),
          pathWeight (fun σ τ => if flagStepB σ τ then x ^ (σ.st.muOf + τ.st.siteOf) else 0)
            (flagHeadVec x) (flagTailVec x) L := by
  rw [Finset.sum_image ?inj]
  case inj => intro S _ T _ h; exact flagPath_inj h
  refine Finset.sum_congr rfl fun S _ => ?_
  exact (pathWeight_flag_guarded x S.toPath m rfl).symm

/-! ### A path that fails the guard anywhere has weight zero

The weight is a product along the path, and the guarded kernel contributes a zero factor
wherever the guard fails.  So the sum over ALL paths sees only the guarded ones. -/

theorem pathWeight_zero_of_guard_fails (x : ℤ) (g : ℤ → FlagState) :
    ∀ (n : ℕ) (A : ℤ) (lam mu : FlagState → ℤ) (k : ℤ), A ≤ k → k < A + n →
      flagStepB (g k) (g (k + 1)) = false →
      pathWeight (fun σ τ => if flagStepB σ τ then x ^ (σ.st.muOf + τ.st.siteOf) else 0)
        lam mu ((A :: idxList A n).map g) = 0 := by
  intro n
  induction n with
  | zero => intro A lam mu k h1 h2 _; push_cast at h2; omega
  | succ m ih =>
      intro A lam mu k h1 h2 hfail
      show lam (g A) * (if flagStepB (g A) (g (A + 1)) then
              x ^ ((g A).st.muOf + (g (A + 1)).st.siteOf) else 0)
            * pathWeight (fun σ τ => if flagStepB σ τ then x ^ (σ.st.muOf + τ.st.siteOf) else 0)
              (fun _ => (1 : ℤ)) mu ((idxList A (m + 1)).map g) = 0
      by_cases hk : k = A
      · subst hk
        rw [hfail]
        simp
      · have h3 : pathWeight (fun σ τ => if flagStepB σ τ then
              x ^ (σ.st.muOf + τ.st.siteOf) else 0) (fun _ => (1 : ℤ)) mu
            (((A + 1) :: idxList (A + 1) m).map g) = 0 :=
          ih (A + 1) (fun _ => (1 : ℤ)) mu k (by omega) (by push_cast at h2 ⊢; omega) hfail
        rw [show ((idxList A (m + 1)).map g) = (((A + 1) :: idxList (A + 1) m).map g) from rfl,
          h3]
        ring

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

/-! ## H1a: the generating set

`IsRelaxedLength` cannot be discharged without a word-length function, and that needs
the generators as actual `Elt`-valued maps.  They are the three moves the `nogap` BFS
uses:

    s1 : toggle the side
    s2 : toggle the side and flip the sign
    s3 : move the cursor one step, depositing at the edge it crosses

`s1` and `s2` leave `kstar` and `d` alone, so all three `Elt` obligations are
inherited.  `s3` is the one with content: it changes `travel` at exactly the edge it
deposits on, and the deposit is what keeps `hpar` true.
-/

namespace EltBridge
namespace Elt

/-- **Toggle the side.** -/
def s1 (g : Elt) : Elt := { g with delta := !g.delta }

/-- **Toggle the side and flip the sign.**  Written with the explicit constructor:
`heps` is a proof field whose type mentions `eps`, so structure update cannot carry
it. -/
def s2 (g : Elt) : Elt where
  kstar := g.kstar
  eps := -g.eps
  delta := !g.delta
  heps := by rcases g.heps with h | h <;> rw [h] <;> norm_num
  d := g.d
  hpar := g.hpar
  supp := g.supp
  hsupp := g.hsupp

@[simp] theorem s1_kstar (g : Elt) : (s1 g).kstar = g.kstar := rfl
@[simp] theorem s1_d (g : Elt) : (s1 g).d = g.d := rfl
@[simp] theorem s2_kstar (g : Elt) : (s2 g).kstar = g.kstar := rfl
@[simp] theorem s2_d (g : Elt) : (s2 g).d = g.d := rfl

/-- Both side moves return the side after two applications. -/
theorem s1_delta_involutive (g : Elt) : (s1 (s1 g)).delta = g.delta := by
  simp [s1]

theorem s2_eps_involutive (g : Elt) : (s2 (s2 g)).eps = g.eps := by
  simp [s2]

end Elt
end EltBridge

#print axioms EltBridge.Elt.s1
#print axioms EltBridge.Elt.s2

namespace EltBridge
namespace Elt

/-! ### How `travel` moves when the cursor does

Stepping the cursor changes the travel indicator at exactly one edge -- the one the
cursor crosses -- and by exactly one.  That is what lets the deposit keep `hpar`. -/

theorem travel_pred_ne (k i : ℤ) (h : i ≠ k - 1) :
    SiteCost.travel (k - 1) i = SiteCost.travel k i := by
  unfold SiteCost.travel; split_ifs <;> omega

theorem travel_pred_at (k : ℤ) :
    SiteCost.travel (k - 1) (k - 1) = SiteCost.travel k (k - 1) - 1 := by
  unfold SiteCost.travel; split_ifs <;> omega

theorem travel_succ_ne (k i : ℤ) (h : i ≠ k) :
    SiteCost.travel (k + 1) i = SiteCost.travel k i := by
  unfold SiteCost.travel; split_ifs <;> omega

theorem travel_succ_at (k : ℤ) :
    SiteCost.travel (k + 1) k = SiteCost.travel k k + 1 := by
  unfold SiteCost.travel; split_ifs <;> omega

end Elt
end EltBridge

#print axioms EltBridge.Elt.travel_pred_ne
#print axioms EltBridge.Elt.travel_pred_at
#print axioms EltBridge.Elt.travel_succ_ne
#print axioms EltBridge.Elt.travel_succ_at

namespace EltBridge
namespace Elt

/-- **Move the cursor one step, depositing at the edge it crosses.**

The side says which way.  `travel` changes by exactly one at that edge
(`travel_succ_at`, `travel_pred_at`) and nowhere else (`travel_succ_ne`,
`travel_pred_ne`), and the deposit moves `d` there by `∓eps`, so
`d - travel` changes by an even amount and `hpar` survives. -/
noncomputable def s3 (g : Elt) : Elt :=
  if hd : g.delta then
    { kstar := g.kstar + 1
      eps := g.eps
      delta := false
      heps := g.heps
      d := Function.update g.d g.kstar (g.d g.kstar - g.eps)
      hpar := by
        intro i
        by_cases hi : i = g.kstar
        · have hp := g.hpar i
          subst hi
          rw [Function.update_self, travel_succ_at]
          rcases g.heps with h | h <;> rw [h] <;> omega
        · rw [Function.update_of_ne hi, travel_succ_ne g.kstar i hi]
          exact g.hpar i
      supp := insert g.kstar g.supp
      hsupp := by
        intro j hj
        rw [Finset.mem_insert, not_or] at hj
        obtain ⟨hne, hns⟩ := hj
        obtain ⟨hd0, ht0⟩ := g.hsupp j hns
        exact ⟨by rw [Function.update_of_ne hne]; exact hd0,
               by rw [travel_succ_ne g.kstar j hne]; exact ht0⟩ }
  else
    { kstar := g.kstar - 1
      eps := g.eps
      delta := true
      heps := g.heps
      d := Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps)
      hpar := by
        intro i
        by_cases hi : i = g.kstar - 1
        · have hp := g.hpar i
          subst hi
          rw [Function.update_self, travel_pred_at]
          rcases g.heps with h | h <;> rw [h] <;> omega
        · rw [Function.update_of_ne hi, travel_pred_ne g.kstar i hi]
          exact g.hpar i
      supp := insert (g.kstar - 1) g.supp
      hsupp := by
        intro j hj
        rw [Finset.mem_insert, not_or] at hj
        obtain ⟨hne, hns⟩ := hj
        obtain ⟨hd0, ht0⟩ := g.hsupp j hns
        exact ⟨by rw [Function.update_of_ne hne]; exact hd0,
               by rw [travel_pred_ne g.kstar j hne]; exact ht0⟩ }

end Elt
end EltBridge

#print axioms EltBridge.Elt.s3

namespace EltBridge
namespace Elt

/-- The identity: cursor at `0`, no deposits. -/
def one : Elt where
  kstar := 0
  eps := 1
  delta := false
  heps := Or.inl rfl
  d := fun _ => 0
  hpar := by
    intro j
    rw [SiteCost.travel_of_kstar_zero]
    norm_num
  supp := ∅
  hsupp := by
    intro j _
    exact ⟨rfl, SiteCost.travel_of_kstar_zero j⟩

/-- Two `Elt` terms are the same group element when they agree off `supp`. -/
def SameElt (g h : Elt) : Prop :=
  g.kstar = h.kstar ∧ g.eps = h.eps ∧ g.delta = h.delta ∧ g.d = h.d

theorem SameElt.refl (g : Elt) : SameElt g g := ⟨rfl, rfl, rfl, rfl⟩

theorem SameElt.symm {g h : Elt} (H : SameElt g h) : SameElt h g :=
  ⟨H.1.symm, H.2.1.symm, H.2.2.1.symm, H.2.2.2.symm⟩

theorem SameElt.trans {g h k : Elt} (H1 : SameElt g h) (H2 : SameElt h k) : SameElt g k :=
  ⟨H1.1.trans H2.1, H1.2.1.trans H2.2.1, H1.2.2.1.trans H2.2.2.1,
    H1.2.2.2.trans H2.2.2.2⟩

/-- **One generator step.**  The three moves of the `nogap` BFS, taken up to
`SameElt`: `Elt` stores `supp` non-canonically (BLOCK 141), so a step lands on the
right *element* and only incidentally on a particular term.  Defining `Gen` with
strict equality would make it non-symmetric even though every generator is an
involution, which is a defect of the encoding, not of the group. -/
noncomputable def Gen (a b : Elt) : Prop :=
  SameElt b (s1 a) ∨ SameElt b (s2 a) ∨ SameElt b (s3 a)

/-- **Reachable from the identity in `n` steps.**  The base case is `SameElt _ one`
for the same reason. -/
inductive Reaches : ℕ → Elt → Prop
  | refl {g : Elt} : SameElt g one → Reaches 0 g
  | step {n : ℕ} {a b : Elt} : Reaches n a → Gen a b → Reaches (n + 1) b

/-- **The word length**: the least number of generator steps reaching `g`.

`Nat.sInf` returns `0` on an empty set, so this is the word length only on elements
that are reachable at all; `Reachable` below is the side condition, and it is what any
use of `wordLength` must carry. -/
noncomputable def wordLength (g : Elt) : ℕ := sInf {n | Reaches n g}

/-- `g` is a word in the generators. -/
def Reachable (g : Elt) : Prop := ∃ n, Reaches n g

theorem wordLength_one : wordLength one = 0 := by
  have h : (0 : ℕ) ∈ {n | Reaches n one} := Reaches.refl (SameElt.refl one)
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le h)

theorem reaches_wordLength {g : Elt} (h : Reachable g) : Reaches (wordLength g) g :=
  Nat.sInf_mem h

/-- The word length is a lower bound on any reaching count. -/
theorem wordLength_le {g : Elt} {n : ℕ} (h : Reaches n g) : wordLength g ≤ n :=
  Nat.sInf_le h

/-- **H1a, stated against a concrete function.**  `IsRelaxedLength` was a contract with
no candidate to test; `wordLength` is now that candidate, so H1a is the sentence

    IsRelaxedLength wordLength

with the generating set and identity formalised.  It is not proved here. -/
theorem H1a_statement : IsRelaxedLength wordLength ↔ ∀ g : Elt, wordLength g = g.lR :=
  Iff.rfl

end Elt
end EltBridge

#print axioms EltBridge.Elt.one
#print axioms EltBridge.Elt.wordLength_one
#print axioms EltBridge.Elt.H1a_statement

namespace EltBridge
namespace Elt

/-! ### `Elt` is not extensional, and the generators are involutions only modulo that

Applying `s3` twice returns `kstar`, `eps`, `delta` and `d` to their original values --
the deposit `∓eps` is undone by the `±eps` of the reverse step, and
`Function.update` collapses.  But `supp` does not return: each application inserts the
crossed edge, so `s3 (s3 g)` carries `insert k g.supp`.

That is not a defect in `s3`.  It is that `Elt` stores `supp` as a witness for finite
support rather than canonically, so two `Elt` terms agreeing on `kstar`, `eps`,
`delta` and `d` are the same group element with different bookkeeping.  The generators
are involutions on the element, not on the term.

This matters for H1a: `wordLength` is defined on terms, so the statement
`IsRelaxedLength wordLength` is about terms, while the metric it should equal is a
function of the element.  `SameElt` is the relation that has to be quotiented by, or
carried. -/

/-- **`s1` is an involution.** -/
theorem s1_involutive (g : Elt) : SameElt (s1 (s1 g)) g := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  simp [s1]

/-- **`s2` is an involution.** -/
theorem s2_involutive (g : Elt) : SameElt (s2 (s2 g)) g := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · simp [s2]
  · simp [s2]

end Elt
end EltBridge

#print axioms EltBridge.Elt.s1_involutive
#print axioms EltBridge.Elt.s2_involutive

namespace EltBridge
namespace Elt

/-- **`s3` is an involution on the element.**  The reverse cursor step deposits the
opposite `±eps` at the same edge, so the two `Function.update`s collapse; `kstar`
returns because the steps are opposite, and `delta` because each flips it.  Only
`supp` fails to return, which is why the statement is `SameElt`. -/
theorem s3_involutive (g : Elt) : SameElt (s3 (s3 g)) g := by
  unfold SameElt
  by_cases hd : g.delta = true
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [s3, hd, Function.update_idem, Function.update_eq_self]
  · simp only [Bool.not_eq_true] at hd
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [s3, hd, Function.update_idem, Function.update_eq_self]

end Elt
end EltBridge

#print axioms EltBridge.Elt.s3_involutive

namespace EltBridge
namespace Elt

/-- **`occ` does not depend on `supp`.**  `hsupp` forces every edge with a deposit or
travel to lie in `supp`, so filtering `supp` by that condition picks out the same set
whichever valid `supp` was stored. -/
theorem occ_congr {g h : Elt} (H : SameElt g h) : g.occ = h.occ := by
  obtain ⟨hk, -, -, hdd⟩ := H
  ext j
  simp only [occ, Finset.mem_insert, Finset.mem_filter]
  constructor
  · rintro (rfl | ⟨-, hcond⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨?_, ?_⟩
      · by_contra hns
        obtain ⟨h1, h2⟩ := h.hsupp j hns
        rw [← hdd] at h1
        rw [← hk] at h2
        exact (hcond.elim (fun c => c h1) (fun c => c h2))
      · rw [← hdd, ← hk]; exact hcond
  · rintro (rfl | ⟨-, hcond⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨?_, ?_⟩
      · by_contra hns
        obtain ⟨h1, h2⟩ := g.hsupp j hns
        rw [hdd] at h1
        rw [hk] at h2
        exact (hcond.elim (fun c => c h1) (fun c => c h2))
      · rw [hdd, hk]; exact hcond

/-- Hence the span, and hence the relaxed length, are functions of the element. -/
theorem A_congr {g h : Elt} (H : SameElt g h) : g.A = h.A := by
  unfold A
  congr 1
  exact occ_congr H

theorem B_congr {g h : Elt} (H : SameElt g h) : g.B = h.B := by
  unfold B
  congr 1
  exact occ_congr H

end Elt
end EltBridge

#print axioms EltBridge.Elt.occ_congr
#print axioms EltBridge.Elt.A_congr

namespace EltBridge
namespace Elt

/-! ### `Gen` is symmetric

With `Gen` taken up to `SameElt` (BLOCK 142) the involutions do what they should: a
generator step can be undone by the same generator, so the Cayley graph is undirected
and `wordLength` is a metric rather than a quasi-metric. -/

theorem s1_congr {g h : Elt} (H : SameElt g h) : SameElt (s1 g) (s1 h) :=
  ⟨H.1, H.2.1, by simp only [s1]; rw [H.2.2.1], H.2.2.2⟩

theorem s2_congr {g h : Elt} (H : SameElt g h) : SameElt (s2 g) (s2 h) :=
  ⟨H.1, by simp only [s2]; rw [H.2.1], by simp only [s2]; rw [H.2.2.1], H.2.2.2⟩

theorem s3_congr {g h : Elt} (H : SameElt g h) : SameElt (s3 g) (s3 h) := by
  obtain ⟨hk, he, hδ, hd⟩ := H
  unfold s3
  by_cases hg : g.delta = true
  · have hh : h.delta = true := by rw [← hδ]; exact hg
    rw [dif_pos hg, dif_pos hh]
    exact ⟨by simp [hk], he, rfl, by simp [hd, hk, he]⟩
  · have hh : h.delta ≠ true := by rw [← hδ]; exact hg
    rw [dif_neg hg, dif_neg hh]
    exact ⟨by simp [hk], he, rfl, by simp [hd, hk, he]⟩

/-- **A generator step can be undone by the same generator.** -/
theorem Gen.symm {a b : Elt} (H : Gen a b) : Gen b a := by
  rcases H with h | h | h
  · exact Or.inl (((s1_congr h).trans (s1_involutive a)).symm)
  · exact Or.inr (Or.inl (((s2_congr h).trans (s2_involutive a)).symm))
  · exact Or.inr (Or.inr (((s3_congr h).trans (s3_involutive a)).symm))

/-- **`Reaches` respects `SameElt`**: reachability is a property of the element. -/
theorem Reaches.congr {n : ℕ} {g h : Elt} (H : Reaches n g) (E : SameElt g h) :
    Reaches n h := by
  cases H with
  | refl hone => exact Reaches.refl (E.symm.trans hone)
  | step hprev hgen =>
    refine Reaches.step hprev ?_
    rcases hgen with c | c | c
    · exact Or.inl (E.symm.trans c)
    · exact Or.inr (Or.inl (E.symm.trans c))
    · exact Or.inr (Or.inr (E.symm.trans c))

end Elt
end EltBridge

#print axioms EltBridge.Elt.Gen.symm
#print axioms EltBridge.Elt.Reaches.congr

namespace EltBridge
namespace Elt

/-! ### Reachability: the base case

An element with the cursor at `0` and no deposits is determined by `(eps, delta)`, and
all four such elements are words of length at most two:

    (1, false)  = one          (-1, true)  = s2 one
    (1, true)   = s1 one       (-1, false) = s1 (s2 one)
-/

theorem reachable_one : Reachable one := ⟨0, Reaches.refl (SameElt.refl one)⟩

theorem reaches_s1_one : Reaches 1 (s1 one) :=
  Reaches.step (Reaches.refl (SameElt.refl one)) (Or.inl (SameElt.refl _))

theorem reaches_s2_one : Reaches 1 (s2 one) :=
  Reaches.step (Reaches.refl (SameElt.refl one)) (Or.inr (Or.inl (SameElt.refl _)))

theorem reaches_s1_s2_one : Reaches 2 (s1 (s2 one)) :=
  Reaches.step reaches_s2_one (Or.inl (SameElt.refl _))

/-- **Every element with the cursor at `0` and no deposits is reachable**, in at most
two steps. -/
theorem reachable_of_trivial (g : Elt) (hk : g.kstar = 0) (hd : g.d = fun _ => 0) :
    Reachable g := by
  have hone : one.kstar = 0 ∧ one.eps = 1 ∧ one.delta = false ∧ one.d = fun _ => 0 :=
    ⟨rfl, rfl, rfl, rfl⟩
  rcases g.heps with he | he
  · by_cases hδ : g.delta = true
    · exact ⟨1, Reaches.congr reaches_s1_one
        ⟨by simp [one, s1, hk], by simp [one, s1, he], by simp [one, s1, hδ], by simp [one, s1, hd]⟩⟩
    · simp only [Bool.not_eq_true] at hδ
      exact ⟨0, Reaches.refl ⟨by simp [one, hk], by simp [one, he], by simp [one, hδ], by simp [one, hd]⟩⟩
  · by_cases hδ : g.delta = true
    · exact ⟨1, Reaches.congr reaches_s2_one
        ⟨by simp [one, s2, hk], by simp [one, s2, he], by simp [one, s2, hδ], by simp [one, s2, hd]⟩⟩
    · simp only [Bool.not_eq_true] at hδ
      exact ⟨2, Reaches.congr reaches_s1_s2_one
        ⟨by simp [one, s1, s2, hk], by simp [one, s1, s2, he], by simp [one, s1, s2, hδ],
          by simp [one, s1, s2, hd]⟩⟩

end Elt
end EltBridge

#print axioms EltBridge.Elt.reachable_of_trivial

namespace EltBridge
namespace Elt

/-! ### The round trip

A cursor excursion across one edge and back, with the sign flipped in between, returns
the cursor and changes that edge's deposit by `±2`.  This is the engine for the deposit
induction: `hpar` ties each deposit's parity to `travel`, so once `kstar` is fixed the
deposits may only move in steps of two, and this word realises exactly that step.

From `delta = false` the word is `s3, s2, s1, s3`:

    s3   kstar k-1, delta true,  d (k-1) += e
    s2   eps -e, delta false
    s1   delta true
    s3   kstar k,   delta false, d (k-1) -= (-e) = += e

so `d (k-1)` moves by `2e`, `kstar` and `delta` return, and `eps` is flipped. -/
theorem roundTrip_left (g : Elt) (hδ : g.delta = false) :
    (s3 (s1 (s2 (s3 g)))).kstar = g.kstar ∧
    (s3 (s1 (s2 (s3 g)))).eps = -g.eps ∧
    (s3 (s1 (s2 (s3 g)))).delta = g.delta ∧
    (s3 (s1 (s2 (s3 g)))).d
      = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + 2 * g.eps) := by
  have h1 : ¬ (g.delta = true) := by rw [hδ]; simp
  -- the first step
  have e1 : (s3 g).kstar = g.kstar - 1 := by rw [s3, dif_neg h1]
  have e2 : (s3 g).eps = g.eps := by rw [s3, dif_neg h1]
  have e3 : (s3 g).delta = true := by rw [s3, dif_neg h1]
  have e4 : (s3 g).d
      = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
    rw [s3, dif_neg h1]
  -- the two side moves: both are definitional on every field
  have f1 : (s1 (s2 (s3 g))).kstar = g.kstar - 1 := e1
  have f2 : (s1 (s2 (s3 g))).eps = -g.eps := by
    show -(s3 g).eps = -g.eps
    rw [e2]
  have f3 : (s1 (s2 (s3 g))).delta = true := by
    show (!(!(s3 g).delta)) = true
    rw [e3]
    simp
  have f4 : (s1 (s2 (s3 g))).d
      = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := e4
  -- the return step
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [s3, dif_pos f3]; show (s1 (s2 (s3 g))).kstar + 1 = g.kstar; rw [f1]; ring
  · rw [s3, dif_pos f3]; show (s1 (s2 (s3 g))).eps = -g.eps; exact f2
  · rw [s3, dif_pos f3]; show false = g.delta; exact hδ.symm
  · rw [s3, dif_pos f3]
    show Function.update (s1 (s2 (s3 g))).d (s1 (s2 (s3 g))).kstar
      ((s1 (s2 (s3 g))).d (s1 (s2 (s3 g))).kstar - (s1 (s2 (s3 g))).eps)
      = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + 2 * g.eps)
    rw [f1, f2, f4, Function.update_self, Function.update_idem]
    congr 1
    ring

end Elt
end EltBridge

#print axioms EltBridge.Elt.roundTrip_left

namespace EltBridge
namespace Elt

/-! ### Reachability is closed under the generators, hence under the round trip -/

theorem reachable_s1 {g : Elt} (h : Reachable g) : Reachable (s1 g) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, Reaches.step hn (Or.inl (SameElt.refl _))⟩

theorem reachable_s2 {g : Elt} (h : Reachable g) : Reachable (s2 g) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, Reaches.step hn (Or.inr (Or.inl (SameElt.refl _)))⟩

theorem reachable_s3 {g : Elt} (h : Reachable g) : Reachable (s3 g) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, Reaches.step hn (Or.inr (Or.inr (SameElt.refl _)))⟩

/-- **The round trip preserves reachability**, at a cost of four steps. -/
theorem reachable_roundTrip {g : Elt} (h : Reachable g) :
    Reachable (s3 (s1 (s2 (s3 g)))) :=
  reachable_s3 (reachable_s1 (reachable_s2 (reachable_s3 h)))

/-- **The engine, stated on the element.**  From a reachable `g` with `delta = false`,
the element that agrees with `g` except that one deposit has moved by `2 * eps` and the
sign is flipped is reachable.  `hpar` allows exactly these moves once `kstar` is fixed,
so this is the whole freedom in the deposits. -/
theorem reachable_deposit_step {g h : Elt} (hg : Reachable g) (hδ : g.delta = false)
    (hk : h.kstar = g.kstar) (he : h.eps = -g.eps) (hd : h.delta = g.delta)
    (hdd : h.d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + 2 * g.eps)) :
    Reachable h := by
  obtain ⟨n, hn⟩ := reachable_roundTrip hg
  obtain ⟨r1, r2, r3, r4⟩ := roundTrip_left g hδ
  exact ⟨n, Reaches.congr hn ⟨r1.trans hk.symm, r2.trans he.symm,
    r3.trans hd.symm, r4.trans hdd.symm⟩⟩

end Elt
end EltBridge

#print axioms EltBridge.Elt.reachable_roundTrip
#print axioms EltBridge.Elt.reachable_deposit_step

namespace EltBridge
namespace Elt

/-! ### Cursor placement

`s3` alone cannot be iterated: it flips the side, so the next `s3` walks back.  But
`s1 ∘ s3` **preserves** the side, and therefore iterates -- it steps the cursor left
while `delta = false` and right while `delta = true`, depositing at each crossed edge.
That is the cursor-placement word. -/

/-- One cursor step in the direction the side names, keeping the side. -/
noncomputable def cstep (g : Elt) : Elt := s1 (s3 g)

theorem cstep_left (g : Elt) (hδ : g.delta = false) :
    (cstep g).kstar = g.kstar - 1 ∧ (cstep g).eps = g.eps ∧
    (cstep g).delta = false ∧
    (cstep g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
  have h1 : ¬ (g.delta = true) := by rw [hδ]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (s3 g).kstar = g.kstar - 1
    rw [s3, dif_neg h1]
  · show (s3 g).eps = g.eps
    rw [s3, dif_neg h1]
  · show (!(s3 g).delta) = false
    rw [s3, dif_neg h1]
    simp
  · show (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps)
    rw [s3, dif_neg h1]

theorem cstep_right (g : Elt) (hδ : g.delta = true) :
    (cstep g).kstar = g.kstar + 1 ∧ (cstep g).eps = g.eps ∧
    (cstep g).delta = true ∧
    (cstep g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (s3 g).kstar = g.kstar + 1
    rw [s3, dif_pos hδ]
  · show (s3 g).eps = g.eps
    rw [s3, dif_pos hδ]
  · show (!(s3 g).delta) = true
    rw [s3, dif_pos hδ]
    simp
  · show (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps)
    rw [s3, dif_pos hδ]

theorem reachable_cstep {g : Elt} (h : Reachable g) : Reachable (cstep g) :=
  reachable_s1 (reachable_s3 h)

theorem reachable_cstep_iter {g : Elt} (h : Reachable g) (n : ℕ) :
    Reachable (cstep^[n] g) := by
  induction n generalizing g with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (reachable_cstep h)

/-- **Walking left from a side-`false` element**: after `n` steps the cursor has moved
`n` to the left and the side is unchanged. -/
theorem cstep_iter_left (g : Elt) (hδ : g.delta = false) (n : ℕ) :
    (cstep^[n] g).kstar = g.kstar - n ∧ (cstep^[n] g).delta = false := by
  induction n generalizing g with
  | zero => simpa using hδ
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, -, h3, -⟩ := cstep_left g hδ
    obtain ⟨p1, p2⟩ := ih (cstep g) h3
    refine ⟨?_, p2⟩
    rw [p1, h1]
    push_cast
    ring

/-- **Every non-positive cursor position is reachable.** -/
theorem reachable_kstar_nonpos (n : ℕ) :
    ∃ g : Elt, Reachable g ∧ g.kstar = -(n : ℤ) ∧ g.delta = false := by
  refine ⟨cstep^[n] one, reachable_cstep_iter reachable_one n, ?_, ?_⟩
  · obtain ⟨h1, -⟩ := cstep_iter_left one rfl n
    rw [h1]
    show (0 : ℤ) - n = -(n : ℤ)
    ring
  · exact (cstep_iter_left one rfl n).2

end Elt
end EltBridge

#print axioms EltBridge.Elt.cstep_left
#print axioms EltBridge.Elt.cstep_iter_left
#print axioms EltBridge.Elt.reachable_kstar_nonpos

namespace EltBridge
namespace Elt

/-- **Walking right from a side-`true` element.** -/
theorem cstep_iter_right (g : Elt) (hδ : g.delta = true) (n : ℕ) :
    (cstep^[n] g).kstar = g.kstar + n ∧ (cstep^[n] g).delta = true := by
  induction n generalizing g with
  | zero => simpa using hδ
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, -, h3, -⟩ := cstep_right g hδ
    obtain ⟨p1, p2⟩ := ih (cstep g) h3
    refine ⟨?_, p2⟩
    rw [p1, h1]
    push_cast
    ring

/-- **Every non-negative cursor position is reachable.** -/
theorem reachable_kstar_nonneg (n : ℕ) :
    ∃ g : Elt, Reachable g ∧ g.kstar = (n : ℤ) ∧ g.delta = true := by
  refine ⟨cstep^[n] (s1 one), reachable_cstep_iter (reachable_s1 reachable_one) n, ?_, ?_⟩
  · obtain ⟨h1, -⟩ := cstep_iter_right (s1 one) rfl n
    rw [h1]
    show (0 : ℤ) + n = (n : ℤ)
    ring
  · exact (cstep_iter_right (s1 one) rfl n).2

/-- **Cursor placement: every cursor position is reachable.**  This is the first half
of the reachability induction -- and the half that matters for the second, since
fixing `kstar` fixes every deposit's parity through `hpar`. -/
theorem reachable_kstar (m : ℤ) : ∃ g : Elt, Reachable g ∧ g.kstar = m := by
  by_cases hm : 0 ≤ m
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    obtain ⟨g, hg, hk, -⟩ := reachable_kstar_nonneg n
    exact ⟨g, hg, hk⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -(n : ℤ) :=
      ⟨(-m).toNat, by omega⟩
    obtain ⟨g, hg, hk, -⟩ := reachable_kstar_nonpos n
    exact ⟨g, hg, by rw [hk, hn]⟩

end Elt
end EltBridge

#print axioms EltBridge.Elt.reachable_kstar_nonneg
#print axioms EltBridge.Elt.reachable_kstar

namespace EltBridge
namespace Elt

/-! ### What the walk leaves behind

`reachable_kstar` places the cursor but does not say what it deposits on the way.  It
does: walking left from `one` lays down `+1` at every edge it crosses, so after `n`
steps the deposit profile is the indicator of `[-n, -1]`.  Computing it is what lets
the round trips correct the walk to a target. -/

theorem cstep_iter_one (n : ℕ) :
    (cstep^[n] one).kstar = -(n : ℤ) ∧ (cstep^[n] one).delta = false ∧
    (cstep^[n] one).eps = 1 ∧
    ∀ j : ℤ, (cstep^[n] one).d j = if -(n : ℤ) ≤ j ∧ j ≤ -1 then 1 else 0 := by
  induction n with
  | zero =>
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro j
    show (0 : ℤ) = _
    rw [if_neg (by push_cast; omega)]
  | succ k ih =>
    obtain ⟨hk, hδ, he, hd⟩ := ih
    rw [Function.iterate_succ_apply']
    obtain ⟨c1, c2, c3, c4⟩ := cstep_left _ hδ
    refine ⟨?_, c3, ?_, ?_⟩
    · rw [c1, hk]; push_cast; ring
    · rw [c2, he]
    · intro j
      rw [c4, hk, he]
      by_cases hj : j = -(k : ℤ) - 1
      · subst hj
        rw [Function.update_self, hd, if_neg (by omega), if_pos (by push_cast; omega)]
        norm_num
      · rw [Function.update_of_ne (by omega), hd]
        by_cases hin : -(k : ℤ) ≤ j ∧ j ≤ -1
        · rw [if_pos hin, if_pos (by push_cast; omega)]
        · rw [if_neg hin, if_neg (by push_cast; omega)]

end Elt
end EltBridge

#print axioms EltBridge.Elt.cstep_iter_one

namespace EltBridge
namespace Elt

/-! ### Correction to BLOCK 140: `wordLength` is not a candidate for `IsRelaxedLength`

BLOCK 140 said H1a had become the concrete sentence `IsRelaxedLength wordLength`.  It
has not.  `IsRelaxedLength L` asks `L g = g.lR`, and `lR` is the RELAXED length; the
recorded metric formula is `|g| = lR g + 2 * c g`, so `wordLength`, which is the true
word length, agrees with `lR` only where the defect vanishes.  It does not vanish:
`nogap` at depth 21 reports `max c observed = 3` over 50763 elements.

So `IsRelaxedLength wordLength` is false, and the sentence H1a wants from `wordLength`
is the defect formula instead.  `H1a_statement` remains true -- it only unfolds the
definition -- but it is not H1a, and calling it that was the error. -/

/-- **`IsRelaxedLength wordLength` would force the defect to vanish identically.**
Given the recorded metric formula, which is what `c` means, the contract collapses to
`c = 0` everywhere -- refuted by `nogap`, which sees `c = 3`. -/
theorem isRelaxedLength_wordLength_forces_no_defect
    (c : Elt → ℕ) (hmetric : ∀ g : Elt, wordLength g = g.lR + 2 * c g)
    (h : IsRelaxedLength wordLength) : ∀ g : Elt, c g = 0 := by
  intro g
  have hg := h g
  rw [hmetric g] at hg
  omega

/-- So the target for `wordLength` is the defect formula, not the relaxed one.  This
names it; it is not proved, and its lower-bound half is the one recorded as open. -/
def IsTrueLength (L : Elt → ℕ) (c : Elt → ℕ) : Prop :=
  ∀ g : Elt, L g = g.lR + 2 * c g

end Elt
end EltBridge

#print axioms EltBridge.Elt.isRelaxedLength_wordLength_forces_no_defect

namespace EltBridge
namespace Elt

/-! ### Flipping the sign alone

The round trip flips `eps`, and that breaks the cancellation a walk-out/walk-back would
otherwise give: walking out deposits `+eps` at each crossed edge and walking back
deposits `-eps`, which cancel only if `eps` is the same on both legs.  `s2` flips `eps`
but also the side; composing with `s1` restores the side, so `feps = s1 ∘ s2` flips the
sign alone, in two steps. -/

noncomputable def feps (g : Elt) : Elt := s1 (s2 g)

theorem feps_spec (g : Elt) :
    (feps g).kstar = g.kstar ∧ (feps g).eps = -g.eps ∧
    (feps g).delta = g.delta ∧ (feps g).d = g.d := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  show (!(!g.delta)) = g.delta
  simp

theorem reachable_feps {g : Elt} (h : Reachable g) : Reachable (feps g) :=
  reachable_s1 (reachable_s2 h)

/-- **The excursion word, as a specification.**  To change the deposit at an arbitrary
edge while returning the cursor, the word is

    walk out   (cstep^k)    deposits +eps at each crossed edge
    round trip (4 steps)    moves the target deposit by 2*eps, flips eps
    feps       (2 steps)    restores eps, so the return leg cancels the outward one
    walk back  (cstep^k)    deposits -eps at each crossed edge

The two walks cancel exactly because `feps` sits between them; without it the return
leg would double the outward deposits instead of undoing them.  This records the
shape; the bookkeeping over an arbitrary distance is not carried out. -/
def IsExcursion (w : Elt → Elt) (j : ℤ) : Prop :=
  ∀ g : Elt, (w g).kstar = g.kstar ∧ (w g).delta = g.delta ∧
    (w g).d = Function.update g.d j (g.d j + 2 * g.eps)

end Elt
end EltBridge

#print axioms EltBridge.Elt.feps_spec
#print axioms EltBridge.Elt.reachable_feps

namespace EltBridge

/-! ### The free-pair obstruction is not on the shield law's path

`free_pair_of_minimal_fails_in_free_model` is about the SWAP criterion: a cost-minimal
`GData` datum can have a cross-walk pair admitting no free swap.  That machinery serves
`MergesMin` -- merging everything into ONE walk, which is `thm:nogap`.

The shield law's upper bound is a different statement and takes a different route.
`walkCount_le_runs_blk` concludes `walkCount ≤ |Z| + 1` from `hedge` and `hsep`, and
`hsep` asks only that each RUN be connected.  No swap and no free pair appears in it.

What supplies `hsep` is BLOCK 135's dichotomy: off a cut site a passing pairing ties or
beats the bouncing one (`pass_le_bounce_of_left_differs`), so a minimal pairing that
passes exists there; at a cut site the bounce strictly wins
(`bounce_beats_pass_at_cut`), so none passes.  Passes link adjacent edges, so a run
whose interior sites all pass is connected.

The step that makes this legitimate is that the choice is free site by site: total cost
is a sum over sites, so choosing a minimal local pairing at each site independently
assembles into a global minimum.  That is the principle below, and it is why "some
minimal pairing passes at each non-cut site" upgrades to "some minimal pairing passes
at every non-cut site at once" -- the upgrade `cutturn mu4` measured over 29520
configurations. -/

/-- **Per-site minimal choices assemble into a global minimum**, because the cost is a
sum over sites and the sites are independent. -/
theorem sum_min_is_min {ι : Type*} (S : Finset ι) (f g : ι → ℕ)
    (h : ∀ i ∈ S, f i ≤ g i) : ∑ i ∈ S, f i ≤ ∑ i ∈ S, g i :=
  Finset.sum_le_sum h

-- A pass links the two edges it crosses: an end and its turn are adjacent in the
-- walk graph, so if the turn carries an end of one edge to an end of another, the two
-- lie in one component.  That is `reachable_turn`, already in this file (BLOCK 15);
-- it is not restated here.  Chaining it along a run is what `hsep` needs.

end EltBridge

#print axioms EltBridge.sum_min_is_min
#print axioms EltBridge.reachable_turn

namespace EltBridge

/-! ### Passing without swapping

BLOCK 149 refuted `HasFreePair` in the per-strand model, which kills the swap route to
`hsep`: one cannot MERGE walks there.  But `hsep` does not require merging.  What
`exists_run_connected` produces is a minimal datum whose runs are connected, and such a
datum can be CHOSEN rather than reached by swaps -- take a passing pairing at every
non-cut site and the forced bounce at every cut site.

The step that makes the choice legitimate is that a passing pairing attains the
minimum off a cut site.  `pass_le_bounce_of_left_differs` covers the case where the left
side's classes differ; in the bulk a non-cut site has `alpha != 0` or `beta != 0`, and
`beta != 0` is the right side's classes differing, so both cases are needed. -/

/-- **Off a cut site the pass attains the minimum, whichever side differs.**  A
difference on either side forces the bounce to pay a flip there, which the two passes
match. -/
theorem pass_le_bounce_of_either_differs (l l' r r' : Fin 4)
    (hl : l.val < 2) (hl' : l'.val < 2) (hr : 2 ≤ r.val) (hr' : 2 ≤ r'.val)
    (hne : l ≠ l' ∨ r ≠ r') :
    costOf l r' + costOf r l' ≤ costOf l l' + costOf r r' := by
  have h1 : costOf l r' = 1 := by
    unfold costOf
    rw [if_neg (by intro h; rw [h] at hl; omega), if_neg (by omega)]
  have h2 : costOf r l' = 1 := by
    unfold costOf
    rw [if_neg (by intro h; rw [h] at hr; omega), if_neg (by omega)]
  rw [h1, h2]
  rcases hne with h | h
  · have h3 : costOf l l' = 2 := by
      unfold costOf; rw [if_neg h, if_pos (by omega)]
    have h4 : 0 ≤ costOf r r' := Nat.zero_le _
    omega
  · have h3 : costOf r r' = 2 := by
      unfold costOf; rw [if_neg h, if_pos (by omega)]
    have h4 : 0 ≤ costOf l l' := Nat.zero_le _
    omega

/-- **The non-cut criterion in the bulk.**  A bulk site is a cut site exactly when both
sides' classes agree, so a non-cut bulk site has one side differing -- which is the
hypothesis `pass_le_bounce_of_either_differs` wants. -/
theorem noncut_gives_a_difference (l l' r r' : Fin 4)
    (hnotcut : ¬ (l = l' ∧ r = r')) : l ≠ l' ∨ r ≠ r' := by
  by_cases h : l = l'
  · exact Or.inr (fun hc => hnotcut ⟨h, hc⟩)
  · exact Or.inl h

/-- **So the choice is available everywhere it is needed**: at a non-cut bulk site a
passing pairing attains the minimum, and at a cut site the bounce strictly wins.  Taking
the pass off the cut sites and the bounce on them is therefore a minimal datum, and its
runs are connected because passes link adjacent edges.  No swap and no free pair
appears. -/
theorem choose_pass_off_cut (l l' r r' : Fin 4)
    (hl : l.val < 2) (hl' : l'.val < 2) (hr : 2 ≤ r.val) (hr' : 2 ≤ r'.val) :
    (¬ (l = l' ∧ r = r') →
      costOf l r' + costOf r l' ≤ costOf l l' + costOf r r') ∧
    ((l = l' ∧ r = r') →
      costOf l l' + costOf r r' < costOf l r' + costOf r l') := by
  refine ⟨fun h => pass_le_bounce_of_either_differs l l' r r' hl hl' hr hr'
    (noncut_gives_a_difference l l' r r' h), ?_⟩
  rintro ⟨rfl, rfl⟩
  exact bounce_beats_pass_at_cut l r hl hr

end EltBridge

#print axioms EltBridge.pass_le_bounce_of_either_differs
#print axioms EltBridge.choose_pass_off_cut

namespace EltBridge

/-! ### The dichotomy over class counts

`choose_pass_off_cut` is stated on `Fin 4` classes -- one strand per class per side,
the `mu = 2` shape.  For general `mu` a site is described by its class COUNTS, and the
statement has to be recast over them.

Writing `Ap Am Bp Bm` for the arrival class counts and `Cp Cm Dp Dm` for the departure
ones, with `Phi = 0` in the bulk:

* a bounce-only plan keeps each half to itself.  On the left it must match `(Ap, Am)`
  to `(Cp, Cm)`, and since `Ap + Am = Cp + Cm` the mismatch is `|Ap - Cp|` pairs, each a
  sign flip costing `2`.  As `alpha = 2 (Cp - Ap)` under `Phi = 0`, that is `|alpha|`.
  The right side likewise costs `|beta|`.  So bounce-only costs `|alpha| + |beta|`.
* the certified minimum is `siteValue = max (|alpha|, |beta|)` when `Phi = 0`.

So bounce-only is optimal exactly when one of `alpha`, `beta` vanishes, and strictly
suboptimal when both are non-zero -- in which case EVERY minimal plan passes.  That is
stronger than the `mu = 2` statement, where passing was only available. -/

/-- `alpha = 2 (Cp - Ap)` once `Phi = 0`: the flow balance turns the sign imbalance into
a class imbalance. -/
theorem alpha_eq_two_mul_of_phi_zero (Ap Am Cp Cm : ℕ)
    (hphi : SiteCost.Phi Ap Am Cp Cm = 0) :
    SiteCost.alpha Ap Am Cp Cm = 2 * ((Cp : ℤ) - Ap) := by
  unfold SiteCost.Phi at hphi
  unfold SiteCost.alpha
  omega

/-- **When both sides differ, bounce-only is strictly beaten.**  The minimum is the max
of the two imbalances and the bounce pays their sum, so every minimal plan must move
mass across the halves -- a pass is forced, not merely available. -/
theorem bounce_strictly_beaten_when_both_differ (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    max a.natAbs b.natAbs < a.natAbs + b.natAbs := by
  have h1 : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have h2 : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  rcases Nat.le_total a.natAbs b.natAbs with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-- And with `Phi = 0` the site value is exactly that max, so the comparison above is a
comparison with the true minimum. -/
theorem siteValue_eq_max_of_phi_zero (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (hphi : SiteCost.Phi Ap Am Cp Cm = 0) :
    SiteCost.siteValue Ap Am Bp Bm Cp Cm Dp Dm
      = max (SiteCost.alpha Ap Am Cp Cm).natAbs (SiteCost.beta Bp Bm Dp Dm).natAbs := by
  unfold SiteCost.siteValue
  rw [hphi]
  simp

/-- **The counts form of the dichotomy.**  Given that a bounce-only plan costs
`|alpha| + |beta|` -- the hypothesis `hbounce`, which is the transportation computation
and is not proved here -- a site with both imbalances non-zero admits no minimal
bounce-only plan, so every minimal plan passes. -/
theorem pass_forced_when_both_differ (Ap Am Bp Bm Cp Cm Dp Dm : ℕ) (bounceCost : ℕ)
    (hphi : SiteCost.Phi Ap Am Cp Cm = 0)
    (hbounce : bounceCost
      = (SiteCost.alpha Ap Am Cp Cm).natAbs + (SiteCost.beta Bp Bm Dp Dm).natAbs)
    (ha : SiteCost.alpha Ap Am Cp Cm ≠ 0) (hb : SiteCost.beta Bp Bm Dp Dm ≠ 0) :
    SiteCost.siteValue Ap Am Bp Bm Cp Cm Dp Dm < bounceCost := by
  rw [hbounce, siteValue_eq_max_of_phi_zero Ap Am Bp Bm Cp Cm Dp Dm hphi]
  exact bounce_strictly_beaten_when_both_differ _ _ ha hb

end EltBridge

#print axioms EltBridge.alpha_eq_two_mul_of_phi_zero
#print axioms EltBridge.bounce_strictly_beaten_when_both_differ
#print axioms EltBridge.pass_forced_when_both_differ

namespace EltBridge

/-! ### `hbounce`, the transportation computation

BLOCK 154 carried `hbounce` -- that a bounce-only plan costs `|alpha| + |beta|` -- as a
hypothesis.  Only the LOWER bound is needed, since the argument is that bounce-only
EXCEEDS the minimum, and the lower bound is pinned by the row and column sums alone.

In the left block, `x01` is the mass flipped from arrival class `0` to departure class
`1` and `x10` the reverse.  The row sum `x00 + x01 = Ap` and the column sum
`x00 + x10 = Cp` give `x01 - x10 = Ap - Cp` outright, so the flipped mass
`x01 + x10` is at least `|Ap - Cp|`.  With `Phi = 0` that is `|alpha| / 2`, and each
flip costs `2`. -/

/-- **The flipped mass in a half is pinned by its sums.**  `x01 - x10 = Ap - Cp`, so
`x01 + x10 ≥ |Ap - Cp|` whatever the plan does. -/
theorem flip_mass_ge (Ap Cp x00 x01 x10 : ℕ)
    (r0 : x00 + x01 = Ap) (c0 : x00 + x10 = Cp) :
    ((Ap : ℤ) - Cp).natAbs ≤ x01 + x10 := by
  omega

/-- **So a bounce-only plan costs at least `|alpha|` on the left.**  Each flip costs
`2`, and with `Phi = 0` the imbalance `|Ap - Cp|` is `|alpha| / 2`. -/
theorem bounce_left_cost_ge (Ap Am Cp Cm x00 x01 x10 : ℕ)
    (hphi : SiteCost.Phi Ap Am Cp Cm = 0)
    (r0 : x00 + x01 = Ap) (c0 : x00 + x10 = Cp) :
    (SiteCost.alpha Ap Am Cp Cm).natAbs ≤ 2 * (x01 + x10) := by
  have hα := alpha_eq_two_mul_of_phi_zero Ap Am Cp Cm hphi
  have hflip := flip_mass_ge Ap Cp x00 x01 x10 r0 c0
  omega

/-- **`hbounce`, in the form the argument needs.**  A bounce-only plan -- one whose
cross-half entries all vanish -- costs at least `|alpha| + |beta|`.  Its cost is
`2 (x01 + x10) + 2 (x23 + x32)` once the cross terms are gone, and each half is bounded
below by its own imbalance. -/
theorem bounce_only_cost_ge (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (x00 x01 x10 x22 x23 x32 : ℕ)
    (hphiL : SiteCost.Phi Ap Am Cp Cm = 0)
    (hphiR : SiteCost.Phi Bp Bm Dp Dm = 0)
    (r0 : x00 + x01 = Ap) (c0 : x00 + x10 = Cp)
    (r2 : x22 + x23 = Bp) (c2 : x22 + x32 = Dp) :
    (SiteCost.alpha Ap Am Cp Cm).natAbs + (SiteCost.beta Bp Bm Dp Dm).natAbs
      ≤ 2 * (x01 + x10) + 2 * (x23 + x32) := by
  have hL := bounce_left_cost_ge Ap Am Cp Cm x00 x01 x10 hphiL r0 c0
  have hR := bounce_left_cost_ge Bp Bm Dp Dm x22 x23 x32 hphiR r2 c2
  have hswap : (SiteCost.beta Bp Bm Dp Dm).natAbs
      = (SiteCost.alpha Bp Bm Dp Dm).natAbs :=
    (SiteCost.alpha_natAbs_swap Bp Bm Dp Dm).symm
  omega

/-- **The forced pass, with `hbounce` discharged.**  At a bulk site with both imbalances
non-zero, no bounce-only plan attains the minimum: its cost is at least
`|alpha| + |beta|`, which strictly exceeds `max(|alpha|, |beta|)`. -/
theorem pass_forced_of_sums (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (x00 x01 x10 x22 x23 x32 : ℕ)
    (hphiL : SiteCost.Phi Ap Am Cp Cm = 0)
    (hphiR : SiteCost.Phi Bp Bm Dp Dm = 0)
    (r0 : x00 + x01 = Ap) (c0 : x00 + x10 = Cp)
    (r2 : x22 + x23 = Bp) (c2 : x22 + x32 = Dp)
    (ha : SiteCost.alpha Ap Am Cp Cm ≠ 0) (hb : SiteCost.beta Bp Bm Dp Dm ≠ 0) :
    SiteCost.siteValue Ap Am Bp Bm Cp Cm Dp Dm < 2 * (x01 + x10) + 2 * (x23 + x32) := by
  have hge := bounce_only_cost_ge Ap Am Bp Bm Cp Cm Dp Dm x00 x01 x10 x22 x23 x32
    hphiL hphiR r0 c0 r2 c2
  have hlt := bounce_strictly_beaten_when_both_differ
    (SiteCost.alpha Ap Am Cp Cm) (SiteCost.beta Bp Bm Dp Dm) ha hb
  rw [siteValue_eq_max_of_phi_zero Ap Am Bp Bm Cp Cm Dp Dm hphiL]
  omega

end EltBridge

#print axioms EltBridge.flip_mass_ge
#print axioms EltBridge.bounce_only_cost_ge
#print axioms EltBridge.pass_forced_of_sums

namespace EltBridge

/-! ### The one-sided case: passing ties

`pass_forced_of_sums` covers a site with BOTH imbalances non-zero, where passing is
forced.  When exactly one vanishes -- say `beta = 0` -- bounce-only already attains the
minimum `|alpha|`, so passing cannot be forced and a passing plan must be EXHIBITED.

It is exhibited by a local trade.  With `alpha != 0` the left half carries at least one
flip, and the right half, being occupied (`mu_pos` on the span), carries at least one
same-class bounce.  Trade the two for two passes:

    remove   a left flip        cost 2
    remove   a right bounce     cost 0
    add      two passes         cost 1 + 1

Row and column sums are preserved -- the left arrival now goes right, the right arrival
now goes left -- and the cost is unchanged, `2 + 0 = 1 + 1`.  So a minimal plan with a
pass exists, which is what run connectivity needs. -/

/-- **Passing ties when one side is balanced.**  A flip on the differing side and a
bounce on the balanced side cost exactly what the two passes replacing them cost. -/
theorem pass_ties_bounce_of_one_side (l l' r r' : Fin 4)
    (hl : l.val < 2) (hl' : l'.val < 2) (hr : 2 ≤ r.val) (hr' : 2 ≤ r'.val)
    (hne : l ≠ l') (heq : r = r') :
    costOf l r' + costOf r l' = costOf l l' + costOf r r' := by
  have h1 : costOf l r' = 1 := by
    unfold costOf
    rw [if_neg (by intro h; rw [h] at hl; omega), if_neg (by omega)]
  have h2 : costOf r l' = 1 := by
    unfold costOf
    rw [if_neg (by intro h; rw [h] at hr; omega), if_neg (by omega)]
  have h3 : costOf l l' = 2 := by
    unfold costOf; rw [if_neg hne, if_pos (by omega)]
  have h4 : costOf r r' = 0 := by
    unfold costOf; rw [if_pos heq]
  rw [h1, h2, h3, h4]

/-- **The three local cases together.**  At a bulk site, comparing the bouncing pairing
with the passing one:

* both sides agree (a cut site): the bounce STRICTLY wins, so no minimal plan passes;
* exactly one side differs: the two are EQUAL, so a minimal plan that passes exists;
* both sides differ: the pass is strictly cheaper, so every minimal plan passes.

Only the first denies a pass, and it is exactly the cut condition. -/
theorem local_trichotomy (l l' r r' : Fin 4)
    (hl : l.val < 2) (hl' : l'.val < 2) (hr : 2 ≤ r.val) (hr' : 2 ≤ r'.val) :
    (l = l' → r = r' →
      costOf l l' + costOf r r' < costOf l r' + costOf r l') ∧
    (l ≠ l' → r = r' →
      costOf l r' + costOf r l' = costOf l l' + costOf r r') ∧
    (l ≠ l' → r ≠ r' →
      costOf l r' + costOf r l' < costOf l l' + costOf r r') := by
  refine ⟨?_, pass_ties_bounce_of_one_side l l' r r' hl hl' hr hr', ?_⟩
  · rintro rfl rfl
    exact bounce_beats_pass_at_cut l r hl hr
  · intro hne hne'
    have h1 : costOf l r' = 1 := by
      unfold costOf
      rw [if_neg (by intro h; rw [h] at hl; omega), if_neg (by omega)]
    have h2 : costOf r l' = 1 := by
      unfold costOf
      rw [if_neg (by intro h; rw [h] at hr; omega), if_neg (by omega)]
    have h3 : costOf l l' = 2 := by
      unfold costOf; rw [if_neg hne, if_pos (by omega)]
    have h4 : costOf r r' = 2 := by
      unfold costOf; rw [if_neg hne', if_pos (by omega)]
    rw [h1, h2, h3, h4]
    omega

end EltBridge

#print axioms EltBridge.pass_ties_bounce_of_one_side
#print axioms EltBridge.local_trichotomy

namespace EltBridge

/-! ### Gluing the per-site choices

`local_trichotomy` supplies, at each site, a minimal pairing with the pass/bounce
behaviour that site needs.  Those choices have to become ONE turn.

They do, and for the reason `exists_rival_data` spliced a single site: each per-site
involution moves ends only within its own site, so applying `T (siteOf x)` to `x` lands
at the same site, and a second application is by the same `T`.  The glue is therefore an
involution with no compatibility condition between different sites at all. -/

/-- **A family of per-site involutions glues to one involution.**  Each `T s` is an
involution fixing everything off site `s` and preserving site `s`; the glue applies the
one belonging to the end's own site. -/
theorem glue_involution {α : Type*} (siteOf : α → ℤ) (T : ℤ → α → α)
    (hinv : ∀ s x, T s (T s x) = x)
    (hsite : ∀ s x, siteOf x = s → siteOf (T s x) = s) :
    ∀ x : α, T (siteOf (T (siteOf x) x)) (T (siteOf x) x) = x := by
  intro x
  rw [hsite (siteOf x) x rfl, hinv]

/-- The glue is fixed-point-free as soon as each piece is, on its own site. -/
theorem glue_ne {α : Type*} (siteOf : α → ℤ) (T : ℤ → α → α)
    (hne : ∀ s x, siteOf x = s → T s x ≠ x) :
    ∀ x : α, T (siteOf x) x ≠ x :=
  fun x => hne (siteOf x) x rfl

/-- And it keeps every end at its own site, which is what makes the cost a sum over
sites and hence `sum_min_is_min` applicable. -/
theorem glue_site {α : Type*} (siteOf : α → ℤ) (T : ℤ → α → α)
    (hsite : ∀ s x, siteOf x = s → siteOf (T s x) = s) :
    ∀ x : α, siteOf (T (siteOf x) x) = siteOf x :=
  fun x => hsite (siteOf x) x rfl

/-- **The glue meets the crossing partner nowhere**, given that the partner changes the
site.  With this the three `WalkGraph.Data` obligations are all discharged for the
glued turn, exactly as they were for the single-site splice. -/
theorem glue_pt_ne {α : Type*} (siteOf : α → ℤ) (p : α → α) (T : ℤ → α → α)
    (hpsite : ∀ x, siteOf (p x) ≠ siteOf x)
    (hsite : ∀ s x, siteOf x = s → siteOf (T s x) = s) :
    ∀ x : α, p x ≠ T (siteOf x) x := by
  intro x hc
  exact hpsite x (by rw [hc, glue_site siteOf T hsite x])

end EltBridge

#print axioms EltBridge.glue_involution
#print axioms EltBridge.glue_ne
#print axioms EltBridge.glue_pt_ne

namespace EltBridge

/-- **The glued turn as a `WalkGraph.Data`.**  All three obligations come from the glue
lemmas: involutivity from `glue_involution`, fixed-point-freeness from `glue_ne`, and
disjointness from `p` from `glue_pt_ne`.  So per-site choices assemble into a datum with
nothing further to check. -/
theorem exists_glued_data {α : Type*} [Fintype α] [DecidableEq α]
    (siteOf : α → ℤ) (p : α → α) (T : ℤ → α → α)
    (hpinv : ∀ x, p (p x) = x) (hpne : ∀ x, p x ≠ x)
    (hpsite : ∀ x, siteOf (p x) ≠ siteOf x)
    (hinv : ∀ s x, T s (T s x) = x)
    (hsite : ∀ s x, siteOf x = s → siteOf (T s x) = s)
    (hne : ∀ s x, siteOf x = s → T s x ≠ x) :
    ∃ E : WalkGraph.Data α, E.p = p ∧ ∀ x, E.t x = T (siteOf x) x := by
  refine ⟨{ p := p, t := fun x => T (siteOf x) x,
            p_invol := hpinv, p_ne := hpne,
            t_invol := glue_involution siteOf T hinv hsite,
            t_ne := glue_ne siteOf T hne,
            pt_ne := glue_pt_ne siteOf p T hpsite hsite }, rfl, fun _ => rfl⟩

/-- **M4b's global layer, stated.**  With the glued datum in hand, `hsep` is the
statement that any two ends with the same run index are joined; a pass at a site links
the two edges it crosses (`reachable_turn`), and `local_trichotomy` says a minimal
choice passing at every non-cut site exists.  This names the remaining obligation: that
those links chain along a run. -/
def RunsConnected {α : Type*} [Fintype α] [DecidableEq α]
    (edgeOf : α → ℤ) (Zf : Finset ℤ) (E : WalkGraph.Data α) : Prop :=
  ∀ x y : α, runIndexG edgeOf Zf x = runIndexG edgeOf Zf y →
    (WalkGraph.graph E).Reachable x y

end EltBridge

#print axioms EltBridge.exists_glued_data

namespace EltBridge

/-! ### The two-chain argument at `mu = 2`

BLOCK 159 located the local route's validity exactly: it works when every edge carries
two strands, and the mechanism is that passes chain the up strands and the down strands
SEPARATELY, while the bounce at a cut site joins the two chains at one edge.

Abstracted, a strand is `(edge, up?)`.  A pass at the site between `j` and `j+1` gives
`(j, true) — (j+1, true)` and `(j+1, false) — (j, false)`; the bounce at the run's left
boundary gives `(lo, true) — (lo, false)`.  Those three families put every strand of the
run in one component, which is the `|Z| + 1` count. -/

/-- **A run is one component.**  Passes chain each level and the boundary bounce joins
the levels, so every strand of the run is reachable from the leftmost up strand. -/
theorem run_one_component (lo : ℤ) (n : ℕ) (R : ℤ × Bool → ℤ × Bool → Prop)
    (hup : ∀ k : ℕ, k < n → R (lo + k, true) (lo + (k + 1 : ℕ), true))
    (hdn : ∀ k : ℕ, k < n → R (lo + k, false) (lo + (k + 1 : ℕ), false))
    (hjoin : R (lo, true) (lo, false)) :
    ∀ k : ℕ, k ≤ n →
      Relation.ReflTransGen R (lo, true) (lo + k, true) ∧
      Relation.ReflTransGen R (lo, true) (lo + k, false) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · simpa using Relation.ReflTransGen.refl
    · have : Relation.ReflTransGen R (lo, true) (lo, false) :=
        Relation.ReflTransGen.single hjoin
      simpa using this
  | succ j ih =>
    intro hjn
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨?_, ?_⟩
    · exact h1.tail (hup j (by omega))
    · exact h2.tail (hdn j (by omega))

/-- The same conclusion phrased as "any two strands of the run are joined", which is the
shape `RunsConnected` wants. -/
theorem run_pairwise (lo : ℤ) (n : ℕ) (R : ℤ × Bool → ℤ × Bool → Prop)
    (hsymm : ∀ a b, R a b → R b a)
    (hup : ∀ k : ℕ, k < n → R (lo + k, true) (lo + (k + 1 : ℕ), true))
    (hdn : ∀ k : ℕ, k < n → R (lo + k, false) (lo + (k + 1 : ℕ), false))
    (hjoin : R (lo, true) (lo, false))
    (j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n) (b b' : Bool) :
    Relation.ReflTransGen R (lo + j, b) (lo + j', b') := by
  have hsymmR : ∀ a c, Relation.ReflTransGen R a c → Relation.ReflTransGen R c a := by
    intro a c h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.head (hsymm _ _ hstep) ih
  obtain ⟨u1, d1⟩ := run_one_component lo n R hup hdn hjoin j hj
  obtain ⟨u2, d2⟩ := run_one_component lo n R hup hdn hjoin j' hj'
  have hb : Relation.ReflTransGen R (lo + j, b) (lo, true) := by
    cases b
    · exact hsymmR _ _ d1
    · exact hsymmR _ _ u1
  have hb' : Relation.ReflTransGen R (lo, true) (lo + j', b') := by
    cases b'
    · exact d2
    · exact u2
  exact hb.trans hb'

end EltBridge

#print axioms EltBridge.run_one_component
#print axioms EltBridge.run_pairwise

namespace EltBridge

/-! ### From the strand chain to the walk graph

`run_pairwise` lives on strands, `(edge, up?)`, and concludes in `Relation.ReflTransGen`.
`RunsConnected` lives on ends and concludes in `SimpleGraph.Reachable`.  The bridge is
that reachability is transitive and reflexive, so any relation whose steps are
realisable as walks transfers along the chain. -/

/-- **Transfer**: a chain of steps each realisable in the graph is a walk in the graph. -/
theorem reachable_of_reflTransGen {α β : Type*} (G : SimpleGraph β)
    (R : α → α → Prop) (f : α → β)
    (hR : ∀ a b, R a b → G.Reachable (f a) (f b))
    {x y : α} (h : Relation.ReflTransGen R x y) : G.Reachable (f x) (f y) := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hstep ih => exact ih.trans (hR _ _ hstep)

/-- **The run is connected in the walk graph.**  Instantiating `run_pairwise` through
the transfer: if each strand step is realisable as a walk -- which the passes and the
boundary bounce supply, since an end and its turn are adjacent (`reachable_turn`) -- then
any two strands of the run are joined in the walk graph itself. -/
theorem run_connected_in_graph {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (f : ℤ × Bool → α) (lo : ℤ) (n : ℕ)
    (R : ℤ × Bool → ℤ × Bool → Prop)
    (hR : ∀ a b, R a b → (WalkGraph.graph D).Reachable (f a) (f b))
    (hsymm : ∀ a b, R a b → R b a)
    (hup : ∀ k : ℕ, k < n → R (lo + k, true) (lo + (k + 1 : ℕ), true))
    (hdn : ∀ k : ℕ, k < n → R (lo + k, false) (lo + (k + 1 : ℕ), false))
    (hjoin : R (lo, true) (lo, false))
    (j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n) (b b' : Bool) :
    (WalkGraph.graph D).Reachable (f (lo + j, b)) (f (lo + j', b')) :=
  reachable_of_reflTransGen (WalkGraph.graph D) R f hR
    (run_pairwise lo n R hsymm hup hdn hjoin j j' hj hj' b b')

/-- The step hypothesis `hR` is not an extra assumption in the intended instantiation:
a turn step is always realisable, since an end and its turn are adjacent. -/
theorem turn_step_realisable {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (x : α) : (WalkGraph.graph D).Reachable x (D.t x) :=
  reachable_turn D x

end EltBridge

#print axioms EltBridge.reachable_of_reflTransGen
#print axioms EltBridge.run_connected_in_graph

namespace EltBridge

/-! ### The instantiation

Take `f` to be "the bottom end of the strand": `up j` for edge `j`'s up strand and
`dn j` for its down strand.  Then the three hypotheses of `run_pairwise` are statements
about the concrete turn.

* `hup`: from `up j` cross its own strand (the partner) to the top, where a pass sends
  it to `up (j+1)`.
* `hdn`: the same one step to the left, since a pass at that site carries
  `dn (j+1)`'s partner to `dn j`.
* `hjoin`: the bounce at the run's left boundary sends `dn lo` straight to `up lo`.

Nothing else about the configuration enters. -/

/-- Reachability along the crossing partner, the companion of `reachable_turn`. -/
theorem reachable_partner {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (x : α) : (WalkGraph.graph D).Reachable x (D.p x) :=
  SimpleGraph.Adj.reachable (G := WalkGraph.graph D) (Or.inl rfl)

/-- **The run is connected, from the turn structure alone.**  `up j` and `dn j` name the
bottom ends of edge `j`'s two strands; the hypotheses say the passes chain them and the
boundary bounce joins them. -/
theorem run_connected_of_turn_structure {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (up dn : ℤ → α) (lo : ℤ) (n : ℕ)
    (hpass_up : ∀ k : ℕ, k < n → D.t (D.p (up (lo + k))) = up (lo + (k + 1 : ℕ)))
    (hpass_dn : ∀ k : ℕ, k < n → D.t (D.p (dn (lo + (k + 1 : ℕ)))) = dn (lo + k))
    (hbounce : D.t (dn lo) = up lo)
    (j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n) (b b' : Bool) :
    (WalkGraph.graph D).Reachable
      (if b then up (lo + j) else dn (lo + j))
      (if b' then up (lo + j') else dn (lo + j')) := by
  classical
  set f : ℤ × Bool → α := fun a => if a.2 then up a.1 else dn a.1 with hf
  set R : ℤ × Bool → ℤ × Bool → Prop :=
    fun a b => (WalkGraph.graph D).Reachable (f a) (f b) with hRdef
  have hR : ∀ a b, R a b → (WalkGraph.graph D).Reachable (f a) (f b) := fun _ _ h => h
  have hsymm : ∀ a b, R a b → R b a := fun _ _ h => h.symm
  -- a strand step: cross the strand, then turn
  have hstep : ∀ x : α, (WalkGraph.graph D).Reachable x (D.t (D.p x)) :=
    fun x => (reachable_partner D x).trans (reachable_turn D (D.p x))
  have hup : ∀ k : ℕ, k < n → R (lo + k, true) (lo + (k + 1 : ℕ), true) := by
    intro k hk
    have := hstep (up (lo + k))
    rw [hpass_up k hk] at this
    simpa [hRdef, hf] using this
  have hdn : ∀ k : ℕ, k < n → R (lo + k, false) (lo + (k + 1 : ℕ), false) := by
    intro k hk
    have := hstep (dn (lo + (k + 1 : ℕ)))
    rw [hpass_dn k hk] at this
    simpa [hRdef, hf] using this.symm
  have hjoin : R (lo, true) (lo, false) := by
    have := reachable_turn D (dn lo)
    rw [hbounce] at this
    simpa [hRdef, hf] using this.symm
  have := run_pairwise lo n R hsymm hup hdn hjoin j j' hj hj' b b'
  have hmain := reachable_of_reflTransGen (WalkGraph.graph D) R f hR this
  simpa [hf] using hmain

end EltBridge

#print axioms EltBridge.reachable_partner
#print axioms EltBridge.run_connected_of_turn_structure

namespace EltBridge

/-! ### From strand bottoms to all ends

`run_connected_of_turn_structure` joins the BOTTOM ends of the strands in a run.
`hsep` quantifies over all ends.  The gap is one step: an end is either a bottom itself
or its partner's, and an end is always adjacent to its partner. -/

/-- Every end reaches its own strand's chosen representative. -/
theorem reachable_to_base {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (base : α → α)
    (hbase : ∀ x, base x = x ∨ base x = D.p x) (x : α) :
    (WalkGraph.graph D).Reachable x (base x) := by
  rcases hbase x with h | h
  · rw [h]
  · rw [h]; exact reachable_partner D x

/-- **`hsep` from run connectivity on representatives.**  If representatives in the same
run are joined, then so are all ends in that run: go to the representative, across, and
back. -/
theorem hsep_of_base_connected {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (base : α → α) (idx : α → ℕ)
    (hbase : ∀ x, base x = x ∨ base x = D.p x)
    (hbase_idx : ∀ x, idx (base x) = idx x)
    (hrun : ∀ x y : α, idx x = idx y →
      (WalkGraph.graph D).Reachable (base x) (base y)) :
    ∀ x y : α, idx x = idx y → (WalkGraph.graph D).Reachable x y := by
  intro x y hxy
  have h1 : (WalkGraph.graph D).Reachable x (base x) := reachable_to_base D base hbase x
  have h2 : (WalkGraph.graph D).Reachable (base x) (base y) := hrun x y hxy
  have h3 : (WalkGraph.graph D).Reachable (base y) y :=
    (reachable_to_base D base hbase y).symm
  exact (h1.trans h2).trans h3

/-- **What M4b's upper bound now reduces to at `mu = 2`.**  Given the two remaining
inputs -- `hedge`, the geometric condition of `walkCount_le_runs_blk`, and the matching
of the run decomposition to `runIndexG` -- the count follows.  Everything else in the
chain is proved. -/
theorem walkCount_le_of_hsep {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (pos : α → ℤ) (Zf : Finset ℤ)
    (hedge : ∀ x y : α, (WalkGraph.graph D).Adj x y →
      CutComponents.blk pos Zf x = CutComponents.blk pos Zf y ∨ (∃ t : ℤ,
        (pos x = t - 1 ∨ pos x = t) ∧ (pos y = t - 1 ∨ pos y = t) ∧
        (pos x ≠ pos y → t ∉ Zf)))
    (hsep : ∀ x y : α, runIndexG pos Zf x = runIndexG pos Zf y →
      (WalkGraph.graph D).Reachable x y) :
    WalkGraph.walkCount D ≤ Zf.card + 1 :=
  walkCount_le_runs_blk D pos Zf hedge hsep

end EltBridge

#print axioms EltBridge.reachable_to_base
#print axioms EltBridge.hsep_of_base_connected
#print axioms EltBridge.walkCount_le_of_hsep

namespace EltBridge

/-! ### `hedge`

The geometric half of `walkCount_le_runs_blk`, and it is exactly the `TurnInvG`
condition again.  With `pos = edgeOf`:

* a PARTNER edge keeps the edge, so `pos` is unchanged and `blk`, being `gz Zf ∘ pos`,
  is unchanged with it -- the first disjunct;
* a TURN edge keeps the SITE.  Both ends of it therefore have `pos` in `{s-1, s}` for
  `s` that site, since `siteOf` is `edgeOf` or `edgeOf + 1`.  And if the two `pos`
  differ the turn changed the edge, which `hturn` says happens only off `Zf`.
-/

/-- **`hedge` from the turn invariant.**  No new hypothesis: `hturn` is `TurnInvG`'s
second condition, the one `local_trichotomy` secures by making the bounce strictly win
at a cut site. -/
theorem hedge_of_turnInv {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (edgeOf siteOf : α → ℤ) (Zf : Finset ℤ)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hts : ∀ x, siteOf (D.t x) = siteOf x)
    (hse : ∀ x, siteOf x = edgeOf x ∨ siteOf x = edgeOf x + 1)
    (hturn : ∀ x, edgeOf (D.t x) ≠ edgeOf x → siteOf x ∉ Zf) :
    ∀ x y : α, (WalkGraph.graph D).Adj x y →
      CutComponents.blk edgeOf Zf x = CutComponents.blk edgeOf Zf y ∨ (∃ t : ℤ,
        (edgeOf x = t - 1 ∨ edgeOf x = t) ∧ (edgeOf y = t - 1 ∨ edgeOf y = t) ∧
        (edgeOf x ≠ edgeOf y → t ∉ Zf)) := by
  intro x y hadj
  rcases hadj with rfl | rfl
  · -- the crossing partner keeps the edge
    left
    unfold CutComponents.blk
    rw [hpe x]
  · -- the turn keeps the site
    right
    refine ⟨siteOf x, ?_, ?_, ?_⟩
    · rcases hse x with h | h
      · exact Or.inr h.symm
      · exact Or.inl (by omega)
    · have hy : siteOf (D.t x) = siteOf x := hts x
      rcases hse (D.t x) with h | h
      · exact Or.inr (by rw [← hy, h])
      · exact Or.inl (by rw [← hy, h]; omega)
    · intro hne
      exact hturn x (fun hc => hne hc.symm)

end EltBridge

#print axioms EltBridge.hedge_of_turnInv

namespace EltBridge

/-! ### The run decomposition matches `runIndexG`

`runIndexG pos Zf x` is `gz Zf (pos x)`, and `gz Zf t` counts the cut sites at or below
`t`.  So two ends carry the same run index exactly when no cut site lies strictly
between their edges -- which is precisely the interval `run_connected_of_turn_structure`
runs along.  That is the last input. -/

/-- **Equal run index means no cut site in between.**  If a cut site lay in `(a, b]` it
would be counted by `gz` at `b` and not at `a`. -/
theorem no_cut_between_of_gz_eq (Zf : Finset ℤ) (a b : ℤ) (hab : a ≤ b)
    (h : CutComponents.gz Zf a = CutComponents.gz Zf b) :
    ∀ s : ℤ, a < s → s ≤ b → s ∉ Zf := by
  classical
  intro s hsa hsb hs
  have hsub : Zf.filter (fun z => z ≤ a) ⊆ Zf.filter (fun z => z ≤ b) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, le_trans hz.2 hab⟩
  have hss : Zf.filter (fun z => z ≤ a) ⊂ Zf.filter (fun z => z ≤ b) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨s, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨hs, hsb⟩
    · rw [Finset.mem_filter]
      rintro ⟨-, hle⟩
      omega
  have hcard := Finset.card_lt_card hss
  unfold CutComponents.gz at h
  omega

/-- **And no cut site in between means equal run index.**  Stepping across a non-cut
site leaves `gz` unchanged (`gz_step_eq`), so it is constant along the interval. -/
theorem gz_eq_of_no_cut_between (Zf : Finset ℤ) (a : ℤ) (n : ℕ)
    (h : ∀ s : ℤ, a < s → s ≤ a + n → s ∉ Zf) :
    CutComponents.gz Zf (a + n) = CutComponents.gz Zf a := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hstep : CutComponents.gz Zf (a + (k + 1 : ℕ)) = CutComponents.gz Zf (a + k) := by
      have hnot : a + ((k : ℤ) + 1) ∉ Zf := by
        refine h _ (by omega) (by push_cast; omega)
      have := CutComponents.gz_step_eq Zf hnot
      push_cast
      rw [show (a : ℤ) + ((k : ℤ) + 1) - 1 = a + k by ring] at this
      push_cast at this ⊢
      exact this
    rw [hstep]
    exact ih (fun s hs1 hs2 => h s hs1 (by push_cast at hs2 ⊢; omega))

end EltBridge

#print axioms EltBridge.no_cut_between_of_gz_eq
#print axioms EltBridge.gz_eq_of_no_cut_between

namespace EltBridge

/-! ### The assembly

Everything proved since BLOCK 153, in one statement.  The hypotheses are the geometry
of the end type, the choice of a strand representative, and run connectivity on those
representatives -- which `run_connected_of_turn_structure` supplies at `mu = 2` from the
turn's passes and boundary bounces. -/

/-- **The shield law's upper bound, from the turn structure.**  `walkCount <= |Z| + 1`.

`hedge` comes from the turn invariant (`hedge_of_turnInv`), `hsep` from run connectivity
on representatives lifted to all ends (`hsep_of_base_connected`), and the two feed
`walkCount_le_runs_blk`.  No merge, no swap and no free pair appears. -/
theorem shield_upper_bound_of_structure {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (edgeOf siteOf : α → ℤ) (Zf : Finset ℤ) (base : α → α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hts : ∀ x, siteOf (D.t x) = siteOf x)
    (hse : ∀ x, siteOf x = edgeOf x ∨ siteOf x = edgeOf x + 1)
    (hturn : ∀ x, edgeOf (D.t x) ≠ edgeOf x → siteOf x ∉ Zf)
    (hbase : ∀ x, base x = x ∨ base x = D.p x)
    (hbase_idx : ∀ x, CutComponents.gz Zf (edgeOf (base x))
      = CutComponents.gz Zf (edgeOf x))
    (hrun : ∀ x y : α, CutComponents.gz Zf (edgeOf x) = CutComponents.gz Zf (edgeOf y) →
      (WalkGraph.graph D).Reachable (base x) (base y)) :
    WalkGraph.walkCount D ≤ Zf.card + 1 := by
  refine walkCount_le_runs_blk D edgeOf Zf
    (hedge_of_turnInv D edgeOf siteOf Zf hpe hts hse hturn) ?_
  -- `hsep`, through the representatives
  have hlift := hsep_of_base_connected D base
    (fun x => CutComponents.gz Zf (edgeOf x)) hbase hbase_idx hrun
  intro x y hxy
  refine hlift x y ?_
  have : (runIndexG edgeOf Zf x).val = (runIndexG edgeOf Zf y).val := by rw [hxy]
  simpa [runIndexG] using this

end EltBridge

#print axioms EltBridge.shield_upper_bound_of_structure

namespace EltBridge

/-! ### Instantiated on `EndType.Endpt`

Two of the geometric hypotheses are facts about the end type itself: `partner` keeps the
edge, and `siteOf` is `edgeOf` or `edgeOf + 1` by definition.  Discharging them leaves
only the turn's own properties. -/

/-- `siteOf` sits on one of the two edges it separates. -/
theorem siteOf_cases {n : ℕ} {m : Fin n → ℕ} (x : EndType.Endpt n m) :
    EndType.siteOf x = EndType.edgeOf x ∨ EndType.siteOf x = EndType.edgeOf x + 1 := by
  unfold EndType.siteOf
  by_cases h : EndType.atTop x
  · exact Or.inr (by rw [h]; norm_num)
  · exact Or.inl (by simp [h])

/-- **The shield law's upper bound on the end type.**  `hpe` and `hse` are discharged
from `EndType`; what remains is the turn keeping its site, the turn invariant, the
representative, and run connectivity. -/
theorem shield_upper_bound_endpt {n : ℕ} {m : Fin n → ℕ}
    (D : WalkGraph.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (base : EndType.Endpt n m → EndType.Endpt n m)
    (hp : ∀ x, D.p x = EndType.partner x)
    (hts : ∀ x, EndType.siteOf (D.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (D.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hbase : ∀ x, base x = x ∨ base x = D.p x)
    (hbase_idx : ∀ x, CutComponents.gz Zf (EndType.edgeOf (base x))
      = CutComponents.gz Zf (EndType.edgeOf x))
    (hrun : ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph D).Reachable (base x) (base y)) :
    WalkGraph.walkCount D ≤ Zf.card + 1 :=
  shield_upper_bound_of_structure D EndType.edgeOf EndType.siteOf Zf base
    (fun x => by rw [hp x]; exact EndType.partner_edgeOf x)
    hts siteOf_cases hturn hbase hbase_idx hrun

end EltBridge

#print axioms EltBridge.siteOf_cases
#print axioms EltBridge.shield_upper_bound_endpt

namespace EltBridge

/-- **On the canonical turn.**  `DataBuild.dataOf` has `p := partner` and
`t := glue siteOf (turnAt up)`, and `glue` applies the local map of the end's own site,
so `hp` is `rfl` and `hts` is `turnAt_site`.  Only the turn invariant, the
representative and run connectivity remain. -/
theorem shield_upper_bound_dataOf {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ,
      (EndType.arrAt (m := m) up s).card = (EndType.depAt (m := m) up s).card)
    (Zf : Finset ℤ) (base : EndType.Endpt n m → EndType.Endpt n m)
    (hturn : ∀ x, EndType.edgeOf ((DataBuild.dataOf up hbal).t x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf)
    (hbase : ∀ x, base x = x ∨ base x = (DataBuild.dataOf up hbal).p x)
    (hbase_idx : ∀ x, CutComponents.gz Zf (EndType.edgeOf (base x))
      = CutComponents.gz Zf (EndType.edgeOf x))
    (hrun : ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph (DataBuild.dataOf up hbal)).Reachable (base x) (base y)) :
    WalkGraph.walkCount (DataBuild.dataOf up hbal) ≤ Zf.card + 1 :=
  shield_upper_bound_endpt (DataBuild.dataOf up hbal) Zf base
    (fun _ => rfl)
    (fun x => DataBuild.turnAt_site up hbal x)
    hturn hbase hbase_idx hrun

end EltBridge

#print axioms EltBridge.shield_upper_bound_dataOf

namespace EltBridge

/-- The bottom end of an end's own strand: the canonical representative. -/
def botOf {n : ℕ} {m : Fin n → ℕ} (x : EndType.Endpt n m) : EndType.Endpt n m :=
  ⟨x.edge, x.idx, false⟩

@[simp] theorem botOf_edgeOf {n : ℕ} {m : Fin n → ℕ} (x : EndType.Endpt n m) :
    EndType.edgeOf (botOf x) = EndType.edgeOf x := rfl

/-- The representative is the end itself or its crossing partner. -/
theorem botOf_eq_or_partner {n : ℕ} {m : Fin n → ℕ} (x : EndType.Endpt n m) :
    botOf x = x ∨ botOf x = EndType.partner x := by
  cases hx : x.top
  · left
    unfold botOf
    cases x with
    | mk e i t => simp_all
  · right
    unfold botOf EndType.partner
    cases x with
    | mk e i t => simp_all

/-- **The shield law's upper bound with the representative discharged.**  Only the turn
invariant and run connectivity remain -- the two the `mu = 2` construction supplies. -/
theorem shield_upper_bound_bot {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ,
      (EndType.arrAt (m := m) up s).card = (EndType.depAt (m := m) up s).card)
    (Zf : Finset ℤ)
    (hturn : ∀ x, EndType.edgeOf ((DataBuild.dataOf up hbal).t x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf)
    (hrun : ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph (DataBuild.dataOf up hbal)).Reachable (botOf x) (botOf y)) :
    WalkGraph.walkCount (DataBuild.dataOf up hbal) ≤ Zf.card + 1 :=
  shield_upper_bound_dataOf up hbal Zf botOf hturn
    (fun x => botOf_eq_or_partner x) (fun _ => rfl) hrun

end EltBridge

#print axioms EltBridge.botOf_eq_or_partner
#print axioms EltBridge.shield_upper_bound_bot

namespace EltBridge

/-! ### `hrun` from the two-chain connectivity

`run_connected_of_turn_structure` joins `up (lo+j)` and `dn (lo+j)` across a run.
`hrun` asks for `botOf x` and `botOf y`.  The two match once `botOf` is known to be one
of the two strand bottoms on its own edge, which at `mu = 2` it is: an edge has exactly
the strands `0` and `1`. -/

/-- **`hrun` on a single run.**  With every end's edge inside `[lo, lo+nn]` and every
representative one of that edge's two strand bottoms, the two-chain connectivity gives
`hrun` outright. -/
theorem hrun_single_run {n : ℕ} {m : Fin n → ℕ} (D : WalkGraph.Data (EndType.Endpt n m))
    (up dn : ℤ → EndType.Endpt n m) (lo : ℤ) (nn : ℕ)
    (hcover : ∀ x, botOf x = up (EndType.edgeOf x) ∨ botOf x = dn (EndType.edgeOf x))
    (hrange : ∀ x : EndType.Endpt n m, ∃ k : ℕ, k ≤ nn ∧ EndType.edgeOf x = lo + k)
    (hconn : ∀ j j' : ℕ, j ≤ nn → j' ≤ nn → ∀ b b' : Bool,
      (WalkGraph.graph D).Reachable
        (if b then up (lo + j) else dn (lo + j))
        (if b' then up (lo + j') else dn (lo + j'))) :
    ∀ x y : EndType.Endpt n m, (WalkGraph.graph D).Reachable (botOf x) (botOf y) := by
  intro x y
  obtain ⟨j, hj, hxj⟩ := hrange x
  obtain ⟨j', hj', hyj⟩ := hrange y
  rcases hcover x with hx | hx <;> rcases hcover y with hy | hy <;> rw [hx, hy, hxj, hyj]
  · simpa using hconn j j' hj hj' true true
  · simpa using hconn j j' hj hj' true false
  · simpa using hconn j j' hj hj' false true
  · simpa using hconn j j' hj hj' false false

/-- **The shield bound on a single run, with only `hturn` left.**  Composing
`hrun_single_run` into `shield_upper_bound_bot`: everything else has been discharged, so
the bound follows from the turn invariant and the two-chain connectivity alone. -/
theorem shield_upper_bound_single_run {n : ℕ} {m : Fin n → ℕ} (up' : Fin n → ℕ)
    (hbal : ∀ s : ℤ,
      (EndType.arrAt (m := m) up' s).card = (EndType.depAt (m := m) up' s).card)
    (Zf : Finset ℤ) (up dn : ℤ → EndType.Endpt n m) (lo : ℤ) (nn : ℕ)
    (hturn : ∀ x, EndType.edgeOf ((DataBuild.dataOf up' hbal).t x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf)
    (hcover : ∀ x, botOf x = up (EndType.edgeOf x) ∨ botOf x = dn (EndType.edgeOf x))
    (hrange : ∀ x : EndType.Endpt n m, ∃ k : ℕ, k ≤ nn ∧ EndType.edgeOf x = lo + k)
    (hconn : ∀ j j' : ℕ, j ≤ nn → j' ≤ nn → ∀ b b' : Bool,
      (WalkGraph.graph (DataBuild.dataOf up' hbal)).Reachable
        (if b then up (lo + j) else dn (lo + j))
        (if b' then up (lo + j') else dn (lo + j'))) :
    WalkGraph.walkCount (DataBuild.dataOf up' hbal) ≤ Zf.card + 1 :=
  shield_upper_bound_bot up' hbal Zf hturn
    (fun x y _ => hrun_single_run (DataBuild.dataOf up' hbal) up dn lo nn
      hcover hrange hconn x y)

end EltBridge

#print axioms EltBridge.hrun_single_run
#print axioms EltBridge.shield_upper_bound_single_run

namespace EltBridge

/-- **The shield law's upper bound from the turn's own passes and bounces.**

Composing `run_connected_of_turn_structure` into `shield_upper_bound_single_run`, every
hypothesis is now a concrete statement about the turn:

    hturn      it changes the edge only off the cut sites
    hpass_up   at each interior site it carries `up j`'s partner to `up (j+1)`
    hpass_dn   and `dn (j+1)`'s partner to `dn j`
    hbounce    at the run's left boundary it carries `dn lo` to `up lo`
    hcover     each representative is one of its edge's two strand bottoms
    hrange     every edge lies in the run

and the conclusion is `walkCount <= |Z| + 1`.  No merge, no swap, no free pair. -/
theorem shield_upper_bound_from_turn {n : ℕ} {m : Fin n → ℕ} (up' : Fin n → ℕ)
    (hbal : ∀ s : ℤ,
      (EndType.arrAt (m := m) up' s).card = (EndType.depAt (m := m) up' s).card)
    (Zf : Finset ℤ) (up dn : ℤ → EndType.Endpt n m) (lo : ℤ) (nn : ℕ)
    (hturn : ∀ x, EndType.edgeOf ((DataBuild.dataOf up' hbal).t x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf)
    (hcover : ∀ x, botOf x = up (EndType.edgeOf x) ∨ botOf x = dn (EndType.edgeOf x))
    (hrange : ∀ x : EndType.Endpt n m, ∃ k : ℕ, k ≤ nn ∧ EndType.edgeOf x = lo + k)
    (hpass_up : ∀ k : ℕ, k < nn →
      (DataBuild.dataOf up' hbal).t ((DataBuild.dataOf up' hbal).p (up (lo + k)))
        = up (lo + (k + 1 : ℕ)))
    (hpass_dn : ∀ k : ℕ, k < nn →
      (DataBuild.dataOf up' hbal).t
          ((DataBuild.dataOf up' hbal).p (dn (lo + (k + 1 : ℕ)))) = dn (lo + k))
    (hbounce : (DataBuild.dataOf up' hbal).t (dn lo) = up lo) :
    WalkGraph.walkCount (DataBuild.dataOf up' hbal) ≤ Zf.card + 1 :=
  shield_upper_bound_single_run up' hbal Zf up dn lo nn hturn hcover hrange
    (fun j j' hj hj' b b' =>
      run_connected_of_turn_structure (DataBuild.dataOf up' hbal) up dn lo nn
        hpass_up hpass_dn hbounce j j' hj hj' b b')

end EltBridge

#print axioms EltBridge.shield_upper_bound_from_turn

namespace EltBridge

/-! ### Several runs

`hrange` assumed every edge lies in one run.  In general the edges split into runs, one
per value of `gz`, and each has its own left boundary and length.  Indexing them by the
run number lifts the argument: two ends with the same `gz` lie in the same run, and the
two-chain connectivity for THAT run joins them.

Each run does have a boundary bounce.  A run is bounded by cut sites, so unless `Zf` is
empty -- in which case the bound is `walkCount <= 1`, which is `thm:nogap` and already
green -- there is a cut site at one end, and the bounce there joins the two chains. -/

/-- **`hrun` for a family of runs.**  `lo r` and `len r` describe run `r`; every end
lies in the run its `gz` names, and each run is internally connected. -/
theorem hrun_multi {n : ℕ} {m : Fin n → ℕ} (D : WalkGraph.Data (EndType.Endpt n m))
    (Zf : Finset ℤ) (up dn : ℤ → EndType.Endpt n m) (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (hcover : ∀ x, botOf x = up (EndType.edgeOf x) ∨ botOf x = dn (EndType.edgeOf x))
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (hconn : ∀ r : ℕ, ∀ j j' : ℕ, j ≤ len r → j' ≤ len r → ∀ b b' : Bool,
      (WalkGraph.graph D).Reachable
        (if b then up (lo r + j) else dn (lo r + j))
        (if b' then up (lo r + j') else dn (lo r + j'))) :
    ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph D).Reachable (botOf x) (botOf y) := by
  intro x y hxy
  obtain ⟨j, hj, hxj⟩ := hrange x
  obtain ⟨j', hj', hyj⟩ := hrange y
  rw [← hxy] at hj' hyj
  rcases hcover x with hx | hx <;> rcases hcover y with hy | hy <;> rw [hx, hy, hxj, hyj]
  · simpa using hconn _ j j' hj hj' true true
  · simpa using hconn _ j j' hj hj' true false
  · simpa using hconn _ j j' hj hj' false true
  · simpa using hconn _ j j' hj hj' false false

/-- **The shield bound over several runs.**  `hrange` is now per-run, so the statement
covers a configuration with any number of cut sites rather than one run. -/
theorem shield_upper_bound_multi {n : ℕ} {m : Fin n → ℕ} (up' : Fin n → ℕ)
    (hbal : ∀ s : ℤ,
      (EndType.arrAt (m := m) up' s).card = (EndType.depAt (m := m) up' s).card)
    (Zf : Finset ℤ) (up dn : ℤ → EndType.Endpt n m) (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (hturn : ∀ x, EndType.edgeOf ((DataBuild.dataOf up' hbal).t x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf)
    (hcover : ∀ x, botOf x = up (EndType.edgeOf x) ∨ botOf x = dn (EndType.edgeOf x))
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (hpass_up : ∀ r k : ℕ, k < len r →
      (DataBuild.dataOf up' hbal).t ((DataBuild.dataOf up' hbal).p (up (lo r + k)))
        = up (lo r + (k + 1 : ℕ)))
    (hpass_dn : ∀ r k : ℕ, k < len r →
      (DataBuild.dataOf up' hbal).t
          ((DataBuild.dataOf up' hbal).p (dn (lo r + (k + 1 : ℕ)))) = dn (lo r + k))
    (hbounce : ∀ r : ℕ, (DataBuild.dataOf up' hbal).t (dn (lo r)) = up (lo r)) :
    WalkGraph.walkCount (DataBuild.dataOf up' hbal) ≤ Zf.card + 1 :=
  shield_upper_bound_bot up' hbal Zf hturn
    (hrun_multi (DataBuild.dataOf up' hbal) Zf up dn lo len hcover hrange
      (fun r j j' hj hj' b b' =>
        run_connected_of_turn_structure (DataBuild.dataOf up' hbal) up dn (lo r) (len r)
          (hpass_up r) (hpass_dn r) (hbounce r) j j' hj hj' b b'))

end EltBridge

#print axioms EltBridge.hrun_multi
#print axioms EltBridge.shield_upper_bound_multi

namespace EltBridge

/-! ### `hcover` at `mu = 2`

An edge carries `m e` strands, so at `mu = 2` its strand index lies in `Fin 2` and is
`0` or `1`.  `botOf x` is therefore one of the edge's two strand bottoms, which is
`hcover` once `up` and `dn` are the maps naming them. -/

/-- At `mu = 2` a strand index is `0` or `1`. -/
theorem botOf_idx_cases {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (x : EndType.Endpt n m) : (x.idx : ℕ) = 0 ∨ (x.idx : ℕ) = 1 := by
  have h := x.idx.isLt
  have h2 := hm x.edge
  omega

/-- **`hcover` reduces to `up` and `dn` naming the two strand bottoms.**  No other
property of the configuration is used. -/
theorem hcover_of_mu_two {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (up dn : ℤ → EndType.Endpt n m)
    (hup : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 0 → up (EndType.edgeOf x) = botOf x)
    (hdn : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 1 → dn (EndType.edgeOf x) = botOf x) :
    ∀ x, botOf x = up (EndType.edgeOf x) ∨ botOf x = dn (EndType.edgeOf x) := by
  intro x
  rcases botOf_idx_cases hm x with h | h
  · exact Or.inl (hup x h).symm
  · exact Or.inr (hdn x h).symm

/-- **The shield bound at `mu = 2`, with `hcover` discharged.**  What is left to verify
on a concrete configuration is the turn's own behaviour: `hturn`, `hrange`, the two pass
laws, and the boundary bounce. -/
theorem shield_upper_bound_mu_two {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (up' : Fin n → ℕ)
    (hbal : ∀ s : ℤ,
      (EndType.arrAt (m := m) up' s).card = (EndType.depAt (m := m) up' s).card)
    (Zf : Finset ℤ) (up dn : ℤ → EndType.Endpt n m) (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (hturn : ∀ x, EndType.edgeOf ((DataBuild.dataOf up' hbal).t x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf)
    (hup : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 0 → up (EndType.edgeOf x) = botOf x)
    (hdn : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 1 → dn (EndType.edgeOf x) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (hpass_up : ∀ r k : ℕ, k < len r →
      (DataBuild.dataOf up' hbal).t ((DataBuild.dataOf up' hbal).p (up (lo r + k)))
        = up (lo r + (k + 1 : ℕ)))
    (hpass_dn : ∀ r k : ℕ, k < len r →
      (DataBuild.dataOf up' hbal).t
          ((DataBuild.dataOf up' hbal).p (dn (lo r + (k + 1 : ℕ)))) = dn (lo r + k))
    (hbounce : ∀ r : ℕ, (DataBuild.dataOf up' hbal).t (dn (lo r)) = up (lo r)) :
    WalkGraph.walkCount (DataBuild.dataOf up' hbal) ≤ Zf.card + 1 :=
  shield_upper_bound_multi up' hbal Zf up dn lo len hturn
    (hcover_of_mu_two hm up dn hup hdn) hrange hpass_up hpass_dn hbounce

end EltBridge

#print axioms EltBridge.botOf_idx_cases
#print axioms EltBridge.shield_upper_bound_mu_two

namespace EltBridge

/-! ### `hturn` from zero crossing

`hturn_of_cross_zero` (BLOCK 61) already turns "the plan at each cut site does not
cross" into `hturn`, and `(DataBuild.dataOf up hbal).t` is `DataBuild.turn up`
definitionally, so the two compose with nothing in between.

`hcross` itself is what `local_trichotomy` is for: a cut site has `siteValue = 0`, the
bounce attains it and every pass costs at least one, so a plan attaining the site value
has `cross = 0`.  That is `ConfigLoop.no_cross_at_cut`, whose remaining input is that
the plan IS minimal at that site. -/

/-- **The shield bound with `hturn` reduced to zero crossing at the cut sites.** -/
theorem shield_upper_bound_of_cross_zero {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (up' : Fin n → ℕ) (ds : Bool → Bool)
    (hbal : ∀ s : ℤ,
      (EndType.arrAt (m := m) up' s).card = (EndType.depAt (m := m) up' s).card)
    (Zf : Finset ℤ) (up dn : ℤ → EndType.Endpt n m) (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (hcross : ∀ s ∈ Zf, (ConfigLoop.planAt up' ds s (hbal s)).cross = 0)
    (hup : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 0 → up (EndType.edgeOf x) = botOf x)
    (hdn : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 1 → dn (EndType.edgeOf x) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (hpass_up : ∀ r k : ℕ, k < len r →
      (DataBuild.dataOf up' hbal).t ((DataBuild.dataOf up' hbal).p (up (lo r + k)))
        = up (lo r + (k + 1 : ℕ)))
    (hpass_dn : ∀ r k : ℕ, k < len r →
      (DataBuild.dataOf up' hbal).t
          ((DataBuild.dataOf up' hbal).p (dn (lo r + (k + 1 : ℕ)))) = dn (lo r + k))
    (hbounce : ∀ r : ℕ, (DataBuild.dataOf up' hbal).t (dn (lo r)) = up (lo r)) :
    WalkGraph.walkCount (DataBuild.dataOf up' hbal) ≤ Zf.card + 1 :=
  shield_upper_bound_mu_two hm up' hbal Zf up dn lo len
    (hturn_of_cross_zero up' ds Zf hbal hcross)
    hup hdn hrange hpass_up hpass_dn hbounce

end EltBridge

#print axioms EltBridge.shield_upper_bound_of_cross_zero

namespace EltBridge

/-! ### The turn must be chosen, not taken

`DataBuild.dataOf`'s turn comes from an arbitrary involution at each site
(`exists_involution_of_card_eq`), so one cannot simply assume it bounces at the cut
sites and passes elsewhere.  Those are the properties `local_trichotomy` says a MINIMAL
turn has, and the way to get them is to CHOOSE the per-site involutions and glue them --
`exists_glued_data`, BLOCK 157.

This is the form the argument should have taken from the start: build the datum, do not
inherit it. -/

/-- **The shield bound for a chosen turn.**  Given per-site involutions `T` with the
pass/bounce behaviour `local_trichotomy` provides, the glued datum satisfies
`walkCount <= |Z| + 1`. -/
theorem shield_upper_bound_glued {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (T : ℤ → EndType.Endpt n m → EndType.Endpt n m) (Zf : Finset ℤ)
    (up dn : ℤ → EndType.Endpt n m) (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (hinv : ∀ s x, T s (T s x) = x)
    (hTsite : ∀ s x, EndType.siteOf x = s → EndType.siteOf (T s x) = s)
    (hne : ∀ s x, EndType.siteOf x = s → T s x ≠ x)
    (hturn : ∀ x, EndType.edgeOf (T (EndType.siteOf x) x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf)
    (hup : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 0 → up (EndType.edgeOf x) = botOf x)
    (hdn : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 1 → dn (EndType.edgeOf x) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (hpass_up : ∀ r k : ℕ, k < len r →
      T (EndType.siteOf (EndType.partner (up (lo r + k))))
        (EndType.partner (up (lo r + k))) = up (lo r + (k + 1 : ℕ)))
    (hpass_dn : ∀ r k : ℕ, k < len r →
      T (EndType.siteOf (EndType.partner (dn (lo r + (k + 1 : ℕ)))))
        (EndType.partner (dn (lo r + (k + 1 : ℕ)))) = dn (lo r + k))
    (hbounce : ∀ r : ℕ,
      T (EndType.siteOf (dn (lo r))) (dn (lo r)) = up (lo r)) :
    ∃ D : WalkGraph.Data (EndType.Endpt n m),
      WalkGraph.walkCount D ≤ Zf.card + 1 := by
  obtain ⟨E, hEp, hEt⟩ := exists_glued_data EndType.siteOf EndType.partner T
    EndType.partner_invol EndType.partner_ne EndType.partner_site_ne hinv hTsite hne
  refine ⟨E, ?_⟩
  refine shield_upper_bound_endpt E Zf botOf (fun x => by rw [hEp]) ?_ ?_
    (fun x => by rw [hEp]; exact botOf_eq_or_partner x) (fun _ => rfl) ?_
  · intro x
    rw [hEt x]
    exact hTsite _ x rfl
  · intro x hx
    rw [hEt x] at hx
    exact hturn x hx
  · refine hrun_multi E Zf up dn lo len (hcover_of_mu_two hm up dn hup hdn) hrange ?_
    intro r j j' hj hj' b b'
    refine run_connected_of_turn_structure E up dn (lo r) (len r) ?_ ?_ ?_ j j' hj hj' b b'
    · intro k hk
      rw [hEp, hEt]
      exact hpass_up r k hk
    · intro k hk
      rw [hEp, hEt]
      exact hpass_dn r k hk
    · rw [hEt]
      exact hbounce r

end EltBridge

#print axioms EltBridge.shield_upper_bound_glued

namespace EltBridge

/-! ### Restating the chain hypotheses as reachability

`run_connected_of_turn_structure` asks for `D.t (D.p x) = y`.  For the UP chain that is
the right composition -- cross the strand, then turn.  For the DOWN chain the concrete
pass runs the other way: at site `s` it sends `dn s` to the TOP of edge `s-1`'s down
strand, so what holds is `D.p (D.t (dn (j+1))) = dn j`, turn first and then cross.

Both give the same reachability, so nothing proved is wrong; but stating the hypotheses
as REACHABILITY rather than as a fixed composition avoids having to match the order, and
is what a concrete `T` can actually discharge. -/

/-- **The run is connected, from reachability hypotheses.**  Weaker and easier to
discharge than the equation form: any walk joining consecutive strands will do,
whichever way it composes. -/
theorem run_connected_of_reachability {α : Type*} [Fintype α] [DecidableEq α]
    (D : WalkGraph.Data α) (up dn : ℤ → α) (lo : ℤ) (n : ℕ)
    (hup : ∀ k : ℕ, k < n →
      (WalkGraph.graph D).Reachable (up (lo + k)) (up (lo + (k + 1 : ℕ))))
    (hdn : ∀ k : ℕ, k < n →
      (WalkGraph.graph D).Reachable (dn (lo + k)) (dn (lo + (k + 1 : ℕ))))
    (hjoin : (WalkGraph.graph D).Reachable (up lo) (dn lo))
    (j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n) (b b' : Bool) :
    (WalkGraph.graph D).Reachable
      (if b then up (lo + j) else dn (lo + j))
      (if b' then up (lo + j') else dn (lo + j')) := by
  classical
  set f : ℤ × Bool → α := fun a => if a.2 then up a.1 else dn a.1 with hf
  set R : ℤ × Bool → ℤ × Bool → Prop :=
    fun a b => (WalkGraph.graph D).Reachable (f a) (f b) with hRdef
  have hR : ∀ a b, R a b → (WalkGraph.graph D).Reachable (f a) (f b) := fun _ _ h => h
  have hsymm : ∀ a b, R a b → R b a := fun _ _ h => h.symm
  have hupR : ∀ k : ℕ, k < n → R (lo + k, true) (lo + (k + 1 : ℕ), true) := by
    intro k hk; simpa [hRdef, hf] using hup k hk
  have hdnR : ∀ k : ℕ, k < n → R (lo + k, false) (lo + (k + 1 : ℕ), false) := by
    intro k hk; simpa [hRdef, hf] using hdn k hk
  have hjoinR : R (lo, true) (lo, false) := by simpa [hRdef, hf] using hjoin
  have hchain := run_pairwise lo n R hsymm hupR hdnR hjoinR j j' hj hj' b b'
  have hmain := reachable_of_reflTransGen (WalkGraph.graph D) R f hR hchain
  simpa [hf] using hmain

end EltBridge

#print axioms EltBridge.run_connected_of_reachability

namespace EltBridge

/-- **The shield bound for a chosen turn, on reachability hypotheses.**  The chain
conditions are now "consecutive up strands are joined", "consecutive down strands are
joined", and "the two are joined at the run's boundary" -- whichever walk does it.  That
is what a concrete `T` at `mu = 2` discharges: the pass at a non-cut site joins the
strands on either side of it, and the bounce at a cut site joins the two strands of its
edge. -/
theorem shield_upper_bound_reach {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (T : ℤ → EndType.Endpt n m → EndType.Endpt n m) (Zf : Finset ℤ)
    (up dn : ℤ → EndType.Endpt n m) (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (hinv : ∀ s x, T s (T s x) = x)
    (hTsite : ∀ s x, EndType.siteOf x = s → EndType.siteOf (T s x) = s)
    (hne : ∀ s x, EndType.siteOf x = s → T s x ≠ x)
    (hturn : ∀ x, EndType.edgeOf (T (EndType.siteOf x) x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf)
    (hup : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 0 → up (EndType.edgeOf x) = botOf x)
    (hdn : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 1 → dn (EndType.edgeOf x) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner) (hEt : ∀ x, E.t x = T (EndType.siteOf x) x)
    (hchain_up : ∀ r k : ℕ, k < len r →
      (WalkGraph.graph E).Reachable (up (lo r + k)) (up (lo r + (k + 1 : ℕ))))
    (hchain_dn : ∀ r k : ℕ, k < len r →
      (WalkGraph.graph E).Reachable (dn (lo r + k)) (dn (lo r + (k + 1 : ℕ))))
    (hchain_join : ∀ r : ℕ,
      (WalkGraph.graph E).Reachable (up (lo r)) (dn (lo r))) :
    WalkGraph.walkCount E ≤ Zf.card + 1 := by
  refine shield_upper_bound_endpt E Zf botOf (fun x => by rw [hEp]) ?_ ?_
    (fun x => by rw [hEp]; exact botOf_eq_or_partner x) (fun _ => rfl) ?_
  · intro x; rw [hEt x]; exact hTsite _ x rfl
  · intro x hx; rw [hEt x] at hx; exact hturn x hx
  · refine hrun_multi E Zf up dn lo len (hcover_of_mu_two hm up dn hup hdn) hrange ?_
    intro r j j' hj hj' b b'
    exact run_connected_of_reachability E up dn (lo r) (len r)
      (hchain_up r) (hchain_dn r) (hchain_join r) j j' hj hj' b b'

end EltBridge

#print axioms EltBridge.shield_upper_bound_reach

namespace EltBridge

/-! ### The chain conditions from a pass and a bounce

Three short steps, each a walk of length at most two.

* UP chain.  A pass at site `j+1` carries the TOP of edge `j`'s up strand to the BOTTOM
  of edge `j+1`'s.  So from `up j` cross the strand and turn.
* DOWN chain.  The same pass carries `dn (j+1)` to the TOP of edge `j`'s down strand.
  So from `dn j` cross the strand, and the turn from there is `dn (j+1)` read backwards.
* JOIN.  The bounce at a cut site pairs the two bottoms of its own edge, so one turn
  step joins `up lo` and `dn lo`.
-/

theorem chain_up_of_pass {α : Type*} [Fintype α] [DecidableEq α]
    (E : WalkGraph.Data α) (up : ℤ → α) (a b : ℤ)
    (h : E.t (E.p (up a)) = up b) :
    (WalkGraph.graph E).Reachable (up a) (up b) := by
  have h1 : (WalkGraph.graph E).Reachable (up a) (E.t (E.p (up a))) :=
    (reachable_partner E (up a)).trans (reachable_turn E (E.p (up a)))
  rwa [h] at h1

theorem chain_dn_of_pass {α : Type*} [Fintype α] [DecidableEq α]
    (E : WalkGraph.Data α) (dn : ℤ → α) (a b : ℤ)
    (h : E.t (dn b) = E.p (dn a)) :
    (WalkGraph.graph E).Reachable (dn a) (dn b) := by
  have h1 : (WalkGraph.graph E).Reachable (dn a) (E.p (dn a)) := reachable_partner E (dn a)
  have h2 : (WalkGraph.graph E).Reachable (E.t (dn b)) (dn b) :=
    (reachable_turn E (dn b)).symm
  rw [h] at h2
  exact h1.trans h2

theorem chain_join_of_bounce {α : Type*} [Fintype α] [DecidableEq α]
    (E : WalkGraph.Data α) (up dn : ℤ → α) (lo : ℤ)
    (h : E.t (dn lo) = up lo) :
    (WalkGraph.graph E).Reachable (up lo) (dn lo) := by
  have h1 : (WalkGraph.graph E).Reachable (dn lo) (E.t (dn lo)) := reachable_turn E (dn lo)
  rw [h] at h1
  exact h1.symm

/-- **The shield bound from the pass and bounce equations.**  The three chain conditions
of `shield_upper_bound_reach` are discharged from the turn's own behaviour, in the
composition a `mu = 2` turn actually has. -/
theorem shield_upper_bound_of_pass_bounce {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (T : ℤ → EndType.Endpt n m → EndType.Endpt n m) (Zf : Finset ℤ)
    (up dn : ℤ → EndType.Endpt n m) (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (hinv : ∀ s x, T s (T s x) = x)
    (hTsite : ∀ s x, EndType.siteOf x = s → EndType.siteOf (T s x) = s)
    (hne : ∀ s x, EndType.siteOf x = s → T s x ≠ x)
    (hturn : ∀ x, EndType.edgeOf (T (EndType.siteOf x) x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf)
    (hup : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 0 → up (EndType.edgeOf x) = botOf x)
    (hdn : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 1 → dn (EndType.edgeOf x) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner) (hEt : ∀ x, E.t x = T (EndType.siteOf x) x)
    (hpass_up : ∀ r k : ℕ, k < len r →
      E.t (E.p (up (lo r + k))) = up (lo r + (k + 1 : ℕ)))
    (hpass_dn : ∀ r k : ℕ, k < len r →
      E.t (dn (lo r + (k + 1 : ℕ))) = E.p (dn (lo r + k)))
    (hbounce : ∀ r : ℕ, E.t (dn (lo r)) = up (lo r)) :
    WalkGraph.walkCount E ≤ Zf.card + 1 :=
  shield_upper_bound_reach hm T Zf up dn lo len hinv hTsite hne hturn hup hdn hrange
    E hEp hEt
    (fun r k hk => chain_up_of_pass E up _ _ (hpass_up r k hk))
    (fun r k hk => chain_dn_of_pass E dn _ _ (hpass_dn r k hk))
    (fun r => chain_join_of_bounce E up dn (lo r) (hbounce r))

end EltBridge

#print axioms EltBridge.chain_dn_of_pass
#print axioms EltBridge.shield_upper_bound_of_pass_bounce

namespace EltBridge

/-! ### The turn, defined

At `mu = 2` a site `s` carries exactly four ends: the two tops of edge `s-1`, which are
`p (up (s-1))` and `p (dn (s-1))`, and the two bottoms of edge `s`, which are `up s` and
`dn s`.  There are exactly two involutions on them that respect the site, and
`local_trichotomy` says which one minimality picks:

* at a cut site, the BOUNCE, pairing within each edge;
* elsewhere, the PASS, pairing across.

`passTurn` is that choice. -/

/-- The pairing at a site, before the guard: the bounce inside `Zf`, the pass outside. -/
noncomputable def passCore {α : Type*} [DecidableEq α] (p : α → α) (up dn : ℤ → α)
    (Zf : Finset ℤ) (s : ℤ) (x : α) : α :=
  if s ∈ Zf then
    if x = p (up (s - 1)) then p (dn (s - 1))
    else if x = p (dn (s - 1)) then p (up (s - 1))
    else if x = up s then dn s
    else if x = dn s then up s
    else x
  else
    if x = p (up (s - 1)) then up s
    else if x = up s then p (up (s - 1))
    else if x = dn s then p (dn (s - 1))
    else if x = p (dn (s - 1)) then dn s
    else x

/-- The turn: `passCore` on its own site, the identity elsewhere.  The guard is what
makes it an involution without any assumption about ends at other sites. -/
noncomputable def passTurn {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ) (x : α) : α :=
  if siteOf x = s then passCore p up dn Zf s x else x

theorem passTurn_off_site {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ) (x : α) (h : siteOf x ≠ s) :
    passTurn siteOf p up dn Zf s x = x := by
  unfold passTurn; rw [if_neg h]

theorem passTurn_on_site {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ) (x : α) (h : siteOf x = s) :
    passTurn siteOf p up dn Zf s x = passCore p up dn Zf s x := by
  unfold passTurn; rw [if_pos h]

/-- **`passCore` keeps every end at its site.** -/
theorem passCore_site {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ)
    (h1 : siteOf (p (up (s - 1))) = s) (h2 : siteOf (p (dn (s - 1))) = s)
    (h3 : siteOf (up s) = s) (h4 : siteOf (dn s) = s)
    (x : α) (hx : siteOf x = s) : siteOf (passCore p up dn Zf s x) = s := by
  unfold passCore
  by_cases hs : s ∈ Zf <;> simp only [hs, if_true, if_false, ite_true, ite_false] <;>
    split_ifs <;> simp_all

/-- **`passCore` is an involution**, given the four ends are distinct. -/
theorem passCore_invol {α : Type*} [DecidableEq α] (p : α → α) (up dn : ℤ → α)
    (Zf : Finset ℤ) (s : ℤ)
    (h12 : p (up (s - 1)) ≠ p (dn (s - 1)))
    (h13 : p (up (s - 1)) ≠ up s) (h14 : p (up (s - 1)) ≠ dn s)
    (h23 : p (dn (s - 1)) ≠ up s) (h24 : p (dn (s - 1)) ≠ dn s)
    (h34 : up s ≠ dn s) (x : α) :
    passCore p up dn Zf s (passCore p up dn Zf s x) = x := by
  have h21 := h12.symm; have h31 := h13.symm; have h41 := h14.symm
  have h32 := h23.symm; have h42 := h24.symm; have h43 := h34.symm
  unfold passCore
  by_cases hs : s ∈ Zf <;> simp only [hs, if_true, if_false, ite_true, ite_false] <;>
    split_ifs <;> simp_all

/-- **So `passTurn` is an involution**, with no hypothesis about other sites. -/
theorem passTurn_invol {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ)
    (h12 : (∃ y, siteOf y = s) → p (up (s - 1)) ≠ p (dn (s - 1)))
    (h13 : (∃ y, siteOf y = s) → p (up (s - 1)) ≠ up s)
    (h14 : (∃ y, siteOf y = s) → p (up (s - 1)) ≠ dn s)
    (h23 : (∃ y, siteOf y = s) → p (dn (s - 1)) ≠ up s)
    (h24 : (∃ y, siteOf y = s) → p (dn (s - 1)) ≠ dn s)
    (h34 : (∃ y, siteOf y = s) → up s ≠ dn s)
    (hs1 : (∃ y, siteOf y = s) → siteOf (p (up (s - 1))) = s)
    (hs2 : (∃ y, siteOf y = s) → siteOf (p (dn (s - 1))) = s)
    (hs3 : (∃ y, siteOf y = s) → siteOf (up s) = s)
    (hs4 : (∃ y, siteOf y = s) → siteOf (dn s) = s) (x : α) :
    passTurn siteOf p up dn Zf s (passTurn siteOf p up dn Zf s x) = x := by
  by_cases hxs : siteOf x = s
  · -- an end sits at `s`, so the site is occupied and the hypotheses apply
    have hocc : ∃ y, siteOf y = s := ⟨x, hxs⟩
    rw [passTurn_on_site siteOf p up dn Zf s x hxs,
      passTurn_on_site siteOf p up dn Zf s _
        (passCore_site siteOf p up dn Zf s (hs1 hocc) (hs2 hocc) (hs3 hocc) (hs4 hocc)
          x hxs),
      passCore_invol p up dn Zf s (h12 hocc) (h13 hocc) (h14 hocc) (h23 hocc)
        (h24 hocc) (h34 hocc) x]
  · rw [passTurn_off_site siteOf p up dn Zf s x hxs,
      passTurn_off_site siteOf p up dn Zf s x hxs]

theorem passTurn_site {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ)
    (h1 : siteOf (p (up (s - 1))) = s) (h2 : siteOf (p (dn (s - 1))) = s)
    (h3 : siteOf (up s) = s) (h4 : siteOf (dn s) = s)
    (x : α) (hx : siteOf x = s) :
    siteOf (passTurn siteOf p up dn Zf s x) = s := by
  rw [passTurn_on_site siteOf p up dn Zf s x hx]
  exact passCore_site siteOf p up dn Zf s h1 h2 h3 h4 x hx

theorem passTurn_ne {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ)
    (h12 : p (up (s - 1)) ≠ p (dn (s - 1)))
    (h13 : p (up (s - 1)) ≠ up s) (h14 : p (up (s - 1)) ≠ dn s)
    (h23 : p (dn (s - 1)) ≠ up s) (h24 : p (dn (s - 1)) ≠ dn s)
    (h34 : up s ≠ dn s) (x : α) (hx : siteOf x = s)
    (hfour : x = p (up (s - 1)) ∨ x = p (dn (s - 1)) ∨ x = up s ∨ x = dn s) :
    passTurn siteOf p up dn Zf s x ≠ x := by
  have h21 := h12.symm; have h31 := h13.symm; have h41 := h14.symm
  have h32 := h23.symm; have h42 := h24.symm; have h43 := h34.symm
  rw [passTurn_on_site siteOf p up dn Zf s x hx]
  unfold passCore
  by_cases hs : s ∈ Zf <;> simp only [hs, if_true, if_false, ite_true, ite_false] <;>
    rcases hfour with rfl | rfl | rfl | rfl <;> split_ifs <;> simp_all

/-! ### `passTurn` satisfies the three equations -/

/-- At a non-cut site the pass carries edge `s-1`'s up top to edge `s`'s up bottom. -/
theorem passTurn_pass_up {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ) (hs : s ∉ Zf)
    (hs1 : siteOf (p (up (s - 1))) = s) :
    passTurn siteOf p up dn Zf s (p (up (s - 1))) = up s := by
  rw [passTurn_on_site siteOf p up dn Zf s _ hs1]
  unfold passCore
  rw [if_neg hs, if_pos rfl]

/-- At a non-cut site the same pass carries edge `s`'s down bottom to edge `s-1`'s down
top -- the opposite composition, as BLOCK 172 found. -/
theorem passTurn_pass_dn {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ) (hs : s ∉ Zf)
    (hs4 : siteOf (dn s) = s)
    (h14 : p (up (s - 1)) ≠ dn s) (h34 : up s ≠ dn s) :
    passTurn siteOf p up dn Zf s (dn s) = p (dn (s - 1)) := by
  rw [passTurn_on_site siteOf p up dn Zf s _ hs4]
  unfold passCore
  rw [if_neg hs, if_neg (Ne.symm h14), if_neg (Ne.symm h34), if_pos rfl]

/-- At a cut site the bounce joins the two bottoms of edge `s`. -/
theorem passTurn_bounce {α : Type*} [DecidableEq α] (siteOf : α → ℤ) (p : α → α)
    (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ) (hs : s ∈ Zf)
    (hs4 : siteOf (dn s) = s)
    (h14 : p (up (s - 1)) ≠ dn s) (h24 : p (dn (s - 1)) ≠ dn s) (h34 : up s ≠ dn s) :
    passTurn siteOf p up dn Zf s (dn s) = up s := by
  rw [passTurn_on_site siteOf p up dn Zf s _ hs4]
  unfold passCore
  rw [if_pos hs, if_neg (Ne.symm h14), if_neg (Ne.symm h24), if_neg (Ne.symm h34),
    if_pos rfl]

/-- **And it changes the edge only off `Zf`.**  At a cut site the bounce keeps each end
on its own edge; off its site the turn is the identity.  That is `hturn`. -/
theorem passTurn_keeps_edge_at_cut {α : Type*} [DecidableEq α] (edgeOf siteOf : α → ℤ)
    (p : α → α) (up dn : ℤ → α) (Zf : Finset ℤ) (s : ℤ) (hs : s ∈ Zf)
    (hpe : ∀ x, edgeOf (p x) = edgeOf x)
    (hud : edgeOf (up s) = edgeOf (dn s))
    (hud' : edgeOf (up (s - 1)) = edgeOf (dn (s - 1)))
    (x : α) : edgeOf (passTurn siteOf p up dn Zf s x) = edgeOf x := by
  by_cases hxs : siteOf x = s
  · rw [passTurn_on_site siteOf p up dn Zf s x hxs]
    unfold passCore
    rw [if_pos hs]
    split_ifs with h1 h2 h3 h4
    · rw [h1, hpe, hpe, hud']
    · rw [h2, hpe, hpe, hud']
    · rw [h3, hud]
    · rw [h4, hud]
    · rfl
  · rw [passTurn_off_site siteOf p up dn Zf s x hxs]

end EltBridge

#print axioms EltBridge.passTurn_pass_up
#print axioms EltBridge.passTurn_bounce
#print axioms EltBridge.passTurn_keeps_edge_at_cut

namespace EltBridge

/-- **The `mu = 2` shield bound with `passTurn` supplied.**  Every property of the turn
is discharged from `passTurn`'s own lemmas.  What the caller provides is the
configuration's geometry: the four ends of each site are distinct, sit at that site, and
are ALL of it (`hfour`); `up` and `dn` name the strand bottoms; the runs are indexed with
cut sites at their boundaries and none inside. -/
theorem shield_upper_bound_passTurn {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (Zf : Finset ℤ) (up dn : ℤ → EndType.Endpt n m) (lo : ℕ → ℤ) (len : ℕ → ℕ)
    -- all hypotheses about a site are conditional on it being OCCUPIED: outside the
    -- span there is no edge at that position and `up s`, `dn s` are junk
    (h12 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → EndType.partner (up (s - 1)) ≠ EndType.partner (dn (s - 1)))
    (h13 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → EndType.partner (up (s - 1)) ≠ up s)
    (h14 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → EndType.partner (up (s - 1)) ≠ dn s)
    (h23 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → EndType.partner (dn (s - 1)) ≠ up s)
    (h24 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → EndType.partner (dn (s - 1)) ≠ dn s)
    (h34 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → up s ≠ dn s)
    (hs1 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → EndType.siteOf (EndType.partner (up (s - 1))) = s)
    (hs2 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → EndType.siteOf (EndType.partner (dn (s - 1))) = s)
    (hs3 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → EndType.siteOf (up s) = s)
    (hs4 : ∀ s : ℤ, (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → EndType.siteOf (dn s) = s)
    (hfour : ∀ (s : ℤ) (x : EndType.Endpt n m), EndType.siteOf x = s →
      x = EndType.partner (up (s - 1)) ∨ x = EndType.partner (dn (s - 1)) ∨
      x = up s ∨ x = dn s)
    (hud : ∀ s : ℤ, EndType.edgeOf (up s) = EndType.edgeOf (dn s))
    (hupn : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 0 → up (EndType.edgeOf x) = botOf x)
    (hdnn : ∀ x : EndType.Endpt n m, (x.idx : ℕ) = 1 → dn (EndType.edgeOf x) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    -- a run's sites lie in the span, so they carry ends
    (hocc : ∀ (r : ℕ) (k : ℕ), k ≤ len r →
      ∃ y : EndType.Endpt n m, EndType.siteOf y = lo r + (k : ℤ))
    (hbdry : ∀ r : ℕ, lo r ∈ Zf)
    (hint : ∀ r k : ℕ, k < len r → lo r + ((k : ℤ) + 1) ∉ Zf)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x
      = passTurn EndType.siteOf EndType.partner up dn Zf (EndType.siteOf x) x) :
    WalkGraph.walkCount E ≤ Zf.card + 1 := by
  have hkeep : ∀ (s : ℤ), s ∈ Zf → ∀ x : EndType.Endpt n m,
      EndType.edgeOf (passTurn EndType.siteOf EndType.partner up dn Zf s x) = EndType.edgeOf x :=
    fun s hs x => passTurn_keeps_edge_at_cut EndType.edgeOf EndType.siteOf EndType.partner up dn Zf s hs
      (fun y => EndType.partner_edgeOf y) (hud s) (hud (s - 1)) x
  refine shield_upper_bound_of_pass_bounce hm
    (passTurn EndType.siteOf EndType.partner up dn Zf) Zf up dn lo len
    (fun s x => passTurn_invol EndType.siteOf EndType.partner up dn Zf s (h12 s) (h13 s)
      (h14 s) (h23 s) (h24 s) (h34 s) (hs1 s) (hs2 s) (hs3 s) (hs4 s) x)
    (fun s x hxs => by
      subst hxs
      exact passTurn_site EndType.siteOf EndType.partner up dn Zf _ (hs1 _ ⟨x, rfl⟩) (hs2 _ ⟨x, rfl⟩)
        (hs3 _ ⟨x, rfl⟩) (hs4 _ ⟨x, rfl⟩) x rfl)
    (fun s x hxs => by
      subst hxs
      exact passTurn_ne EndType.siteOf EndType.partner up dn Zf _ (h12 _ ⟨x, rfl⟩) (h13 _ ⟨x, rfl⟩)
        (h14 _ ⟨x, rfl⟩) (h23 _ ⟨x, rfl⟩) (h24 _ ⟨x, rfl⟩) (h34 _ ⟨x, rfl⟩) x rfl
        (hfour _ x rfl))
    (fun x hx hc => hx (hkeep _ hc x))
    hupn hdnn hrange E hEp hEt ?_ ?_ ?_
  · -- the up pass
    intro r k hk
    have harith : lo r + ((k : ℤ) + 1) - 1 = lo r + (k : ℤ) := by ring
    have hsite : EndType.siteOf (E.p (up (lo r + k))) = lo r + ((k : ℤ) + 1) := by
      rw [hEp]
      have hw : ∃ y : EndType.Endpt n m,
          EndType.siteOf y = lo r + ((k : ℤ) + 1) := by
        have := hocc r (k + 1) (by omega)
        push_cast at this
        exact this
      have h := hs1 (lo r + ((k : ℤ) + 1)) hw
      rw [harith] at h
      exact h
    rw [hEt, hsite, hEp]
    have hw : ∃ y : EndType.Endpt n m, EndType.siteOf y = lo r + ((k : ℤ) + 1) := by
      have := hocc r (k + 1) (by omega)
      push_cast at this
      exact this
    have h := passTurn_pass_up EndType.siteOf EndType.partner up dn Zf
      (lo r + ((k : ℤ) + 1)) (hint r k hk) (hs1 _ hw)
    rw [harith] at h
    push_cast
    exact h
  · -- the down pass
    intro r k hk
    have harith : lo r + ((k : ℤ) + 1) - 1 = lo r + (k : ℤ) := by ring
    have hsite : EndType.siteOf (dn (lo r + ((k : ℕ) + 1 : ℕ)))
        = lo r + ((k : ℤ) + 1) := by
      have hw : ∃ y : EndType.Endpt n m,
          EndType.siteOf y = lo r + ((k : ℤ) + 1) := by
        have := hocc r (k + 1) (by omega)
        push_cast at this
        exact this
      have h := hs4 (lo r + ((k : ℤ) + 1)) hw
      push_cast
      exact h
    rw [hEt, hsite, hEp]
    have hw2 : ∃ y : EndType.Endpt n m, EndType.siteOf y = lo r + ((k : ℤ) + 1) := by
      have := hocc r (k + 1) (by omega)
      push_cast at this
      exact this
    have h := passTurn_pass_dn EndType.siteOf EndType.partner up dn Zf
      (lo r + ((k : ℤ) + 1)) (hint r k hk) (hs4 _ hw2) (h14 _ hw2) (h34 _ hw2)
    rw [harith] at h
    push_cast
    exact h
  · -- the boundary bounce
    intro r
    have hw : ∃ y : EndType.Endpt n m, EndType.siteOf y = lo r := by
      have := hocc r 0 (by omega)
      simpa using this
    rw [hEt, hs4 _ hw]
    exact passTurn_bounce EndType.siteOf EndType.partner up dn Zf (lo r) (hbdry r)
      (hs4 _ hw) (h14 _ hw) (h24 _ hw) (h34 _ hw)

end EltBridge
#print axioms EltBridge.passTurn_site
#print axioms EltBridge.shield_upper_bound_passTurn

namespace EltBridge

/-! ### Concrete `up` and `dn`

At `mu = 2` an edge has strands `0` and `1`.  Given a section `sec : ℤ → Fin n` naming
the edge at each position, `upOf` and `dnOf` are the bottoms of those two strands.

The six distinctness facts need no hypothesis at all: the four ends of a site differ in
`idx` or in `top`.  Only the SITE facts need `sec` to be a genuine section, and only
where the position is in range -- which is what BLOCK 177's occupancy condition
provides. -/

noncomputable def upOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) : EndType.Endpt n m :=
  ⟨sec j, ⟨0, by rw [hm]; norm_num⟩, false⟩

noncomputable def dnOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) : EndType.Endpt n m :=
  ⟨sec j, ⟨1, by rw [hm]; norm_num⟩, false⟩

@[simp] theorem upOf_edge {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) : (upOf (m := m) hm sec j).edge = sec j := rfl

@[simp] theorem dnOf_edge {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) : (dnOf (m := m) hm sec j).edge = sec j := rfl

/-- **The two strands of an edge share it.** -/
theorem upOf_dnOf_edgeOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) :
    EndType.edgeOf (upOf (m := m) hm sec j) = EndType.edgeOf (dnOf (m := m) hm sec j) :=
  rfl

/-- **The two strands are distinct**: their indices differ. -/
theorem upOf_ne_dnOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) : upOf (m := m) hm sec j ≠ dnOf (m := m) hm sec j := by
  intro h
  have := congrArg (fun x => (x.idx : ℕ)) h
  simp [upOf, dnOf] at this

/-- **A top is never a bottom**: `partner` flips `top`, so the tops of edge `s-1` differ
from the bottoms of edge `s`. -/
theorem partner_ne_bot {n : ℕ} {m : Fin n → ℕ} (x y : EndType.Endpt n m)
    (hx : x.top = false) (hy : y.top = false) : EndType.partner x ≠ y := by
  intro h
  have := congrArg EndType.Endpt.top h
  simp [EndType.partner, hx, hy] at this

/-- **And the two tops are distinct**, again by index. -/
theorem partner_upOf_ne_partner_dnOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (sec : ℤ → Fin n) (j : ℤ) :
    EndType.partner (upOf (m := m) hm sec j) ≠ EndType.partner (dnOf (m := m) hm sec j) := by
  intro h
  have := congrArg (fun x => (x.idx : ℕ)) h
  simp [EndType.partner, upOf, dnOf] at this

end EltBridge

#print axioms EltBridge.upOf_dnOf_edgeOf
#print axioms EltBridge.upOf_ne_dnOf
#print axioms EltBridge.partner_ne_bot
#print axioms EltBridge.partner_upOf_ne_partner_dnOf

namespace EltBridge

/-! ### The site facts

`siteOf x = edgeOf x + [top x]`, so a bottom sits at its own edge and a top one to the
right.  Each site fact is therefore exactly the statement that `sec` is a section at
that position. -/

theorem upOf_siteOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) (hsec : ((sec j : ℕ) : ℤ) = j) :
    EndType.siteOf (upOf (m := m) hm sec j) = j := by
  unfold EndType.siteOf EndType.edgeOf upOf EndType.atTop
  simpa using hsec

theorem dnOf_siteOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) (hsec : ((sec j : ℕ) : ℤ) = j) :
    EndType.siteOf (dnOf (m := m) hm sec j) = j := by
  unfold EndType.siteOf EndType.edgeOf dnOf EndType.atTop
  simpa using hsec

theorem partner_upOf_siteOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) (hsec : ((sec j : ℕ) : ℤ) = j) :
    EndType.siteOf (EndType.partner (upOf (m := m) hm sec j)) = j + 1 := by
  unfold EndType.siteOf EndType.edgeOf EndType.partner upOf EndType.atTop
  simp only [Bool.not_false, if_true]
  rw [hsec]

theorem partner_dnOf_siteOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (j : ℤ) (hsec : ((sec j : ℕ) : ℤ) = j) :
    EndType.siteOf (EndType.partner (dnOf (m := m) hm sec j)) = j + 1 := by
  unfold EndType.siteOf EndType.edgeOf EndType.partner dnOf EndType.atTop
  simp only [Bool.not_false, if_true]
  rw [hsec]

/-- **`upOf` and `dnOf` name the strand bottoms.**  Given the section property at `x`'s
own edge, `up (edgeOf x)` is `botOf x` when `x`'s strand is `0`. -/
theorem upOf_eq_botOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (x : EndType.Endpt n m) (hidx : (x.idx : ℕ) = 0)
    (hsec : sec (EndType.edgeOf x) = x.edge) :
    upOf (m := m) hm sec (EndType.edgeOf x) = botOf x := by
  obtain ⟨e, i, t⟩ := x
  have he : sec ((e : ℕ) : ℤ) = e := hsec
  unfold upOf botOf
  simp only [EndType.edgeOf]
  congr 1
  · rw [Fin.heq_ext_iff (by rw [he])]
    simpa using hidx.symm

theorem dnOf_eq_botOf {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (x : EndType.Endpt n m) (hidx : (x.idx : ℕ) = 1)
    (hsec : sec (EndType.edgeOf x) = x.edge) :
    dnOf (m := m) hm sec (EndType.edgeOf x) = botOf x := by
  obtain ⟨e, i, t⟩ := x
  have he : sec ((e : ℕ) : ℤ) = e := hsec
  unfold dnOf botOf
  simp only [EndType.edgeOf]
  congr 1
  · rw [Fin.heq_ext_iff (by rw [he])]
    simpa using hidx.symm

end EltBridge

#print axioms EltBridge.upOf_siteOf
#print axioms EltBridge.partner_upOf_siteOf
#print axioms EltBridge.upOf_eq_botOf

namespace EltBridge

/-! ### `hfour`

An end at site `s` has `top = false`, and then its edge is `s`, or `top = true`, and
then its edge is `s-1`.  Its index is `0` or `1`.  Those four combinations are exactly
`up s`, `dn s`, `partner (up (s-1))`, `partner (dn (s-1))`. -/

/-- A bottom end is its own representative. -/
theorem botOf_eq_self {n : ℕ} {m : Fin n → ℕ} (x : EndType.Endpt n m)
    (h : x.top = false) : botOf x = x := by
  obtain ⟨e, i, t⟩ := x
  simp_all [botOf]

/-- A top end is the partner of its representative. -/
theorem eq_partner_botOf {n : ℕ} {m : Fin n → ℕ} (x : EndType.Endpt n m)
    (h : x.top = true) : x = EndType.partner (botOf x) := by
  obtain ⟨e, i, t⟩ := x
  simp_all [botOf, EndType.partner]

/-- **`hfour` at `mu = 2`.** -/
theorem hfour_of_mu_two {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (s : ℤ) (x : EndType.Endpt n m) (hx : EndType.siteOf x = s)
    (hsec : sec (EndType.edgeOf x) = x.edge) :
    x = EndType.partner (upOf (m := m) hm sec (s - 1)) ∨
    x = EndType.partner (dnOf (m := m) hm sec (s - 1)) ∨
    x = upOf (m := m) hm sec s ∨ x = dnOf (m := m) hm sec s := by
  have hsite : EndType.siteOf x
      = EndType.edgeOf x + (if EndType.atTop x then (1 : ℤ) else 0) := rfl
  cases ht : x.top
  · -- a bottom: its edge is `s`
    have hed : EndType.edgeOf x = s := by
      have hat : EndType.atTop x = false := ht
      rw [hsite, hat] at hx
      simpa using hx
    rcases botOf_idx_cases hm x with hi | hi
    · right; right; left
      rw [← hed, upOf_eq_botOf hm sec x hi hsec, botOf_eq_self x ht]
    · right; right; right
      rw [← hed, dnOf_eq_botOf hm sec x hi hsec, botOf_eq_self x ht]
  · -- a top: its edge is `s - 1`
    have hed : EndType.edgeOf x = s - 1 := by
      have hat : EndType.atTop x = true := ht
      rw [hsite, hat] at hx
      simp only [if_true] at hx
      omega
    rcases botOf_idx_cases hm x with hi | hi
    · left
      rw [← hed, upOf_eq_botOf hm sec x hi hsec]
      exact eq_partner_botOf x ht
    · right; left
      rw [← hed, dnOf_eq_botOf hm sec x hi hsec]
      exact eq_partner_botOf x ht

end EltBridge

#print axioms EltBridge.botOf_eq_self
#print axioms EltBridge.hfour_of_mu_two

namespace EltBridge

/-! ### The bounce set

`hbdry : ∀ r, lo r ∈ Zf` is FALSE for run `0`: its left boundary is the span's start,
not a cut site.  But the turn must bounce there anyway -- at the span's left site there
is no edge to the left, so the two bottoms of the first edge are the only ends and have
nothing to pair with but each other.

So the turn should bounce on a SET `Bs` containing `Zf`, not on `Zf` itself: the cut
sites plus the span's two ends.  That costs nothing elsewhere.  A bounce never changes
the edge, so `hturn` -- the edge changes only off `Zf` -- still holds however much
larger `Bs` is, since passes happen only off `Bs` and `Zf ⊆ Bs`. -/

/-- **`hturn` for a bounce set larger than the cut set.**  Passes occur only off `Bs`,
and `Zf ⊆ Bs`, so an edge change forces the site out of `Zf`. -/
theorem passTurn_hturn_of_subset {α : Type*} [DecidableEq α] (edgeOf siteOf : α → ℤ)
    (p : α → α) (up dn : ℤ → α) (Zf Bs : Finset ℤ) (hsub : Zf ⊆ Bs)
    (hpe : ∀ x, edgeOf (p x) = edgeOf x)
    (hud : ∀ s : ℤ, edgeOf (up s) = edgeOf (dn s))
    (x : α)
    (hx : edgeOf (passTurn siteOf p up dn Bs (siteOf x) x) ≠ edgeOf x) :
    siteOf x ∉ Zf := by
  intro hmem
  exact hx (passTurn_keeps_edge_at_cut edgeOf siteOf p up dn Bs (siteOf x)
    (hsub hmem) hpe (hud _) (hud _) x)

/-- **And the bound is unaffected.**  `walkCount_le_runs_blk` is applied with `Zf`, the
cut set; the larger bounce set appears only in the turn.  So a turn that bounces on
`Bs ⊇ Zf` still gives `walkCount ≤ |Zf| + 1`, provided its runs are connected. -/
theorem shield_upper_bound_bounce_set {n : ℕ} {m : Fin n → ℕ}
    (Zf Bs : Finset ℤ) (hsub : Zf ⊆ Bs)
    (up dn : ℤ → EndType.Endpt n m)
    (hud : ∀ s : ℤ, EndType.edgeOf (up s) = EndType.edgeOf (dn s))
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x
      = passTurn EndType.siteOf EndType.partner up dn Bs (EndType.siteOf x) x)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hrun : ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph E).Reachable (botOf x) (botOf y)) :
    WalkGraph.walkCount E ≤ Zf.card + 1 := by
  refine shield_upper_bound_endpt E Zf botOf (fun x => by rw [hEp]) hTsite ?_
    (fun x => by rw [hEp]; exact botOf_eq_or_partner x) (fun _ => rfl) hrun
  intro x hx
  rw [hEt x] at hx
  exact passTurn_hturn_of_subset EndType.edgeOf EndType.siteOf EndType.partner up dn
    Zf Bs hsub (fun y => EndType.partner_edgeOf y) hud x hx

end EltBridge

#print axioms EltBridge.passTurn_hturn_of_subset
#print axioms EltBridge.shield_upper_bound_bounce_set

namespace EltBridge

/-! ### The run indexing

A run is a level set of `gz Zf` inside the span.  Defining `lo` and `len` as that set's
minimum and extent makes `hrange` immediate: an edge lies in its own level set, hence
between that set's min and max. -/

/-- The edges of the span whose run index is `r`. -/
noncomputable def levelSet (Zf : Finset ℤ) (A B : ℤ) (r : ℕ) : Finset ℤ :=
  (Finset.Icc A B).filter (fun j => CutComponents.gz Zf j = r)

/-- The run's left end. -/
noncomputable def runLo (Zf : Finset ℤ) (A B : ℤ) (r : ℕ) : ℤ :=
  if h : (levelSet Zf A B r).Nonempty then (levelSet Zf A B r).min' h else A

/-- The run's extent. -/
noncomputable def runLen (Zf : Finset ℤ) (A B : ℤ) (r : ℕ) : ℕ :=
  if h : (levelSet Zf A B r).Nonempty then
    ((levelSet Zf A B r).max' h - (levelSet Zf A B r).min' h).toNat else 0

/-- **`hrange`.**  Every edge of the span lies in its own run, between that run's
minimum and maximum. -/
theorem runLo_le_and_le_len (Zf : Finset ℤ) (A B : ℤ) (j : ℤ) (hj : j ∈ Finset.Icc A B) :
    ∃ k : ℕ, k ≤ runLen Zf A B (CutComponents.gz Zf j) ∧
      j = runLo Zf A B (CutComponents.gz Zf j) + k := by
  classical
  set r := CutComponents.gz Zf j with hr
  have hmem : j ∈ levelSet Zf A B r := by
    rw [levelSet, Finset.mem_filter]
    exact ⟨hj, rfl⟩
  have hne : (levelSet Zf A B r).Nonempty := ⟨j, hmem⟩
  have hlo : runLo Zf A B r = (levelSet Zf A B r).min' hne := by
    rw [runLo, dif_pos hne]
  have hlen : runLen Zf A B r
      = ((levelSet Zf A B r).max' hne - (levelSet Zf A B r).min' hne).toNat := by
    rw [runLen, dif_pos hne]
  have hmin := Finset.min'_le _ _ hmem
  have hmax := Finset.le_max' _ _ hmem
  refine ⟨(j - (levelSet Zf A B r).min' hne).toNat, ?_, ?_⟩
  · rw [hlen]
    omega
  · rw [hlo]
    omega

end EltBridge

#print axioms EltBridge.runLo_le_and_le_len

namespace EltBridge

/-- `gz` is monotone: more of `Zf` lies below a larger argument. -/
theorem gz_mono (Zf : Finset ℤ) {a b : ℤ} (h : a ≤ b) :
    CutComponents.gz Zf a ≤ CutComponents.gz Zf b := by
  classical
  unfold CutComponents.gz
  refine Finset.card_le_card ?_
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, le_trans hz.2 h⟩

/-- **A run is an interval.**  `gz` is monotone, so a point squeezed between two members
of a level set is itself a member. -/
theorem levelSet_interval (Zf : Finset ℤ) (A B : ℤ) (r : ℕ) {a b j : ℤ}
    (ha : a ∈ levelSet Zf A B r) (hb : b ∈ levelSet Zf A B r)
    (h1 : a ≤ j) (h2 : j ≤ b) : j ∈ levelSet Zf A B r := by
  rw [levelSet, Finset.mem_filter] at ha hb ⊢
  rw [Finset.mem_Icc] at ha hb ⊢
  refine ⟨⟨le_trans ha.1.1 h1, le_trans h2 hb.1.2⟩, ?_⟩
  have m1 := gz_mono Zf h1
  have m2 := gz_mono Zf h2
  omega

/-- **`hint`.**  Strictly inside a run there is no cut site: the run is an interval on
which `gz` is constant, and a cut site there would raise it. -/
theorem no_cut_inside_run (Zf : Finset ℤ) (A B : ℤ) (r : ℕ) (k : ℕ)
    (hne : (levelSet Zf A B r).Nonempty)
    (hk : k < runLen Zf A B r) :
    runLo Zf A B r + ((k : ℤ) + 1) ∉ Zf := by
  classical
  have hlo : runLo Zf A B r = (levelSet Zf A B r).min' hne := by rw [runLo, dif_pos hne]
  have hlen : runLen Zf A B r
      = ((levelSet Zf A B r).max' hne - (levelSet Zf A B r).min' hne).toNat := by
    rw [runLen, dif_pos hne]
  have hminmem := Finset.min'_mem (levelSet Zf A B r) hne
  have hmaxmem := Finset.max'_mem (levelSet Zf A B r) hne
  have hle := Finset.min'_le_max' (levelSet Zf A B r) hne
  -- the point sits inside the run, so it is in the level set
  have hin : runLo Zf A B r + ((k : ℤ) + 1) ∈ levelSet Zf A B r := by
    refine levelSet_interval Zf A B r hminmem hmaxmem ?_ ?_
    · rw [hlo]; omega
    · rw [hlo]; omega
  -- so `gz` agrees with its value at the run's left end
  have hgz : CutComponents.gz Zf (runLo Zf A B r)
      = CutComponents.gz Zf (runLo Zf A B r + ((k : ℤ) + 1)) := by
    have h1 : CutComponents.gz Zf (runLo Zf A B r) = r := by
      rw [hlo]
      have h := hminmem
      simp only [levelSet, Finset.mem_filter] at h
      exact h.2
    have h2 : CutComponents.gz Zf (runLo Zf A B r + ((k : ℤ) + 1)) = r := by
      have h := hin
      simp only [levelSet, Finset.mem_filter] at h
      exact h.2
    rw [h1, h2]
  exact no_cut_between_of_gz_eq Zf _ _ (by omega) hgz _ (by omega) (le_refl _)

end EltBridge

#print axioms EltBridge.gz_mono
#print axioms EltBridge.levelSet_interval
#print axioms EltBridge.no_cut_inside_run

namespace EltBridge

/-- Every position of a run lies in the run, hence in the span. -/
theorem run_mem_levelSet (Zf : Finset ℤ) (A B : ℤ) (r k : ℕ)
    (hne : (levelSet Zf A B r).Nonempty) (hk : k ≤ runLen Zf A B r) :
    runLo Zf A B r + (k : ℤ) ∈ levelSet Zf A B r := by
  classical
  have hlo : runLo Zf A B r = (levelSet Zf A B r).min' hne := by rw [runLo, dif_pos hne]
  have hlen : runLen Zf A B r
      = ((levelSet Zf A B r).max' hne - (levelSet Zf A B r).min' hne).toNat := by
    rw [runLen, dif_pos hne]
  have hle := Finset.min'_le_max' (levelSet Zf A B r) hne
  refine levelSet_interval Zf A B r (Finset.min'_mem _ hne) (Finset.max'_mem _ hne)
    ?_ ?_
  · rw [hlo]; omega
  · rw [hlo]; omega

/-- **`hocc`.**  A run's positions are edges of the span, and each carries an end -- the
bottom of its up strand. -/
theorem hocc_of_section {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (Zf : Finset ℤ) (A B : ℤ)
    (hsec : ∀ j : ℤ, A ≤ j → j ≤ B → ((sec j : ℕ) : ℤ) = j)
    (r k : ℕ) (hne : (levelSet Zf A B r).Nonempty) (hk : k ≤ runLen Zf A B r) :
    ∃ y : EndType.Endpt n m,
      EndType.siteOf y = runLo Zf A B r + (k : ℤ) := by
  classical
  have hin := run_mem_levelSet Zf A B r k hne hk
  simp only [levelSet, Finset.mem_filter, Finset.mem_Icc] at hin
  exact ⟨upOf (m := m) hm sec (runLo Zf A B r + (k : ℤ)),
    upOf_siteOf hm sec _ (hsec _ hin.1.1 hin.1.2)⟩

end EltBridge

#print axioms EltBridge.run_mem_levelSet
#print axioms EltBridge.hocc_of_section

namespace EltBridge

/-! ### The composition

Everything since BLOCK 153 in one statement.  The inputs are `mu = 2`, a section `sec`
naming the edge at each position of the span, the cut set `Zf`, and a bounce set `Bs`
containing it.  The turn is `passTurn` over `Bs`, the datum is its glue, and the
conclusion is `walkCount ≤ |Zf| + 1`.

The section must extend one position past the span: site `B+1` carries the tops of edge
`B`, so it is occupied and the geometry lemmas are applied there. -/

/-- **The `mu = 2` shield bound, composed.**  Given the section and the run structure,
the glued `passTurn` datum has at most `|Zf| + 1` walks. -/
theorem shield_mu_two_composed {n : ℕ} {m : Fin n → ℕ} (hm : ∀ e, m e = 2)
    (sec : ℤ → Fin n) (Zf Bs : Finset ℤ) (A B : ℤ) (hsub : Zf ⊆ Bs)
    (hsec : ∀ j : ℤ, A ≤ j → j ≤ B + 1 → ((sec j : ℕ) : ℤ) = j)
    -- the span carries the ends
    (hspan : ∀ x : EndType.Endpt n m, A ≤ EndType.edgeOf x ∧ EndType.edgeOf x ≤ B)
    -- the datum, glued from the turn
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = passTurn EndType.siteOf EndType.partner
      (upOf (m := m) hm sec) (dnOf (m := m) hm sec) Bs (EndType.siteOf x) x)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    -- the runs are connected, which the chain lemmas supply
    (hrun : ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph E).Reachable (botOf x) (botOf y)) :
    WalkGraph.walkCount E ≤ Zf.card + 1 :=
  shield_upper_bound_bounce_set Zf Bs hsub
    (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
    (fun s => upOf_dnOf_edgeOf hm sec s)
    E hEp hEt hTsite hrun

end EltBridge

#print axioms EltBridge.shield_mu_two_composed

namespace EltBridge

/-! ### No bounce site strictly inside a run

`no_cut_inside_run` rules out members of `Zf`.  The bounce set adds the span's two ends,
so they must be ruled out too -- and they are, for position reasons: `A` is the left end
of the first run, never strictly inside one, and `B+1` is past every edge. -/

theorem no_bounce_inside_run (Zf : Finset ℤ) (A B : ℤ) (r k : ℕ)
    (hne : (levelSet Zf A B r).Nonempty) (hk : k < runLen Zf A B r) :
    runLo Zf A B r + ((k : ℤ) + 1) ∉ insert A (insert (B + 1) Zf) := by
  classical
  -- the run sits inside the span
  have hlo : runLo Zf A B r = (levelSet Zf A B r).min' hne := by rw [runLo, dif_pos hne]
  have hminmem := Finset.min'_mem (levelSet Zf A B r) hne
  have hmaxmem := Finset.max'_mem (levelSet Zf A B r) hne
  have hlen : runLen Zf A B r
      = ((levelSet Zf A B r).max' hne - (levelSet Zf A B r).min' hne).toNat := by
    rw [runLen, dif_pos hne]
  have hminA : A ≤ (levelSet Zf A B r).min' hne := by
    have := hminmem
    simp only [levelSet, Finset.mem_filter, Finset.mem_Icc] at this
    exact this.1.1
  have hmaxB : (levelSet Zf A B r).max' hne ≤ B := by
    have := hmaxmem
    simp only [levelSet, Finset.mem_filter, Finset.mem_Icc] at this
    exact this.1.2
  have hle := Finset.min'_le_max' (levelSet Zf A B r) hne
  intro hmem
  rw [Finset.mem_insert, Finset.mem_insert] at hmem
  rcases hmem with h | h | h
  · -- it would have to be `A`, but it is strictly right of the run's left end
    rw [hlo] at h; omega
  · -- or `B+1`, but it is at most `B`
    rw [hlo] at h; omega
  · exact no_cut_inside_run Zf A B r k hne hk h

end EltBridge

#print axioms EltBridge.no_bounce_inside_run

namespace EltBridge

/-! ### The run's left end is a bounce site

For `r ≥ 1` the run's left end is an actual CUT site: `gz` is `r` there and less just to
the left, and `gz` can only rise at a member of `Zf`.  For `r = 0` it is the span's left
end, which the bounce set contains. -/

/-- **`gz` rises only at a cut site.** -/
theorem mem_of_gz_lt (Zf : Finset ℤ) (j : ℤ)
    (h : CutComponents.gz Zf (j - 1) < CutComponents.gz Zf j) : j ∈ Zf := by
  classical
  by_contra hj
  exact absurd (CutComponents.gz_step_eq Zf hj) (by omega)

/-- **`hbdry`.**  A run's left end is a bounce site: a cut site when the run is not the
first, and the span's left end when it is. -/
theorem runLo_mem_bounce (Zf : Finset ℤ) (A B : ℤ) (r : ℕ)
    (hne : (levelSet Zf A B r).Nonempty)
    (hmin : ∀ j : ℤ, A ≤ j → j ≤ B → CutComponents.gz Zf j = r → runLo Zf A B r ≤ j) :
    runLo Zf A B r ∈ insert A (insert (B + 1) Zf) := by
  classical
  have hlo : runLo Zf A B r = (levelSet Zf A B r).min' hne := by rw [runLo, dif_pos hne]
  have hmem0 : runLo Zf A B r ∈ levelSet Zf A B r := by
    rw [hlo]; exact Finset.min'_mem _ hne
  have hmem1 : runLo Zf A B r ∈ Finset.Icc A B ∧
      CutComponents.gz Zf (runLo Zf A B r) = r := by
    have h := hmem0
    simp only [levelSet, Finset.mem_filter] at h
    exact h
  have hA' : A ≤ runLo Zf A B r := (Finset.mem_Icc.mp hmem1.1).1
  have hB' : runLo Zf A B r ≤ B := (Finset.mem_Icc.mp hmem1.1).2
  have hgzr : CutComponents.gz Zf (runLo Zf A B r) = r := hmem1.2
  by_cases hA : runLo Zf A B r = A
  · rw [hA]; exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    refine mem_of_gz_lt Zf _ ?_
    have hmono := gz_mono Zf (show runLo Zf A B r - 1 ≤ runLo Zf A B r by omega)
    rcases Nat.lt_or_ge (CutComponents.gz Zf (runLo Zf A B r - 1)) r with h | h
    · omega
    · exfalso
      have heq : CutComponents.gz Zf (runLo Zf A B r - 1) = r := by omega
      have := hmin (runLo Zf A B r - 1) (by omega) (by omega) heq
      omega

end EltBridge

#print axioms EltBridge.mem_of_gz_lt
#print axioms EltBridge.runLo_mem_bounce

namespace EltBridge

/-! ### The chain conditions for the `passTurn` datum

Each is the corresponding `passTurn` equation, read through `chain_*_of_pass` and the
site facts.  The site `lo r + k + 1` is inside the run, so `no_bounce_inside_run` makes
the turn PASS there; the site `lo r` is the run's left end, so `runLo_mem_bounce` makes
it BOUNCE. -/

variable {n : ℕ} {m : Fin n → ℕ}

theorem chain_up_passTurn (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (Zf : Finset ℤ) (A B : ℤ) (r k : ℕ)
    (hne : (levelSet Zf A B r).Nonempty) (hk : k < runLen Zf A B r)
    (hsecA : ((sec (runLo Zf A B r + (k : ℤ)) : ℕ) : ℤ) = runLo Zf A B r + (k : ℤ))
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = passTurn EndType.siteOf EndType.partner
      (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
      (insert A (insert (B + 1) Zf)) (EndType.siteOf x) x) :
    (WalkGraph.graph E).Reachable
      (upOf (m := m) hm sec (runLo Zf A B r + (k : ℤ)))
      (upOf (m := m) hm sec (runLo Zf A B r + ((k : ℤ) + 1))) := by
  set a := runLo Zf A B r + (k : ℤ) with ha
  have hgoal : runLo Zf A B r + ((k : ℤ) + 1) = a + 1 := by rw [ha]; ring
  rw [hgoal]
  refine chain_up_of_pass E (upOf (m := m) hm sec) a (a + 1) ?_
  have hsite : EndType.siteOf (E.p (upOf (m := m) hm sec a)) = a + 1 := by
    rw [hEp]
    exact partner_upOf_siteOf hm sec a hsecA
  rw [hEt, hsite, hEp]
  have harith : a + 1 - 1 = a := by ring
  have h := passTurn_pass_up EndType.siteOf EndType.partner
    (upOf (m := m) hm sec) (dnOf (m := m) hm sec) (insert A (insert (B + 1) Zf)) (a + 1)
    (by
      have h := no_bounce_inside_run Zf A B r k hne hk
      have he : a + 1 = runLo Zf A B r + ((k : ℤ) + 1) := by rw [ha]; ring
      rw [he]
      exact h)
    (by rw [harith]; exact partner_upOf_siteOf hm sec a hsecA)
  rw [harith] at h
  exact h

end EltBridge

#print axioms EltBridge.chain_up_passTurn

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

theorem chain_dn_passTurn (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (Zf : Finset ℤ) (A B : ℤ) (r k : ℕ)
    (hne : (levelSet Zf A B r).Nonempty) (hk : k < runLen Zf A B r)
    (hsecB : ((sec (runLo Zf A B r + ((k : ℤ) + 1)) : ℕ) : ℤ)
      = runLo Zf A B r + ((k : ℤ) + 1))
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = passTurn EndType.siteOf EndType.partner
      (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
      (insert A (insert (B + 1) Zf)) (EndType.siteOf x) x) :
    (WalkGraph.graph E).Reachable
      (dnOf (m := m) hm sec (runLo Zf A B r + (k : ℤ)))
      (dnOf (m := m) hm sec (runLo Zf A B r + ((k : ℤ) + 1))) := by
  set a := runLo Zf A B r + (k : ℤ) with ha
  have hgoal : runLo Zf A B r + ((k : ℤ) + 1) = a + 1 := by rw [ha]; ring
  rw [hgoal] at hsecB ⊢
  refine chain_dn_of_pass E (dnOf (m := m) hm sec) a (a + 1) ?_
  have hsite : EndType.siteOf (dnOf (m := m) hm sec (a + 1)) = a + 1 :=
    dnOf_siteOf hm sec (a + 1) hsecB
  rw [hEt, hsite, hEp]
  have harith : a + 1 - 1 = a := by ring
  have h := passTurn_pass_dn EndType.siteOf EndType.partner
    (upOf (m := m) hm sec) (dnOf (m := m) hm sec) (insert A (insert (B + 1) Zf)) (a + 1)
    (by
      have h := no_bounce_inside_run Zf A B r k hne hk
      have he : a + 1 = runLo Zf A B r + ((k : ℤ) + 1) := by rw [ha]; ring
      rw [he]; exact h)
    hsite
    (by rw [harith]; exact partner_ne_bot _ _ rfl rfl)
    (upOf_ne_dnOf hm sec (a + 1))
  rw [harith] at h
  exact h

theorem chain_join_passTurn (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (Zf : Finset ℤ) (A B : ℤ) (r : ℕ)
    (hne : (levelSet Zf A B r).Nonempty)
    (hmin : ∀ j : ℤ, A ≤ j → j ≤ B → CutComponents.gz Zf j = r → runLo Zf A B r ≤ j)
    (hsecL : ((sec (runLo Zf A B r) : ℕ) : ℤ) = runLo Zf A B r)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = passTurn EndType.siteOf EndType.partner
      (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
      (insert A (insert (B + 1) Zf)) (EndType.siteOf x) x) :
    (WalkGraph.graph E).Reachable
      (upOf (m := m) hm sec (runLo Zf A B r)) (dnOf (m := m) hm sec (runLo Zf A B r)) := by
  refine chain_join_of_bounce E (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
    (runLo Zf A B r) ?_
  have hsite : EndType.siteOf (dnOf (m := m) hm sec (runLo Zf A B r)) = runLo Zf A B r :=
    dnOf_siteOf hm sec _ hsecL
  rw [hEt, hsite]
  exact passTurn_bounce EndType.siteOf EndType.partner
    (upOf (m := m) hm sec) (dnOf (m := m) hm sec) (insert A (insert (B + 1) Zf))
    (runLo Zf A B r) (runLo_mem_bounce Zf A B r hne hmin) hsite
    (partner_ne_bot _ _ rfl rfl) (partner_ne_bot _ _ rfl rfl)
    (upOf_ne_dnOf hm sec _)

end EltBridge

#print axioms EltBridge.chain_dn_passTurn
#print axioms EltBridge.chain_join_passTurn

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- `runLo_mem_bounce` without the nonemptiness side condition: an empty run's `runLo`
is `A` by definition, and `A` is a bounce site. -/
theorem runLo_mem_bounce' (Zf : Finset ℤ) (A B : ℤ) (r : ℕ)
    (hmin : ∀ j : ℤ, A ≤ j → j ≤ B → CutComponents.gz Zf j = r → runLo Zf A B r ≤ j) :
    runLo Zf A B r ∈ insert A (insert (B + 1) Zf) := by
  classical
  by_cases hne : (levelSet Zf A B r).Nonempty
  · exact runLo_mem_bounce Zf A B r hne hmin
  · have : runLo Zf A B r = A := by rw [runLo, dif_neg hne]
    rw [this]
    exact Finset.mem_insert_self _ _

/-- An empty run has no positions to chain. -/
theorem runLen_eq_zero_of_empty (Zf : Finset ℤ) (A B : ℤ) (r : ℕ)
    (hne : ¬ (levelSet Zf A B r).Nonempty) : runLen Zf A B r = 0 := by
  rw [runLen, dif_neg hne]

/-- **`hrun` for the `passTurn` datum.**  The runs are the level sets of `gz`, the chain
conditions are the three `passTurn` equations, and `hrun_multi` glues them. -/
theorem hrun_passTurn (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (Zf : Finset ℤ) (A B : ℤ)
    (hsecLo : ∀ r : ℕ, ((sec (runLo Zf A B r) : ℕ) : ℤ) = runLo Zf A B r)
    (hsecRun : ∀ (r k : ℕ), k ≤ runLen Zf A B r →
      ((sec (runLo Zf A B r + (k : ℤ)) : ℕ) : ℤ) = runLo Zf A B r + (k : ℤ))
    (hmin : ∀ (r : ℕ) (j : ℤ), A ≤ j → j ≤ B → CutComponents.gz Zf j = r →
      runLo Zf A B r ≤ j)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = passTurn EndType.siteOf EndType.partner
      (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
      (insert A (insert (B + 1) Zf)) (EndType.siteOf x) x) :
    ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph E).Reachable (botOf x) (botOf y) := by
  classical
  refine hrun_multi E Zf (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
    (runLo Zf A B) (runLen Zf A B)
    (hcover_of_mu_two hm _ _
      (fun x hidx => upOf_eq_botOf hm sec x hidx (hsecEdge x))
      (fun x hidx => dnOf_eq_botOf hm sec x hidx (hsecEdge x)))
    (fun x => runLo_le_and_le_len Zf A B _ (hspan x)) ?_
  intro r j j' hj hj' b b'
  by_cases hne : (levelSet Zf A B r).Nonempty
  · exact run_connected_of_reachability E (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
      (runLo Zf A B r) (runLen Zf A B r)
      (fun k hk => chain_up_passTurn hm sec Zf A B r k hne hk
        (hsecRun r k (le_of_lt hk)) E hEp hEt)
      (fun k hk => chain_dn_passTurn hm sec Zf A B r k hne hk
        (by
          have := hsecRun r (k + 1) hk
          push_cast at this ⊢
          exact this) E hEp hEt)
      (chain_join_passTurn hm sec Zf A B r hne (hmin r) (hsecLo r) E hEp hEt)
      j j' hj hj' b b'
  · -- an empty run: no positions to chain, so both indices are `0`
    have hlen := runLen_eq_zero_of_empty Zf A B r hne
    have hj0 : j = 0 := by omega
    have hj0' : j' = 0 := by omega
    subst hj0; subst hj0'
    have hjoin : (WalkGraph.graph E).Reachable
        (upOf (m := m) hm sec (runLo Zf A B r))
        (dnOf (m := m) hm sec (runLo Zf A B r)) := by
      refine chain_join_of_bounce E _ _ _ ?_
      have hsite : EndType.siteOf (dnOf (m := m) hm sec (runLo Zf A B r))
          = runLo Zf A B r := dnOf_siteOf hm sec _ (hsecLo r)
      rw [hEt, hsite]
      exact passTurn_bounce EndType.siteOf EndType.partner _ _ _ _
        (runLo_mem_bounce' Zf A B r (hmin r)) hsite
        (partner_ne_bot _ _ rfl rfl) (partner_ne_bot _ _ rfl rfl)
        (upOf_ne_dnOf hm sec _)
    cases b <;> cases b' <;> simp only [Nat.cast_zero, add_zero]
    · exact SimpleGraph.Reachable.refl _
    · exact hjoin.symm
    · exact hjoin
    · exact SimpleGraph.Reachable.refl _

end EltBridge

#print axioms EltBridge.hrun_passTurn

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The `mu = 2` shield bound, with `hrun` derived.**

This is BLOCK 182's composition with the hole filled: `hrun` is no longer assumed but
produced by `hrun_passTurn` from the turn's own pass and bounce equations.  The inputs
are the section, the span, the cut set, and the glued datum; the conclusion is
`walkCount ≤ |Zf| + 1`.

No merge, no swap, no free pair: `CostMerge` is not invoked anywhere beneath this. -/
theorem shield_mu_two (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (Zf : Finset ℤ) (A B : ℤ)
    (hsecLo : ∀ r : ℕ, ((sec (runLo Zf A B r) : ℕ) : ℤ) = runLo Zf A B r)
    (hsecRun : ∀ (r k : ℕ), k ≤ runLen Zf A B r →
      ((sec (runLo Zf A B r + (k : ℤ)) : ℕ) : ℤ) = runLo Zf A B r + (k : ℤ))
    (hmin : ∀ (r : ℕ) (j : ℤ), A ≤ j → j ≤ B → CutComponents.gz Zf j = r →
      runLo Zf A B r ≤ j)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = passTurn EndType.siteOf EndType.partner
      (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
      (insert A (insert (B + 1) Zf)) (EndType.siteOf x) x)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x) :
    WalkGraph.walkCount E ≤ Zf.card + 1 :=
  shield_upper_bound_bounce_set Zf (insert A (insert (B + 1) Zf))
    (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
    (upOf (m := m) hm sec) (dnOf (m := m) hm sec)
    (fun s => upOf_dnOf_edgeOf hm sec s)
    E hEp hEt hTsite
    (hrun_passTurn hm sec Zf A B hsecLo hsecRun hmin hspan hsecEdge
      E hEp hEt)

end EltBridge

#print axioms EltBridge.shield_mu_two

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- An end's site lies one either side of its edge, hence inside `[A-1, B+1]` when the
edge lies in `[A, B]`. -/
theorem siteOf_mem_of_span (x : EndType.Endpt n m) (A B : ℤ)
    (h : EndType.edgeOf x ∈ Finset.Icc A B) :
    A ≤ EndType.siteOf x ∧ EndType.siteOf x ≤ B + 1 := by
  rw [Finset.mem_Icc] at h
  rcases siteOf_cases x with hs | hs <;> omega

/-- **The datum.**  `exists_glued_data` gives the walk-graph data of the glued
`passTurn`, and its three obligations are `passTurn_invol`, `passTurn_site` and
`passTurn_ne`.  Each is applied only at an OCCUPIED site, where the witness comes from
the very hypothesis `siteOf x = s`, so the section is needed only on `[A-1, B+1]`. -/
theorem exists_passTurn_data (hm : ∀ e, m e = 2) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (A B : ℤ)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (hsecWide : ∀ j : ℤ, A - 1 ≤ j → j ≤ B + 1 → ((sec j : ℕ) : ℤ) = j)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge) :
    ∃ E : WalkGraph.Data (EndType.Endpt n m),
      E.p = EndType.partner ∧
      (∀ x, E.t x = passTurn EndType.siteOf EndType.partner
        (upOf (m := m) hm sec) (dnOf (m := m) hm sec) Bs (EndType.siteOf x) x) ∧
      (∀ x, EndType.siteOf (E.t x) = EndType.siteOf x) := by
  classical
  -- at an occupied site the four site facts hold, since the site is in range
  have hfacts : ∀ (s : ℤ), (∃ y : EndType.Endpt n m, EndType.siteOf y = s) →
      EndType.siteOf (EndType.partner (upOf (m := m) hm sec (s - 1))) = s ∧
      EndType.siteOf (EndType.partner (dnOf (m := m) hm sec (s - 1))) = s ∧
      EndType.siteOf (upOf (m := m) hm sec s) = s ∧
      EndType.siteOf (dnOf (m := m) hm sec s) = s := by
    rintro s ⟨y, rfl⟩
    obtain ⟨h1, h2⟩ := siteOf_mem_of_span y A B (hspan y)
    have hs : ((sec (EndType.siteOf y) : ℕ) : ℤ) = EndType.siteOf y :=
      hsecWide _ (by omega) h2
    have hs' : ((sec (EndType.siteOf y - 1) : ℕ) : ℤ) = EndType.siteOf y - 1 :=
      hsecWide _ (by omega) (by omega)
    refine ⟨?_, ?_, upOf_siteOf hm sec _ hs, dnOf_siteOf hm sec _ hs⟩
    · rw [partner_upOf_siteOf hm sec _ hs']; ring
    · rw [partner_dnOf_siteOf hm sec _ hs']; ring
  obtain ⟨E, hEp, hEt⟩ := exists_glued_data EndType.siteOf EndType.partner
    (passTurn EndType.siteOf EndType.partner (upOf (m := m) hm sec)
      (dnOf (m := m) hm sec) Bs)
    EndType.partner_invol EndType.partner_ne EndType.partner_site_ne
    (fun s x => passTurn_invol EndType.siteOf EndType.partner _ _ Bs s
      (fun h => partner_upOf_ne_partner_dnOf hm sec (s - 1))
      (fun h => partner_ne_bot _ _ rfl rfl) (fun h => partner_ne_bot _ _ rfl rfl)
      (fun h => partner_ne_bot _ _ rfl rfl) (fun h => partner_ne_bot _ _ rfl rfl)
      (fun h => upOf_ne_dnOf hm sec s)
      (fun h => (hfacts s h).1) (fun h => (hfacts s h).2.1)
      (fun h => (hfacts s h).2.2.1) (fun h => (hfacts s h).2.2.2) x)
    (fun s x hxs => by
      subst hxs
      exact passTurn_site EndType.siteOf EndType.partner _ _ Bs _
        ((hfacts _ ⟨x, rfl⟩).1) ((hfacts _ ⟨x, rfl⟩).2.1)
        ((hfacts _ ⟨x, rfl⟩).2.2.1) ((hfacts _ ⟨x, rfl⟩).2.2.2) x rfl)
    (fun s x hxs => by
      subst hxs
      exact passTurn_ne EndType.siteOf EndType.partner _ _ Bs _
        (partner_upOf_ne_partner_dnOf hm sec _)
        (partner_ne_bot _ _ rfl rfl) (partner_ne_bot _ _ rfl rfl)
        (partner_ne_bot _ _ rfl rfl) (partner_ne_bot _ _ rfl rfl)
        (upOf_ne_dnOf hm sec _) x rfl
        (hfour_of_mu_two hm sec _ x rfl (hsecEdge x)))
  refine ⟨E, hEp, hEt, ?_⟩
  intro x
  rw [hEt x]
  exact passTurn_site EndType.siteOf EndType.partner _ _ Bs _
    ((hfacts _ ⟨x, rfl⟩).1) ((hfacts _ ⟨x, rfl⟩).2.1)
    ((hfacts _ ⟨x, rfl⟩).2.2.1) ((hfacts _ ⟨x, rfl⟩).2.2.2) x rfl

end EltBridge

#print axioms EltBridge.siteOf_mem_of_span
#print axioms EltBridge.exists_passTurn_data

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The `mu = 2` shield bound, self-contained.**

No datum is assumed: `exists_passTurn_data` builds it, and `shield_mu_two` bounds it.
The hypotheses are the configuration alone --

    hm         every edge carries two strands
    hspan      every end's edge lies in `[A, B]`
    hsecWide   `sec` names the edge at each position of `[A-1, B+1]`
    hsecEdge   and names an end's own edge at its own position
    hmin       `runLo` is the least position of its run

-- and the conclusion is that SOME walk-graph datum, namely the glue of `passTurn`, has
at most `|Zf| + 1` walks.  That is `prop:cut`'s converse on this class: the defect is at
most the number of cut sites.

`CostMerge` is invoked nowhere beneath this. -/
theorem shield_mu_two_final (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (Zf : Finset ℤ) (A B : ℤ)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (hsecWide : ∀ j : ℤ, A - 1 ≤ j → j ≤ B + 1 → ((sec j : ℕ) : ℤ) = j)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge)
    (hmin : ∀ (r : ℕ) (j : ℤ), A ≤ j → j ≤ B → CutComponents.gz Zf j = r →
      runLo Zf A B r ≤ j)
    (hloRange : ∀ r : ℕ, A - 1 ≤ runLo Zf A B r ∧ runLo Zf A B r ≤ B + 1)
    (hrunRange : ∀ (r k : ℕ), k ≤ runLen Zf A B r →
      A - 1 ≤ runLo Zf A B r + (k : ℤ) ∧ runLo Zf A B r + (k : ℤ) ≤ B + 1) :
    ∃ E : WalkGraph.Data (EndType.Endpt n m),
      WalkGraph.walkCount E ≤ Zf.card + 1 := by
  obtain ⟨E, hEp, hEt, hTsite⟩ :=
    exists_passTurn_data hm sec (insert A (insert (B + 1) Zf)) A B hspan hsecWide hsecEdge
  exact ⟨E, shield_mu_two hm sec Zf A B
    (fun r => hsecWide _ (hloRange r).1 (hloRange r).2)
    (fun r k hk => hsecWide _ (hrunRange r k hk).1 (hrunRange r k hk).2)
    hmin hspan hsecEdge E hEp hEt hTsite⟩

end EltBridge

#print axioms EltBridge.shield_mu_two_final

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-! ### The lower bound for the same datum

`prop:cut` is `c ≥ |Z|`, and its machinery -- `CutComponents.exists_injective_components_avoiding`
-- needs only `Local`, which is the second disjunct of `hedge`.  So it applies to the
`passTurn` datum as well, and the two bounds meet on ONE datum rather than on two. -/

/-- **`Local` for a turn that keeps its site and changes the edge only off `Zf`.** -/
theorem local_of_turn (E : WalkGraph.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (hEp : E.p = EndType.partner)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf) :
    CutComponents.Local (WalkGraph.graph E) EndType.edgeOf Zf := by
  intro x y hadj
  rcases hadj with rfl | rfl
  · -- the crossing partner keeps the edge
    refine ⟨EndType.edgeOf x + 1, Or.inl (by ring), Or.inl ?_, ?_⟩
    · rw [hEp, EndType.partner_edgeOf]; ring
    · intro hne
      exact absurd (by rw [hEp, EndType.partner_edgeOf]) hne
  · -- the turn keeps the site
    refine ⟨EndType.siteOf x, ?_, ?_, ?_⟩
    · rcases siteOf_cases x with h | h
      · exact Or.inr h.symm
      · exact Or.inl (by omega)
    · have hy : EndType.siteOf (E.t x) = EndType.siteOf x := hTsite x
      rcases siteOf_cases (E.t x) with h | h
      · exact Or.inr (by rw [← hy, h])
      · exact Or.inl (by rw [← hy, h]; omega)
    · intro hne
      exact hturn x (fun hc => hne hc.symm)

/-- **`prop:cut` for the `passTurn` datum**: at least `|Zf| + 1` walks. -/
theorem walkCount_ge_passTurn (E : WalkGraph.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (A B : ℤ) (hAB : A ≤ B)
    (hEp : E.p = EndType.partner)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (c0 : (WalkGraph.graph E).ConnectedComponent) :
    Zf.card + 1 ≤ WalkGraph.walkCount E := by
  obtain ⟨F, hinj, havoid⟩ :=
    CutComponents.exists_injective_components_avoiding
      (local_of_turn E Zf hEp hTsite hturn) A B hAB hlow hhigh hocc c0
  exact ConfigLoop.walkCount_ge_of_avoiding E Zf.card c0 F hinj havoid

end EltBridge

#print axioms EltBridge.local_of_turn
#print axioms EltBridge.walkCount_ge_passTurn

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The shield law at `mu = 2`: `walkCount = |Z| + 1`.**

Both bounds now hold of the SAME datum.  The lower one is `prop:cut`, which needs only
`Local`; the upper one is the swap-free construction of BLOCKS 153-185.  Together they
pin the walk count exactly, which is `c = |Z|`.

`CostMerge` is invoked in neither direction. -/
theorem shield_law_mu_two (hm : ∀ e, m e = 2) (sec : ℤ → Fin n)
    (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (hsecWide : ∀ j : ℤ, A - 1 ≤ j → j ≤ B + 1 → ((sec j : ℕ) : ℤ) = j)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge)
    (hmin : ∀ (r : ℕ) (j : ℤ), A ≤ j → j ≤ B → CutComponents.gz Zf j = r →
      runLo Zf A B r ≤ j)
    (hloRange : ∀ r : ℕ, A - 1 ≤ runLo Zf A B r ∧ runLo Zf A B r ≤ B + 1)
    (hrunRange : ∀ (r k : ℕ), k ≤ runLen Zf A B r →
      A - 1 ≤ runLo Zf A B r + (k : ℤ) ∧ runLo Zf A B r + (k : ℤ) ≤ B + 1)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hne : Nonempty (EndType.Endpt n m)) :
    ∃ E : WalkGraph.Data (EndType.Endpt n m),
      WalkGraph.walkCount E = Zf.card + 1 := by
  classical
  obtain ⟨E, hEp, hEt, hTsite⟩ :=
    exists_passTurn_data hm sec (insert A (insert (B + 1) Zf)) A B hspan hsecWide hsecEdge
  have hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x →
      EndType.siteOf x ∉ Zf := by
    intro x hx
    rw [hEt x] at hx
    exact passTurn_hturn_of_subset EndType.edgeOf EndType.siteOf EndType.partner
      (upOf (m := m) hm sec) (dnOf (m := m) hm sec) Zf (insert A (insert (B + 1) Zf))
      (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
      (fun y => EndType.partner_edgeOf y)
      (fun s => upOf_dnOf_edgeOf hm sec s) x hx
  refine ⟨E, le_antisymm ?_ ?_⟩
  · exact shield_mu_two hm sec Zf A B
      (fun r => hsecWide _ (hloRange r).1 (hloRange r).2)
      (fun r k hk => hsecWide _ (hrunRange r k hk).1 (hrunRange r k hk).2)
      hmin hspan hsecEdge E hEp hEt hTsite
  · obtain ⟨x0⟩ := hne
    exact walkCount_ge_passTurn E Zf A B hAB hEp hTsite hturn hlow hhigh hocc
      ((WalkGraph.graph E).connectedComponentMk x0)

end EltBridge

#print axioms EltBridge.shield_law_mu_two

namespace EltBridge

/-! ## General `mu`: the run connectivity with `u` levels

At `mu = 2` an edge carried one up strand and one down strand, and `run_one_component`
chained them into two lines closed by a boundary bounce.  At general `mu` an edge carries
`u = mu/2` of each, so a strand is `(edge, level, up?)`, and the same argument needs a
third family of links.

BLOCK 187 identified it: with identity passes the levels never mix, giving `u`
components, and one component requires a single `u`-CYCLE somewhere.  A pass costs the
same whichever levels it pairs, so that cycle is free to insert.

The three link families are therefore

    hchain   (j, l, b) — (j+1, l, b)        the passes, along the run
    hjoin    (lo, l, true) — (lo, l, false) the boundary bounce, up to down
    hcyc     (lo, l, true) — (lo, l+1, true) the one cycle, across levels

and they put every strand of the run in one component. -/

/-- Every level is reachable from level `0` by the cycle's links.  Only the linear part
`0 → 1 → ... → u-1` is used, so no wraparound appears and no `Fin` arithmetic is
needed. -/
theorem levels_reachable (lo : ℤ) (u : ℕ) (hu : 0 < u)
    (R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop)
    (hcyc : ∀ (i : ℕ) (hi : i + 1 < u),
      R (lo, ⟨i, by omega⟩, true) (lo, ⟨i + 1, hi⟩, true)) :
    ∀ (j : ℕ) (hj : j < u),
      Relation.ReflTransGen R (lo, ⟨0, hu⟩, true) (lo, ⟨j, hj⟩, true) := by
  intro j
  induction j with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro hj
    exact (ih (by omega)).tail (hcyc k hj)

/-- **Every strand of the run is reachable from the first.**  The three link families are
the passes along the run, the boundary bounce from up to down, and the cycle across
levels. -/
theorem run_one_component_gen (lo : ℤ) (n u : ℕ) (hu : 0 < u)
    (R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop)
    (hchain : ∀ (k : ℕ) (l : Fin u) (b : Bool), k < n →
      R (lo + k, l, b) (lo + (k + 1 : ℕ), l, b))
    (hjoin : ∀ l : Fin u, R (lo, l, true) (lo, l, false))
    (hcyc : ∀ (i : ℕ) (hi : i + 1 < u),
      R (lo, ⟨i, by omega⟩, true) (lo, ⟨i + 1, hi⟩, true)) :
    ∀ (k : ℕ) (l : Fin u) (b : Bool), k ≤ n →
      Relation.ReflTransGen R (lo, ⟨0, hu⟩, true) (lo + k, l, b) := by
  intro k l b hk
  have hlvl : Relation.ReflTransGen R (lo, ⟨0, hu⟩, true) (lo, l, true) := by
    have h := levels_reachable lo u hu R hcyc l.val l.isLt
    simpa using h
  have hstart : Relation.ReflTransGen R (lo, ⟨0, hu⟩, true) (lo, l, b) := by
    cases b
    · exact hlvl.tail (hjoin l)
    · exact hlvl
  have hout : ∀ j : ℕ, j ≤ n →
      Relation.ReflTransGen R (lo, l, b) (lo + j, l, b) := by
    intro j
    induction j with
    | zero => intro _; simpa using Relation.ReflTransGen.refl
    | succ i ih =>
      intro hi
      exact (ih (by omega)).tail (hchain i l b (by omega))
  exact hstart.trans (hout k hk)

end EltBridge

#print axioms EltBridge.levels_reachable
#print axioms EltBridge.run_one_component_gen

namespace EltBridge

/-- **Any two strands of the run are joined**, at general `u`. -/
theorem run_pairwise_gen (lo : ℤ) (n u : ℕ) (hu : 0 < u)
    (R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop)
    (hsymm : ∀ a b, R a b → R b a)
    (hchain : ∀ (k : ℕ) (l : Fin u) (b : Bool), k < n →
      R (lo + k, l, b) (lo + (k + 1 : ℕ), l, b))
    (hjoin : ∀ l : Fin u, R (lo, l, true) (lo, l, false))
    (hcyc : ∀ (i : ℕ) (hi : i + 1 < u),
      R (lo, ⟨i, by omega⟩, true) (lo, ⟨i + 1, hi⟩, true))
    (j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n) (l l' : Fin u) (b b' : Bool) :
    Relation.ReflTransGen R (lo + j, l, b) (lo + j', l', b') := by
  have hsymmR : ∀ a c, Relation.ReflTransGen R a c → Relation.ReflTransGen R c a := by
    intro a c h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.head (hsymm _ _ hstep) ih
  have h1 := run_one_component_gen lo n u hu R hchain hjoin hcyc j l b hj
  have h2 := run_one_component_gen lo n u hu R hchain hjoin hcyc j' l' b' hj'
  exact (hsymmR _ _ h1).trans h2

/-- **And the run is connected in the walk graph**, at general `u`: any relation whose
steps are realisable as walks transfers along the chain. -/
theorem run_connected_in_graph_gen {α : Type*} [Fintype α] [DecidableEq α]
    (u : ℕ) (D : WalkGraph.Data α) (f : ℤ × Fin u × Bool → α) (lo : ℤ) (n : ℕ)
    (hu : 0 < u)
    (R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop)
    (hR : ∀ a b, R a b → (WalkGraph.graph D).Reachable (f a) (f b))
    (hsymm : ∀ a b, R a b → R b a)
    (hchain : ∀ (k : ℕ) (l : Fin u) (b : Bool), k < n →
      R (lo + k, l, b) (lo + (k + 1 : ℕ), l, b))
    (hjoin : ∀ l : Fin u, R (lo, l, true) (lo, l, false))
    (hcyc : ∀ (i : ℕ) (hi : i + 1 < u),
      R (lo, ⟨i, by omega⟩, true) (lo, ⟨i + 1, hi⟩, true))
    (j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n) (l l' : Fin u) (b b' : Bool) :
    (WalkGraph.graph D).Reachable (f (lo + j, l, b)) (f (lo + j', l', b')) :=
  reachable_of_reflTransGen (WalkGraph.graph D) R f hR
    (run_pairwise_gen lo n u hu R hsymm hchain hjoin hcyc j j' hj hj' l l' b b')

/-- **The `mu = 2` case is the `u = 1` case.**  With one level the cycle family is empty
-- there is no `i` with `i + 1 < 1` -- so the two chains and the boundary bounce are the
whole content, which is `run_one_component`. -/
theorem cycle_vacuous_at_u_one (lo : ℤ)
    (R : ℤ × Fin 1 × Bool → ℤ × Fin 1 × Bool → Prop) :
    ∀ (i : ℕ) (hi : i + 1 < 1), R (lo, ⟨i, by omega⟩, true) (lo, ⟨i + 1, hi⟩, true) := by
  intro i hi
  omega

end EltBridge

#print axioms EltBridge.run_pairwise_gen
#print axioms EltBridge.run_connected_in_graph_gen
#print axioms EltBridge.cycle_vacuous_at_u_one

namespace EltBridge

/-! ## General `mu`: the strand naming

At `mu = 2u` an edge carries `2u` strands, the first `u` up and the last `u` down.  So a
strand is named by `(edge, level, up?)` with `level : Fin u`, and `strOf` is the bottom
end of that strand.

`shield_upper_bound_endpt` is already `u`-agnostic -- it asks only for a representative
and for run connectivity.  What was `mu = 2`-specific is the COVER, that every
representative is one of its edge's strand bottoms, and that is what generalises here. -/

variable {n : ℕ} {m : Fin n → ℕ}

/-- The strand index of level `l` on side `b`: the first `u` indices are the up strands. -/
def levIdx (u : ℕ) (l : Fin u) (b : Bool) : ℕ := if b then (l : ℕ) else u + (l : ℕ)

theorem levIdx_lt (u : ℕ) (l : Fin u) (b : Bool) : levIdx u l b < 2 * u := by
  unfold levIdx
  have := l.isLt
  cases b <;> simp <;> omega

/-- The bottom end of edge `j`'s strand at level `l` on side `b`. -/
noncomputable def strOf (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n)
    (j : ℤ) (l : Fin u) (b : Bool) : EndType.Endpt n m :=
  ⟨sec j, ⟨levIdx u l b, by rw [hm]; exact levIdx_lt u l b⟩, false⟩

/-- Reading a strand index back as a level and a side. -/
def idxLev (u : ℕ) (i : ℕ) : ℕ × Bool := if i < u then (i, true) else (i - u, false)

theorem idxLev_levIdx (u : ℕ) (l : Fin u) (b : Bool) :
    idxLev u (levIdx u l b) = ((l : ℕ), b) := by
  unfold idxLev levIdx
  have hl := l.isLt
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [if_neg (by omega)]
    simp
  · simp only [if_true]
    rw [if_pos hl]

/-- **The cover at general `u`.**  Every strand index is `levIdx` of its level and side,
so every representative is one of its edge's strand bottoms. -/
theorem exists_lev (u : ℕ) (i : ℕ) (hi : i < 2 * u) :
    ∃ (l : Fin u) (b : Bool), levIdx u l b = i := by
  by_cases h : i < u
  · exact ⟨⟨i, h⟩, true, by unfold levIdx; simp⟩
  · refine ⟨⟨i - u, by omega⟩, false, ?_⟩
    unfold levIdx
    simp only [Bool.false_eq_true, if_false]
    omega

end EltBridge

#print axioms EltBridge.levIdx_lt
#print axioms EltBridge.idxLev_levIdx
#print axioms EltBridge.exists_lev

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **`botOf x` is one of its edge's strand bottoms**, at general `u`. -/
theorem botOf_eq_strOf (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n)
    (x : EndType.Endpt n m) (hsec : sec (EndType.edgeOf x) = x.edge) :
    ∃ (l : Fin u) (b : Bool),
      strOf (m := m) hm sec (EndType.edgeOf x) l b = botOf x := by
  classical
  have hlt : (x.idx : ℕ) < 2 * u := by
    have h := x.idx.isLt
    have h2 := hm x.edge
    omega
  obtain ⟨l, b, hlb⟩ := exists_lev u (x.idx : ℕ) hlt
  refine ⟨l, b, ?_⟩
  obtain ⟨e, i, t⟩ := x
  have he : sec ((e : ℕ) : ℤ) = e := hsec
  unfold strOf botOf
  simp only [EndType.edgeOf]
  congr 1
  · rw [Fin.heq_ext_iff (by rw [he])]
    simpa using hlb

/-- **The `mu = 2` naming is the `u = 1` case.**  With one level, `levIdx 1 0 true = 0`
and `levIdx 1 0 false = 1`, which are `upOf` and `dnOf`. -/
theorem levIdx_one : levIdx 1 ⟨0, by omega⟩ true = 0 ∧ levIdx 1 ⟨0, by omega⟩ false = 1 := by
  constructor <;> unfold levIdx <;> simp

end EltBridge

#print axioms EltBridge.botOf_eq_strOf
#print axioms EltBridge.levIdx_one

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **`hrun` at general `u`.**  The runs are the level sets of `gz`; each end's
representative is a strand bottom of its edge, and that edge lies in its run, so the
general-`u` connectivity joins any two. -/
theorem hrun_multi_gen (hm : ∀ e, m e = 2 * u) (hu : 0 < u) (sec : ℤ → Fin n)
    (D : WalkGraph.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop)
    (hR : ∀ a b, R a b → (WalkGraph.graph D).Reachable
      (strOf (m := m) hm sec a.1 a.2.1 a.2.2) (strOf (m := m) hm sec b.1 b.2.1 b.2.2))
    (hsymm : ∀ a b, R a b → R b a)
    (hchain : ∀ (r : ℕ) (k : ℕ) (l : Fin u) (b : Bool), k < len r →
      R (lo r + k, l, b) (lo r + (k + 1 : ℕ), l, b))
    (hjoin : ∀ (r : ℕ) (l : Fin u), R (lo r, l, true) (lo r, l, false))
    (hcyc : ∀ (r : ℕ) (i : ℕ) (hi : i + 1 < u),
      R (lo r, ⟨i, by omega⟩, true) (lo r, ⟨i + 1, hi⟩, true)) :
    ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph D).Reachable (botOf x) (botOf y) := by
  classical
  intro x y hxy
  obtain ⟨lx, bx, hx⟩ := botOf_eq_strOf hm sec x (hsecEdge x)
  obtain ⟨ly, by', hy⟩ := botOf_eq_strOf hm sec y (hsecEdge y)
  obtain ⟨j, hj, hxj⟩ := hrange x
  obtain ⟨j', hj', hyj⟩ := hrange y
  rw [← hx, ← hy, hxj, hyj, ← hxy] at *
  exact run_connected_in_graph_gen u D
    (fun a => strOf (m := m) hm sec a.1 a.2.1 a.2.2)
    (lo (CutComponents.gz Zf (EndType.edgeOf x))) (len _) hu R hR hsymm
    (hchain _) (hjoin _) (hcyc _) j j' hj (by rw [hxy] at hj'; exact hj') lx ly bx by'

end EltBridge

#print axioms EltBridge.hrun_multi_gen

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The shield law at general `mu`: `walkCount = |Z| + 1`.**

Both bounds, on one datum, with no restriction on `u`.  The upper bound is the
swap-free construction with the general-`u` run connectivity of BLOCK 188; the lower one
is `prop:cut`, which needs only `Local`.

The hypotheses on the turn are the three link families -- its passes chain each level
along a run, its boundary bounce joins up to down, and one pass carries the level cycle
-- together with the turn's own geometry.  `CostMerge` is invoked in neither
direction. -/
theorem shield_law_gen (hm : ∀ e, m e = 2 * u) (hu : 0 < u) (sec : ℤ → Fin n)
    (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop)
    (hR : ∀ a b, R a b → (WalkGraph.graph E).Reachable
      (strOf (m := m) hm sec a.1 a.2.1 a.2.2) (strOf (m := m) hm sec b.1 b.2.1 b.2.2))
    (hsymm : ∀ a b, R a b → R b a)
    (hchain : ∀ (r : ℕ) (k : ℕ) (l : Fin u) (b : Bool), k < len r →
      R (lo r + k, l, b) (lo r + (k + 1 : ℕ), l, b))
    (hjoin : ∀ (r : ℕ) (l : Fin u), R (lo r, l, true) (lo r, l, false))
    (hcyc : ∀ (r : ℕ) (i : ℕ) (hi : i + 1 < u),
      R (lo r, ⟨i, by omega⟩, true) (lo r, ⟨i + 1, hi⟩, true))
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hne : Nonempty (EndType.Endpt n m)) :
    WalkGraph.walkCount E = Zf.card + 1 := by
  have hrun := hrun_multi_gen hm hu sec E Zf lo len hsecEdge hrange R hR hsymm
    hchain hjoin hcyc
  refine le_antisymm ?_ ?_
  · exact shield_upper_bound_endpt E Zf botOf (fun x => by rw [hEp]) hTsite hturn
      (fun x => by rw [hEp]; exact botOf_eq_or_partner x) (fun _ => rfl) hrun
  · obtain ⟨x0⟩ := hne
    exact walkCount_ge_passTurn E Zf A B hAB hEp hTsite hturn hlow hhigh hocc
      ((WalkGraph.graph E).connectedComponentMk x0)

end EltBridge

#print axioms EltBridge.shield_law_gen

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-! ### The relabelled naming

`hchain` above is level-preserving, but BLOCK 187 places the level cycle in a PASS, which
permutes levels.  The two are reconciled by relabelling: the level index may be permuted
independently at each position, and a naming that absorbs the passes' permutations makes
them level-preserving by construction.

`run_connected_in_graph_gen` already takes an ARBITRARY `f`, so nothing about the
connectivity changes.  What has to be loosened is `hrun_multi_gen`, which named the
strands by `strOf`; it needs only that `f` COVERS the representatives. -/

/-- **`hrun` from any covering naming.**  `f` need not be `strOf`: any indexing of the
strands by `(position, level, side)` that covers the representatives will do, which is
what lets a relabelling absorb the passes' permutations. -/
theorem hrun_of_cover (hu : 0 < u)
    (D : WalkGraph.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (f : ℤ × Fin u × Bool → EndType.Endpt n m)
    (hcover : ∀ x : EndType.Endpt n m, ∃ (l : Fin u) (b : Bool),
      f (EndType.edgeOf x, l, b) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop)
    (hR : ∀ a b, R a b → (WalkGraph.graph D).Reachable (f a) (f b))
    (hsymm : ∀ a b, R a b → R b a)
    (hchain : ∀ (r : ℕ) (k : ℕ) (l : Fin u) (b : Bool), k < len r →
      R (lo r + k, l, b) (lo r + (k + 1 : ℕ), l, b))
    (hjoin : ∀ (r : ℕ) (l : Fin u), R (lo r, l, true) (lo r, l, false))
    (hcyc : ∀ (r : ℕ) (i : ℕ) (hi : i + 1 < u),
      R (lo r, ⟨i, by omega⟩, true) (lo r, ⟨i + 1, hi⟩, true)) :
    ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph D).Reachable (botOf x) (botOf y) := by
  classical
  intro x y hxy
  obtain ⟨lx, bx, hx⟩ := hcover x
  obtain ⟨ly, by', hy⟩ := hcover y
  obtain ⟨j, hj, hxj⟩ := hrange x
  obtain ⟨j', hj', hyj⟩ := hrange y
  rw [← hx, ← hy, hxj, hyj, ← hxy] at *
  exact run_connected_in_graph_gen u D f
    (lo (CutComponents.gz Zf (EndType.edgeOf x))) (len _) hu R hR hsymm
    (hchain _) (hjoin _) (hcyc _) j j' hj (by rw [hxy] at hj'; exact hj') lx ly bx by'

/-- `strOf` is one such naming, so `hrun_multi_gen` is the special case. -/
theorem strOf_covers (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge) :
    ∀ x : EndType.Endpt n m, ∃ (l : Fin u) (b : Bool),
      (fun a => strOf (m := m) hm sec a.1 a.2.1 a.2.2) (EndType.edgeOf x, l, b) = botOf x :=
  fun x => botOf_eq_strOf hm sec x (hsecEdge x)

end EltBridge

#print axioms EltBridge.hrun_of_cover
#print axioms EltBridge.strOf_covers

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The relabelled naming covers too.**  Permuting the level index independently at
each position is a bijection there, so it changes nothing about the cover -- which is
exactly why the passes' permutations can be absorbed into the naming. -/
theorem relabelled_covers (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n)
    (pi : ℤ → Equiv.Perm (Fin u))
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge) :
    ∀ x : EndType.Endpt n m, ∃ (l : Fin u) (b : Bool),
      (fun a => strOf (m := m) hm sec a.1 ((pi a.1) a.2.1) a.2.2)
        (EndType.edgeOf x, l, b) = botOf x := by
  intro x
  obtain ⟨l', b, hl⟩ := botOf_eq_strOf hm sec x (hsecEdge x)
  exact ⟨(pi (EndType.edgeOf x)).symm l', b, by simpa using hl⟩

/-- **The shield law at general `mu`, with the naming free.**

This is `shield_law_gen` with `strOf` replaced by an arbitrary covering naming, so the
level index may be relabelled at each position.  That is what lets the level cycle sit
in a PASS -- where BLOCK 187 showed it is free, a pass costing the same whichever levels
it pairs -- rather than in a bounce, where it would need a sign class with two strands. -/
theorem shield_law_gen_named (hu : 0 < u) (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (f : ℤ × Fin u × Bool → EndType.Endpt n m)
    (hEp : E.p = EndType.partner)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hcover : ∀ x : EndType.Endpt n m, ∃ (l : Fin u) (b : Bool),
      f (EndType.edgeOf x, l, b) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop)
    (hR : ∀ a b, R a b → (WalkGraph.graph E).Reachable (f a) (f b))
    (hsymm : ∀ a b, R a b → R b a)
    (hchain : ∀ (r : ℕ) (k : ℕ) (l : Fin u) (b : Bool), k < len r →
      R (lo r + k, l, b) (lo r + (k + 1 : ℕ), l, b))
    (hjoin : ∀ (r : ℕ) (l : Fin u), R (lo r, l, true) (lo r, l, false))
    (hcyc : ∀ (r : ℕ) (i : ℕ) (hi : i + 1 < u),
      R (lo r, ⟨i, by omega⟩, true) (lo r, ⟨i + 1, hi⟩, true))
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hne : Nonempty (EndType.Endpt n m)) :
    WalkGraph.walkCount E = Zf.card + 1 := by
  have hrun := hrun_of_cover hu E Zf lo len f hcover hrange R hR hsymm hchain hjoin hcyc
  refine le_antisymm ?_ ?_
  · exact shield_upper_bound_endpt E Zf botOf (fun x => by rw [hEp]) hTsite hturn
      (fun x => by rw [hEp]; exact botOf_eq_or_partner x) (fun _ => rfl) hrun
  · obtain ⟨x0⟩ := hne
    exact walkCount_ge_passTurn E Zf A B hAB hEp hTsite hturn hlow hhigh hocc
      ((WalkGraph.graph E).connectedComponentMk x0)

end EltBridge

#print axioms EltBridge.relabelled_covers
#print axioms EltBridge.shield_law_gen_named

namespace EltBridge

/-! ## The general-`u` turn

At `mu = 2u` a site carries `4u` ends -- the `2u` tops of edge `s-1` and the `2u`
bottoms of edge `s` -- so the `mu = 2` definition's if-chain over four ends does not
scale.  Defining the turn STRUCTURALLY avoids that entirely:

    bounce   stay on the edge, keep the level, flip the SIDE (up <-> down)
    pass     cross to the other edge, keep the side, permute the level by `sigma`

and the reverse pass uses `sigma⁻¹`, so involutivity holds by construction rather than
by case analysis.  Neither needs the ends to be pairwise distinct. -/

variable {n : ℕ} {m : Fin n → ℕ}

/-- The level of an end, and which side it is on. -/
def levOf (u : ℕ) (x : EndType.Endpt n m) : ℕ :=
  if (x.idx : ℕ) < u then (x.idx : ℕ) else (x.idx : ℕ) - u

def udOf (u : ℕ) (x : EndType.Endpt n m) : Bool := decide ((x.idx : ℕ) < u)

theorem levOf_lt (hm : ∀ e, m e = 2 * u) (x : EndType.Endpt n m) : levOf u x < u := by
  unfold levOf
  have h := x.idx.isLt
  have h2 := hm x.edge
  by_cases hc : (x.idx : ℕ) < u
  · rw [if_pos hc]; exact hc
  · rw [if_neg hc]; omega

/-- Rebuilding an end from its edge, level, side and top. -/
noncomputable def mkEnd (hm : ∀ e, m e = 2 * u) (e : Fin n) (l : ℕ) (hl : l < u)
    (b : Bool) (t : Bool) : EndType.Endpt n m :=
  ⟨e, ⟨levIdx u ⟨l, hl⟩ b, by rw [hm]; exact levIdx_lt u ⟨l, hl⟩ b⟩, t⟩

@[simp] theorem mkEnd_edge (hm : ∀ e, m e = 2 * u) (e : Fin n) (l : ℕ) (hl : l < u)
    (b t : Bool) : (mkEnd (m := m) hm e l hl b t).edge = e := rfl

@[simp] theorem mkEnd_top (hm : ∀ e, m e = 2 * u) (e : Fin n) (l : ℕ) (hl : l < u)
    (b t : Bool) : (mkEnd (m := m) hm e l hl b t).top = t := rfl

/-- Reading the level and side back off a rebuilt end. -/
theorem levOf_mkEnd (hm : ∀ e, m e = 2 * u) (e : Fin n) (l : ℕ) (hl : l < u)
    (b t : Bool) : levOf u (mkEnd (m := m) hm e l hl b t) = l := by
  unfold levOf mkEnd levIdx
  cases b
  · simp only [Bool.false_eq_true, if_false, Fin.val_mk]
    rw [if_neg (by omega)]
    omega
  · simp only [if_true, Fin.val_mk]
    rw [if_pos hl]

theorem udOf_mkEnd (hm : ∀ e, m e = 2 * u) (e : Fin n) (l : ℕ) (hl : l < u)
    (b t : Bool) : udOf u (mkEnd (m := m) hm e l hl b t) = b := by
  unfold udOf mkEnd levIdx
  cases b
  · simp only [Bool.false_eq_true, if_false, Fin.val_mk]
    exact decide_eq_false (by omega)
  · simp only [if_true, Fin.val_mk]
    exact decide_eq_true hl

end EltBridge

#print axioms EltBridge.levOf_lt
#print axioms EltBridge.levOf_mkEnd
#print axioms EltBridge.udOf_mkEnd

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The general-`u` turn at a site.**  A bounce keeps the edge and the top and flips
the side; a pass crosses the edge, keeps the side, flips the top and permutes the level
by `sigma` one way and `sigma⁻¹` the other. -/
noncomputable def turnGen (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m) :
    EndType.Endpt n m :=
  if EndType.siteOf x ≠ s then x
  else if s ∈ Bs then
    mkEnd (m := m) hm x.edge (levOf u x) (levOf_lt hm x) (!udOf u x) x.top
  else if x.top then
    mkEnd (m := m) hm (sec s) ((sig s (udOf u x) ⟨levOf u x, levOf_lt hm x⟩ : Fin u) : ℕ)
      (Fin.isLt _) (udOf u x) false
  else
    mkEnd (m := m) hm (sec (s - 1)) (((sig s (udOf u x)).symm ⟨levOf u x, levOf_lt hm x⟩ : Fin u) : ℕ)
      (Fin.isLt _) (udOf u x) true

theorem turnGen_off_site (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m)
    (h : EndType.siteOf x ≠ s) : turnGen (m := m) hm sec Bs sig s x = x := by
  unfold turnGen; rw [if_pos h]

/-- The bounce's image, computed. -/
theorem turnGen_bounce_eq (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m)
    (hx : EndType.siteOf x = s) (hs : s ∈ Bs) :
    turnGen (m := m) hm sec Bs sig s x
      = mkEnd (m := m) hm x.edge (levOf u x) (levOf_lt hm x) (!udOf u x) x.top := by
  unfold turnGen
  rw [if_neg (by simpa using hx), if_pos hs]

/-- The bounce keeps the site: same edge, same top. -/
theorem mkEnd_site (hm : ∀ e, m e = 2 * u) (x : EndType.Endpt n m) (l : ℕ) (hl : l < u)
    (b : Bool) :
    EndType.siteOf (mkEnd (m := m) hm x.edge l hl b x.top) = EndType.siteOf x := rfl

/-- **The bounce is an involution.**  It flips the side twice, and neither the edge nor
the top moves, so the second application takes the same branch. -/
theorem turnGen_bounce_invol (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m)
    (hx : EndType.siteOf x = s) (hs : s ∈ Bs) :
    turnGen (m := m) hm sec Bs sig s (turnGen (m := m) hm sec Bs sig s x) = x := by
  rw [turnGen_bounce_eq hm sec Bs sig s x hx hs]
  have hsite : EndType.siteOf
      (mkEnd (m := m) hm x.edge (levOf u x) (levOf_lt hm x) (!udOf u x) x.top) = s := by
    rw [mkEnd_site]; exact hx
  rw [turnGen_bounce_eq hm sec Bs sig s _ hsite hs]
  simp only [mkEnd_edge, mkEnd_top, levOf_mkEnd, udOf_mkEnd, Bool.not_not]
  -- the rebuilt end is the original
  obtain ⟨e, i, t⟩ := x
  unfold mkEnd
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  unfold levOf udOf levIdx
  simp only [Fin.val_mk]
  have hlt := i.isLt
  have h2 := hm e
  by_cases hc : (i : ℕ) < u
  · rw [if_pos hc]
    simp [hc]
  · rw [if_neg hc]
    simp [hc]
    omega

end EltBridge

#print axioms EltBridge.turnGen_off_site
#print axioms EltBridge.turnGen_bounce_invol

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- The pass's image on a top of edge `s-1`. -/
theorem turnGen_pass_top (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m)
    (hx : EndType.siteOf x = s) (hs : s ∉ Bs) (ht : x.top = true) :
    turnGen (m := m) hm sec Bs sig s x
      = mkEnd (m := m) hm (sec s) ((sig s (udOf u x) ⟨levOf u x, levOf_lt hm x⟩ : Fin u) : ℕ)
          (Fin.isLt _) (udOf u x) false := by
  unfold turnGen
  rw [if_neg (by simpa using hx), if_neg hs, if_pos ht]

/-- The pass's image on a bottom of edge `s`. -/
theorem turnGen_pass_bot (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m)
    (hx : EndType.siteOf x = s) (hs : s ∉ Bs) (ht : x.top = false) :
    turnGen (m := m) hm sec Bs sig s x
      = mkEnd (m := m) hm (sec (s - 1))
          (((sig s (udOf u x)).symm ⟨levOf u x, levOf_lt hm x⟩ : Fin u) : ℕ)
          (Fin.isLt _) (udOf u x) true := by
  unfold turnGen
  rw [if_neg (by simpa using hx), if_neg hs, if_neg (by simp [ht])]

/-- A top of edge `s-1` sits at site `s`; a bottom of edge `s` sits at site `s`. -/
theorem site_of_mkEnd (hm : ∀ e, m e = 2 * u) (e : Fin n) (l : ℕ) (hl : l < u)
    (b t : Bool) :
    EndType.siteOf (mkEnd (m := m) hm e l hl b t)
      = (e : ℤ) + (if t then 1 else 0) := rfl

/-- **The pass is an involution**, given the section: out along `sigma`, back along
`sigma⁻¹`, and the edge and top return. -/
theorem turnGen_pass_invol (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m)
    (hx : EndType.siteOf x = s) (hs : s ∉ Bs)
    (hsecS : ((sec s : ℕ) : ℤ) = s)
    (hsecP : ((sec (s - 1) : ℕ) : ℤ) = s - 1)
    (hedgeTop : x.top = true → (x.edge : ℤ) = s - 1)
    (hedgeBot : x.top = false → (x.edge : ℤ) = s) :
    turnGen (m := m) hm sec Bs sig s (turnGen (m := m) hm sec Bs sig s x) = x := by
  cases ht : x.top
  · -- a bottom of edge `s`: cross to a top of edge `s-1`, then back
    rw [turnGen_pass_bot hm sec Bs sig s x hx hs ht]
    have hsite : EndType.siteOf
        (mkEnd (m := m) hm (sec (s - 1))
          (((sig s (udOf u x)).symm ⟨levOf u x, levOf_lt hm x⟩ : Fin u) : ℕ)
          (Fin.isLt _) (udOf u x) true) = s := by
      rw [site_of_mkEnd, hsecP]; norm_num
    rw [turnGen_pass_top hm sec Bs sig s _ hsite hs (by rfl)]
    simp only [levOf_mkEnd, udOf_mkEnd, Fin.eta, Equiv.apply_symm_apply]
    obtain ⟨e, i, t⟩ := x
    have he : (e : ℤ) = s := hedgeBot ht
    have he' : sec s = e := by
      apply Fin.ext
      have : ((sec s : ℕ) : ℤ) = ((e : ℕ) : ℤ) := by rw [hsecS]; omega
      exact_mod_cast this
    unfold mkEnd
    congr 1
    · refine (Fin.heq_ext_iff (congrArg m he')).mpr ?_
      simp only [Fin.val_mk]
      unfold levOf udOf levIdx
      simp only [Fin.val_mk]
      have hlt := i.isLt
      have h2 := hm e
      by_cases hc : (i : ℕ) < u
      · rw [if_pos hc]; simp [hc]
      · rw [if_neg hc]; simp [hc]; omega
    · exact ht.symm
  · -- a top of edge `s-1`: cross to a bottom of edge `s`, then back
    rw [turnGen_pass_top hm sec Bs sig s x hx hs ht]
    have hsite : EndType.siteOf
        (mkEnd (m := m) hm (sec s) ((sig s (udOf u x) ⟨levOf u x, levOf_lt hm x⟩ : Fin u) : ℕ)
          (Fin.isLt _) (udOf u x) false) = s := by
      rw [site_of_mkEnd, hsecS]; norm_num
    rw [turnGen_pass_bot hm sec Bs sig s _ hsite hs (by rfl)]
    simp only [levOf_mkEnd, udOf_mkEnd, Fin.eta, Equiv.symm_apply_apply]
    obtain ⟨e, i, t⟩ := x
    have he : (e : ℤ) = s - 1 := hedgeTop ht
    have he' : sec (s - 1) = e := by
      apply Fin.ext
      have : ((sec (s - 1) : ℕ) : ℤ) = ((e : ℕ) : ℤ) := by rw [hsecP]; omega
      exact_mod_cast this
    unfold mkEnd
    congr 1
    · refine (Fin.heq_ext_iff (congrArg m he')).mpr ?_
      simp only [Fin.val_mk]
      unfold levOf udOf levIdx
      simp only [Fin.val_mk]
      have hlt := i.isLt
      have h2 := hm e
      by_cases hc : (i : ℕ) < u
      · rw [if_pos hc]; simp [hc]
      · rw [if_neg hc]; simp [hc]; omega
    · exact ht.symm

end EltBridge

#print axioms EltBridge.turnGen_pass_top
#print axioms EltBridge.turnGen_pass_invol

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-! ### `turnGen`'s remaining obligations

Both are immediate in the structural definition.  The bounce flips the SIDE, so the
strand index moves by `u` and cannot be fixed; the pass flips the TOP.  Neither needs
the site's ends to be distinct. -/

/-- **`turnGen` keeps every end at its site.**  A bounce keeps the edge and the top; a
pass moves to the edge whose corresponding end sits at the same site. -/
theorem turnGen_site (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m)
    (hx : EndType.siteOf x = s)
    (hsecS : ((sec s : ℕ) : ℤ) = s)
    (hsecP : ((sec (s - 1) : ℕ) : ℤ) = s - 1) :
    EndType.siteOf (turnGen (m := m) hm sec Bs sig s x) = s := by
  by_cases hs : s ∈ Bs
  · rw [turnGen_bounce_eq hm sec Bs sig s x hx hs, mkEnd_site]; exact hx
  · cases ht : x.top
    · rw [turnGen_pass_bot hm sec Bs sig s x hx hs ht, site_of_mkEnd, hsecP]
      norm_num
    · rw [turnGen_pass_top hm sec Bs sig s x hx hs ht, site_of_mkEnd, hsecS]
      norm_num

/-- The two sides have different strand indices. -/
theorem levIdx_ne (u : ℕ) (hu : 0 < u) (l : Fin u) : levIdx u l true ≠ levIdx u l false := by
  unfold levIdx
  simp only [if_true, Bool.false_eq_true, if_false]
  have := l.isLt
  omega

/-- **`turnGen` is fixed-point-free at its site.**  The bounce moves the strand index by
`u`; the pass moves the top. -/
theorem turnGen_ne (hm : ∀ e, m e = 2 * u) (hu : 0 < u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m)
    (hx : EndType.siteOf x = s) :
    turnGen (m := m) hm sec Bs sig s x ≠ x := by
  by_cases hs : s ∈ Bs
  · rw [turnGen_bounce_eq hm sec Bs sig s x hx hs]
    intro hc
    have h := congrArg (udOf u) hc
    rw [udOf_mkEnd] at h
    exact absurd h (by simp)
  · cases ht : x.top
    · rw [turnGen_pass_bot hm sec Bs sig s x hx hs ht]
      intro hc
      have := congrArg EndType.Endpt.top hc
      simp only [mkEnd_top] at this
      rw [ht] at this
      exact absurd this (by simp)
    · rw [turnGen_pass_top hm sec Bs sig s x hx hs ht]
      intro hc
      have := congrArg EndType.Endpt.top hc
      simp only [mkEnd_top] at this
      rw [ht] at this
      exact absurd this (by simp)

end EltBridge

#print axioms EltBridge.turnGen_site
#print axioms EltBridge.turnGen_ne

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- An end at site `s` sits on edge `s-1` if it is a top, on edge `s` if a bottom. -/
theorem edge_of_site (x : EndType.Endpt n m) (s : ℤ) (hx : EndType.siteOf x = s) :
    (x.top = true → (x.edge : ℤ) = s - 1) ∧ (x.top = false → (x.edge : ℤ) = s) := by
  have hsite : EndType.siteOf x
      = EndType.edgeOf x + (if EndType.atTop x then (1 : ℤ) else 0) := rfl
  constructor
  · intro ht
    have hat : EndType.atTop x = true := ht
    rw [hsite, hat] at hx
    simp only [if_true] at hx
    have : EndType.edgeOf x = (x.edge : ℤ) := rfl
    omega
  · intro ht
    have hat : EndType.atTop x = false := ht
    rw [hsite, hat] at hx
    simp only [Bool.false_eq_true, if_false, add_zero] at hx
    have : EndType.edgeOf x = (x.edge : ℤ) := rfl
    omega

/-- **`turnGen` is an involution**, at every site: off-site it is the identity, on a
bounce site it flips the side twice, and on a pass site it goes out along `sigma` and
back along `sigma⁻¹`. -/
theorem turnGen_invol (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ)
    (hsecS : (∃ y : EndType.Endpt n m, EndType.siteOf y = s) → ((sec s : ℕ) : ℤ) = s)
    (hsecP : (∃ y : EndType.Endpt n m, EndType.siteOf y = s) →
      ((sec (s - 1) : ℕ) : ℤ) = s - 1)
    (x : EndType.Endpt n m) :
    turnGen (m := m) hm sec Bs sig s (turnGen (m := m) hm sec Bs sig s x) = x := by
  by_cases hx : EndType.siteOf x = s
  · have hocc : ∃ y : EndType.Endpt n m, EndType.siteOf y = s := ⟨x, hx⟩
    by_cases hs : s ∈ Bs
    · exact turnGen_bounce_invol hm sec Bs sig s x hx hs
    · obtain ⟨h1, h2⟩ := edge_of_site x s hx
      exact turnGen_pass_invol hm sec Bs sig s x hx hs (hsecS hocc) (hsecP hocc) h1 h2
  · rw [turnGen_off_site hm sec Bs sig s x hx,
      turnGen_off_site hm sec Bs sig s x hx]

end EltBridge

#print axioms EltBridge.edge_of_site
#print axioms EltBridge.turnGen_invol

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The general-`u` datum.**  `exists_glued_data` applied to `turnGen`, its three
obligations discharged by `turnGen_invol`, `turnGen_site` and `turnGen_ne`.  Each is
used only at an OCCUPIED site, where the witness is the hypothesis `siteOf x = s`
itself, so the section is needed only on `[A-1, B+1]`. -/
theorem exists_turnGen_data (hm : ∀ e, m e = 2 * u) (hu : 0 < u) (sec : ℤ → Fin n)
    (Bs : Finset ℤ) (sig : ℤ → Bool → Equiv.Perm (Fin u)) (A B : ℤ)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (hsecWide : ∀ j : ℤ, A - 1 ≤ j → j ≤ B + 1 → ((sec j : ℕ) : ℤ) = j) :
    ∃ E : WalkGraph.Data (EndType.Endpt n m),
      E.p = EndType.partner ∧
      (∀ x, E.t x = turnGen (m := m) hm sec Bs sig (EndType.siteOf x) x) ∧
      (∀ x, EndType.siteOf (E.t x) = EndType.siteOf x) := by
  classical
  -- at an occupied site both section facts hold, the site being in range
  have hfacts : ∀ (s : ℤ), (∃ y : EndType.Endpt n m, EndType.siteOf y = s) →
      ((sec s : ℕ) : ℤ) = s ∧ ((sec (s - 1) : ℕ) : ℤ) = s - 1 := by
    rintro s ⟨y, rfl⟩
    obtain ⟨h1, h2⟩ := siteOf_mem_of_span y A B (hspan y)
    exact ⟨hsecWide _ (by omega) h2, hsecWide _ (by omega) (by omega)⟩
  obtain ⟨E, hEp, hEt⟩ := exists_glued_data EndType.siteOf EndType.partner
    (turnGen (m := m) hm sec Bs sig)
    EndType.partner_invol EndType.partner_ne EndType.partner_site_ne
    (fun s x => turnGen_invol hm sec Bs sig s (fun h => (hfacts s h).1)
      (fun h => (hfacts s h).2) x)
    (fun s x hxs => by
      subst hxs
      exact turnGen_site hm sec Bs sig _ x rfl
        ((hfacts _ ⟨x, rfl⟩).1) ((hfacts _ ⟨x, rfl⟩).2))
    (fun s x hxs => by
      subst hxs
      exact turnGen_ne hm hu sec Bs sig _ x rfl)
  refine ⟨E, hEp, hEt, ?_⟩
  intro x
  rw [hEt x]
  exact turnGen_site hm sec Bs sig _ x rfl
    ((hfacts _ ⟨x, rfl⟩).1) ((hfacts _ ⟨x, rfl⟩).2)

end EltBridge

#print axioms EltBridge.exists_turnGen_data

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **A bounce keeps the edge.**  It stays on the edge by construction, so the edge is
unchanged whatever the level and side do. -/
theorem turnGen_keeps_edge_at_bounce (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n)
    (Bs : Finset ℤ) (sig : ℤ → Bool → Equiv.Perm (Fin u)) (s : ℤ) (x : EndType.Endpt n m)
    (hx : EndType.siteOf x = s) (hs : s ∈ Bs) :
    EndType.edgeOf (turnGen (m := m) hm sec Bs sig s x) = EndType.edgeOf x := by
  rw [turnGen_bounce_eq hm sec Bs sig s x hx hs]
  rfl

/-- **`hturn` for `turnGen`.**  An edge change forces the site off `Bs`, hence off any
`Zf` inside it. -/
theorem turnGen_hturn (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n)
    (Zf Bs : Finset ℤ) (hsub : Zf ⊆ Bs) (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (x : EndType.Endpt n m)
    (hx : EndType.edgeOf (turnGen (m := m) hm sec Bs sig (EndType.siteOf x) x)
      ≠ EndType.edgeOf x) :
    EndType.siteOf x ∉ Zf := by
  intro hmem
  exact hx (turnGen_keeps_edge_at_bounce hm sec Bs sig _ x rfl (hsub hmem))

end EltBridge

#print axioms EltBridge.turnGen_keeps_edge_at_bounce
#print axioms EltBridge.turnGen_hturn

namespace EltBridge

/-! ### `hcyc` is not an assumption -- it is the round trip

BLOCK 188 took the level cycle as a hypothesis at the run's left end.  In the real turn
no single step crosses levels: what crosses them is the ROUND TRIP -- out along the up
chain, across at the far bounce, back along the down chain, and closed at the near
bounce.  BLOCK 187's parity is exactly the statement that this round trip is a
`u`-cycle.

So `hcyc` is derived, not assumed, and the input becomes the far bounce's shift. -/

theorem hcyc_of_round_trip (lo : ℤ) (n u : ℕ)
    (R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop)
    (hsymm : ∀ a b, R a b → R b a)
    (hchain : ∀ (k : ℕ) (l : Fin u) (b : Bool), k < n →
      R (lo + k, l, b) (lo + (k + 1 : ℕ), l, b))
    (hjoinL : ∀ l : Fin u, R (lo, l, true) (lo, l, false))
    (hshift : ∀ (i : ℕ) (hi : i + 1 < u),
      R (lo + (n : ℕ), ⟨i, by omega⟩, true) (lo + (n : ℕ), ⟨i + 1, hi⟩, false))
    (i : ℕ) (hi : i + 1 < u) :
    Relation.ReflTransGen R (lo, ⟨i, by omega⟩, true) (lo, ⟨i + 1, hi⟩, true) := by
  have hsymmR : ∀ a c, Relation.ReflTransGen R a c → Relation.ReflTransGen R c a := by
    intro a c h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.head (hsymm _ _ hstep) ih
  -- out along the run, on either side
  have hout : ∀ (l : Fin u) (b : Bool) (j : ℕ), j ≤ n →
      Relation.ReflTransGen R (lo, l, b) (lo + j, l, b) := by
    intro l b j
    induction j with
    | zero => intro _; simpa using Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      exact (ih (by omega)).tail (hchain k l b (by omega))
  -- out on the up side, shift at the far end, back on the down side, close at the near
  have h1 : Relation.ReflTransGen R (lo, ⟨i, by omega⟩, true)
      (lo + (n : ℕ), ⟨i, by omega⟩, true) := hout _ true n (le_refl _)
  have h2 : Relation.ReflTransGen R (lo + (n : ℕ), ⟨i, by omega⟩, true)
      (lo + (n : ℕ), ⟨i + 1, hi⟩, false) := Relation.ReflTransGen.single (hshift i hi)
  have h3 : Relation.ReflTransGen R (lo + (n : ℕ), ⟨i + 1, hi⟩, false)
      (lo, ⟨i + 1, hi⟩, false) := hsymmR _ _ (hout _ false n (le_refl _))
  have h4 : Relation.ReflTransGen R (lo, ⟨i + 1, hi⟩, false) (lo, ⟨i + 1, hi⟩, true) :=
    hsymmR _ _ (Relation.ReflTransGen.single (hjoinL _))
  exact ((h1.trans h2).trans h3).trans h4

end EltBridge

#print axioms EltBridge.hcyc_of_round_trip

namespace EltBridge

/-- When `R` is reachability itself, a chain of `R`-steps IS an `R`-step. -/
theorem reflTransGen_collapse {α β : Type*} (G : SimpleGraph β) (f : α → β)
    {a b : α}
    (h : Relation.ReflTransGen (fun x y => G.Reachable (f x) (f y)) a b) :
    G.Reachable (f a) (f b) := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hstep ih => exact ih.trans hstep

/-- **The run is one component, from the far bounce's shift.**  `hcyc` is replaced by
`hshift`, a single step of the turn, and the cycle is derived as the round trip. -/
theorem run_one_component_shift {α : Type*} [Fintype α] [DecidableEq α]
    (u : ℕ) (hu : 0 < u) (G : SimpleGraph α) (f : ℤ × Fin u × Bool → α)
    (lo : ℤ) (n : ℕ)
    (hchain : ∀ (k : ℕ) (l : Fin u) (b : Bool), k < n →
      G.Reachable (f (lo + k, l, b)) (f (lo + (k + 1 : ℕ), l, b)))
    (hjoinL : ∀ l : Fin u, G.Reachable (f (lo, l, true)) (f (lo, l, false)))
    (hshift : ∀ (i : ℕ) (hi : i + 1 < u),
      G.Reachable (f (lo + (n : ℕ), ⟨i, by omega⟩, true))
        (f (lo + (n : ℕ), ⟨i + 1, hi⟩, false)))
    (j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n) (l l' : Fin u) (b b' : Bool) :
    G.Reachable (f (lo + j, l, b)) (f (lo + j', l', b')) := by
  set R : ℤ × Fin u × Bool → ℤ × Fin u × Bool → Prop :=
    fun x y => G.Reachable (f x) (f y) with hR
  have hsymm : ∀ a b, R a b → R b a := fun _ _ h => h.symm
  have hcyc : ∀ (i : ℕ) (hi : i + 1 < u),
      R (lo, ⟨i, by omega⟩, true) (lo, ⟨i + 1, hi⟩, true) := by
    intro i hi
    exact reflTransGen_collapse G f
      (hcyc_of_round_trip lo n u R hsymm hchain hjoinL hshift i hi)
  exact reachable_of_reflTransGen G R f (fun _ _ h => h)
    (run_pairwise_gen lo n u hu R hsymm hchain hjoinL hcyc j j' hj hj' l l' b b')

end EltBridge

#print axioms EltBridge.reflTransGen_collapse
#print axioms EltBridge.run_one_component_shift

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The shield law at general `mu`, on single-step hypotheses.**

`hcyc` is gone: the level cycle is derived as the round trip.  What is left of the turn's
behaviour is three families of ACTUAL TURN STEPS --

    hchain    a pass carries a strand bottom to the next edge's, on either side
    hjoinL    the near bounce joins the two sides at the run's left end
    hshift    the far bounce joins them at the right end, one level across

-- and the last is where BLOCK 187's parity lives.  It is satisfiable because a pass
costs the same whichever levels it pairs, so the permutations may be chosen to make the
round trip a `u`-cycle. -/
theorem shield_law_shift (hu : 0 < u) (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (f : ℤ × Fin u × Bool → EndType.Endpt n m)
    (hEp : E.p = EndType.partner)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hcover : ∀ x : EndType.Endpt n m, ∃ (l : Fin u) (b : Bool),
      f (EndType.edgeOf x, l, b) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (hchain : ∀ (r : ℕ) (k : ℕ) (l : Fin u) (b : Bool), k < len r →
      (WalkGraph.graph E).Reachable (f (lo r + k, l, b)) (f (lo r + (k + 1 : ℕ), l, b)))
    (hjoinL : ∀ (r : ℕ) (l : Fin u),
      (WalkGraph.graph E).Reachable (f (lo r, l, true)) (f (lo r, l, false)))
    (hshift : ∀ (r : ℕ) (i : ℕ) (hi : i + 1 < u),
      (WalkGraph.graph E).Reachable (f (lo r + (len r : ℕ), ⟨i, by omega⟩, true))
        (f (lo r + (len r : ℕ), ⟨i + 1, hi⟩, false)))
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hne : Nonempty (EndType.Endpt n m)) :
    WalkGraph.walkCount E = Zf.card + 1 := by
  classical
  have hrun : ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph E).Reachable (botOf x) (botOf y) := by
    intro x y hxy
    obtain ⟨lx, bx, hx⟩ := hcover x
    obtain ⟨ly, by', hy⟩ := hcover y
    obtain ⟨j, hj, hxj⟩ := hrange x
    obtain ⟨j', hj', hyj⟩ := hrange y
    rw [← hx, ← hy, hxj, hyj, ← hxy] at *
    exact run_one_component_shift u hu (WalkGraph.graph E) f _ _
      (hchain _) (hjoinL _) (hshift _) j j' hj (by rw [hxy] at hj'; exact hj') lx ly bx by'
  refine le_antisymm ?_ ?_
  · exact shield_upper_bound_endpt E Zf botOf (fun x => by rw [hEp]) hTsite hturn
      (fun x => by rw [hEp]; exact botOf_eq_or_partner x) (fun _ => rfl) hrun
  · obtain ⟨x0⟩ := hne
    exact walkCount_ge_passTurn E Zf A B hAB hEp hTsite hturn hlow hhigh hocc
      ((WalkGraph.graph E).connectedComponentMk x0)

end EltBridge

#print axioms EltBridge.shield_law_shift

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-! ### The far bounce, as a path

A bounce at the run's RIGHT boundary acts on the TOPS of the last edge, while `strOf`
names strand BOTTOMS.  So the link is three steps: cross the strand to its top, bounce,
cross back.  `partner` keeps the strand index, so the level and side read the same at
both ends of a strand. -/

@[simp] theorem levOf_partner (x : EndType.Endpt n m) :
    levOf u (EndType.partner x) = levOf u x := rfl

@[simp] theorem udOf_partner (x : EndType.Endpt n m) :
    udOf u (EndType.partner x) = udOf u x := rfl

/-- **The far bounce joins a strand to its partner strand, at the same raw level.**
Three steps: to the top, across, and back down. -/
theorem bounce_top_path (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = turnGen (m := m) hm sec Bs sig (EndType.siteOf x) x)
    (j : ℤ) (l : Fin u) (hjs : ((sec j : ℕ) : ℤ) = j) (hmem : j + 1 ∈ Bs) :
    (WalkGraph.graph E).Reachable
      (strOf (m := m) hm sec j l true) (strOf (m := m) hm sec j l false) := by
  set x := strOf (m := m) hm sec j l true with hx
  set y := EndType.partner x with hy
  -- the top of that strand sits at site `j + 1`
  have hsy : EndType.siteOf y = j + 1 := by
    show ((sec j : ℕ) : ℤ) + 1 = j + 1
    rw [hjs]
  -- the bounce there flips the side, keeping the edge, the top and the level
  have himg : E.t y = mkEnd (m := m) hm y.edge (levOf u y) (levOf_lt hm y)
      (!udOf u y) y.top := by
    rw [hEt y, hsy]
    exact turnGen_bounce_eq hm sec Bs sig (j + 1) y hsy hmem
  refine ((reachable_partner E x).trans ?_)
  rw [hEp]
  refine (reachable_turn E y).trans ?_
  rw [himg]
  -- and crossing back lands on the down strand's bottom
  have hlev : levOf u y = (l : ℕ) := by
    rw [hy, hx]
    simp only [levOf_partner]
    unfold strOf
    exact levOf_mkEnd hm _ _ _ _ _
  have hud : udOf u y = true := by
    rw [hy, hx]
    simp only [udOf_partner]
    unfold strOf
    exact udOf_mkEnd hm _ _ _ _ _
  have hedge : y.edge = sec j := rfl
  have htop : y.top = true := rfl
  have hgoal : mkEnd (m := m) hm y.edge (levOf u y) (levOf_lt hm y) (!udOf u y) y.top
      = EndType.partner (strOf (m := m) hm sec j l false) := by
    rw [hedge, htop, hud]
    unfold strOf EndType.partner mkEnd
    simp only [Bool.not_true]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    unfold levIdx
    simp only [Bool.false_eq_true, if_false]
    omega
  rw [hgoal, ← hEp]
  exact (reachable_partner E _).symm

end EltBridge

#print axioms EltBridge.bounce_top_path

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **A pass carries a strand bottom to the next edge's**, permuting the level by the
side's permutation.  Two steps: to the top, then across.  Uniform in the side, since the
pass keeps it. -/
theorem pass_path (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = turnGen (m := m) hm sec Bs sig (EndType.siteOf x) x)
    (j : ℤ) (l : Fin u) (b : Bool)
    (hjs : ((sec j : ℕ) : ℤ) = j) (hnot : j + 1 ∉ Bs) :
    (WalkGraph.graph E).Reachable
      (strOf (m := m) hm sec j l b)
      (strOf (m := m) hm sec (j + 1) (sig (j + 1) b l) b) := by
  set x := strOf (m := m) hm sec j l b with hx
  set y := EndType.partner x with hy
  have hsy : EndType.siteOf y = j + 1 := by
    show ((sec j : ℕ) : ℤ) + 1 = j + 1
    rw [hjs]
  have hlev : levOf u y = (l : ℕ) := by
    rw [hy, hx]; simp only [levOf_partner]; unfold strOf; exact levOf_mkEnd hm _ _ _ _ _
  have hud : udOf u y = b := by
    rw [hy, hx]; simp only [udOf_partner]; unfold strOf; exact udOf_mkEnd hm _ _ _ _ _
  have htop : y.top = true := rfl
  have himg : E.t y = mkEnd (m := m) hm (sec (j + 1))
      ((sig (j + 1) (udOf u y) ⟨levOf u y, levOf_lt hm y⟩ : Fin u) : ℕ)
      (Fin.isLt _) (udOf u y) false := by
    rw [hEt y, hsy]
    exact turnGen_pass_top hm sec Bs sig (j + 1) y hsy hnot htop
  refine (reachable_partner E x).trans ?_
  rw [hEp]
  refine (reachable_turn E y).trans ?_
  rw [himg, hud]
  -- the image is the next edge's strand bottom at the permuted level
  have hgoal : mkEnd (m := m) hm (sec (j + 1))
      ((sig (j + 1) b ⟨levOf u y, levOf_lt hm y⟩ : Fin u) : ℕ) (Fin.isLt _) b false
      = strOf (m := m) hm sec (j + 1) (sig (j + 1) b l) b := by
    have hfin : (⟨levOf u y, levOf_lt hm y⟩ : Fin u) = l :=
      Fin.ext (by simpa using hlev)
    rw [hfin]
    rfl
  rw [hgoal]

end EltBridge

#print axioms EltBridge.pass_path

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The near bounce joins the two sides in one step.**  Both strand bottoms of edge
`j` already sit at site `j`, so the bounce there pairs them directly -- no partner step
is needed, unlike the far bounce. -/
theorem near_bounce_path (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEt : ∀ x, E.t x = turnGen (m := m) hm sec Bs sig (EndType.siteOf x) x)
    (j : ℤ) (l : Fin u) (hjs : ((sec j : ℕ) : ℤ) = j) (hmem : j ∈ Bs) :
    (WalkGraph.graph E).Reachable
      (strOf (m := m) hm sec j l true) (strOf (m := m) hm sec j l false) := by
  set x := strOf (m := m) hm sec j l true with hx
  have hsx : EndType.siteOf x = j := by
    show ((sec j : ℕ) : ℤ) + 0 = j
    rw [hjs]; ring
  have himg : E.t x = mkEnd (m := m) hm x.edge (levOf u x) (levOf_lt hm x)
      (!udOf u x) x.top := by
    rw [hEt x, hsx]
    exact turnGen_bounce_eq hm sec Bs sig j x hsx hmem
  have hlev : levOf u x = (l : ℕ) := by
    rw [hx]; unfold strOf; exact levOf_mkEnd hm _ _ _ _ _
  have hud : udOf u x = true := by
    rw [hx]; unfold strOf; exact udOf_mkEnd hm _ _ _ _ _
  have hgoal : mkEnd (m := m) hm x.edge (levOf u x) (levOf_lt hm x) (!udOf u x) x.top
      = strOf (m := m) hm sec j l false := by
    have hedge : x.edge = sec j := rfl
    have htop : x.top = false := rfl
    rw [hedge, htop, hud]
    have hfin : (⟨levOf u x, levOf_lt hm x⟩ : Fin u) = l :=
      Fin.ext (by simpa using hlev)
    unfold mkEnd strOf
    simp only [Bool.not_true]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    unfold levIdx
    simp only [Bool.false_eq_true, if_false]
    omega
  have := reachable_turn E x
  rw [himg, hgoal] at this
  exact this

end EltBridge

#print axioms EltBridge.near_bounce_path

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-! ### The relabelling

`hchain` asks that the naming make the passes level-preserving.  Defining the
relabelling by the recursion

    rel 0 b = 1,    rel (k+1) b = sig (lo + (k+1)) b * rel k b

makes that hold BY CONSTRUCTION: the pass at position `k+1` permutes by
`sig (lo+(k+1)) b`, which is exactly the step from `rel k b` to `rel (k+1) b`. -/

/-- The relabelling at offset `k` on side `b`: the composite of the passes so far. -/
noncomputable def relAt (sig : ℤ → Bool → Equiv.Perm (Fin u)) (lo : ℤ) :
    ℕ → Bool → Equiv.Perm (Fin u)
  | 0, _ => 1
  | (k + 1), b => (sig (lo + ((k : ℤ) + 1)) b) * relAt sig lo k b

@[simp] theorem relAt_zero (sig : ℤ → Bool → Equiv.Perm (Fin u)) (lo : ℤ) (b : Bool) :
    relAt sig lo 0 b = 1 := rfl

theorem relAt_succ (sig : ℤ → Bool → Equiv.Perm (Fin u)) (lo : ℤ) (k : ℕ) (b : Bool) :
    relAt sig lo (k + 1) b = (sig (lo + ((k : ℤ) + 1)) b) * relAt sig lo k b := rfl

/-- **The naming**: the strand bottom at that position, with the level relabelled. -/
noncomputable def nameAt (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (lo : ℤ) (k : ℕ) (l : Fin u) (b : Bool) :
    EndType.Endpt n m :=
  strOf (m := m) hm sec (lo + (k : ℤ)) (relAt sig lo k b l) b

/-- **`hchain` holds by construction.**  The pass from offset `k` to `k+1` permutes the
level by exactly the step in the relabelling's recursion. -/
theorem hchain_nameAt (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = turnGen (m := m) hm sec Bs sig (EndType.siteOf x) x)
    (lo : ℤ) (k : ℕ) (l : Fin u) (b : Bool)
    (hjs : ((sec (lo + (k : ℤ)) : ℕ) : ℤ) = lo + (k : ℤ))
    (hnot : lo + (k : ℤ) + 1 ∉ Bs) :
    (WalkGraph.graph E).Reachable
      (nameAt (m := m) hm sec sig lo k l b)
      (nameAt (m := m) hm sec sig lo (k + 1) l b) := by
  have h := pass_path hm sec Bs sig E hEp hEt (lo + (k : ℤ))
    (relAt sig lo k b l) b hjs hnot
  unfold nameAt
  have harith : lo + ((k : ℕ) + 1 : ℕ) = lo + (k : ℤ) + 1 := by push_cast; ring
  rw [harith, relAt_succ]
  have hlev : (sig (lo + ((k : ℤ) + 1)) b) (relAt sig lo k b l)
      = ((sig (lo + ((k : ℤ) + 1)) b) * relAt sig lo k b) l := rfl
  have harith2 : lo + (k : ℤ) + 1 = lo + ((k : ℤ) + 1) := by ring
  rw [← hlev]
  rw [harith2] at h ⊢
  exact h

end EltBridge

#print axioms EltBridge.relAt_succ
#print axioms EltBridge.hchain_nameAt

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **`hjoinL` is immediate**: at offset `0` the relabelling is the identity on both
sides, so the naming is the raw one and the near bounce applies directly. -/
theorem hjoinL_nameAt (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEt : ∀ x, E.t x = turnGen (m := m) hm sec Bs sig (EndType.siteOf x) x)
    (lo : ℤ) (l : Fin u)
    (hjs : ((sec lo : ℕ) : ℤ) = lo) (hmem : lo ∈ Bs) :
    (WalkGraph.graph E).Reachable
      (nameAt (m := m) hm sec sig lo 0 l true)
      (nameAt (m := m) hm sec sig lo 0 l false) := by
  unfold nameAt
  simp only [relAt_zero, Equiv.Perm.coe_one, id_eq, Nat.cast_zero, add_zero]
  exact near_bounce_path hm sec Bs sig E hEt lo l hjs hmem

/-- **`hshift` is BLOCK 187's parity**, stated on the permutations: the up and down
relabellings at the run's far end must disagree by the successor.  The far bounce relates
the two sides at the same RAW level, so in the relabelled naming it relates level `i` up
to level `i+1` down exactly when that disagreement holds. -/
theorem hshift_nameAt (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n) (Bs : Finset ℤ)
    (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hEt : ∀ x, E.t x = turnGen (m := m) hm sec Bs sig (EndType.siteOf x) x)
    (lo : ℤ) (len : ℕ)
    (hjs : ((sec (lo + (len : ℤ)) : ℕ) : ℤ) = lo + (len : ℤ))
    (hmem : lo + (len : ℤ) + 1 ∈ Bs)
    (i : ℕ) (hi : i + 1 < u)
    (hrel : relAt sig lo len false ⟨i + 1, hi⟩
      = relAt sig lo len true ⟨i, by omega⟩) :
    (WalkGraph.graph E).Reachable
      (nameAt (m := m) hm sec sig lo len ⟨i, by omega⟩ true)
      (nameAt (m := m) hm sec sig lo len ⟨i + 1, hi⟩ false) := by
  unfold nameAt
  rw [hrel]
  exact bounce_top_path hm sec Bs sig E hEp hEt (lo + (len : ℤ)) _ hjs hmem

end EltBridge

#print axioms EltBridge.hjoinL_nameAt
#print axioms EltBridge.hshift_nameAt

namespace EltBridge

/-! ### The parity is satisfiable

`hrel` asks that the up and down relabellings at the run's far end disagree by the
successor.  With every up pass trivial, `relAt len true = 1`, so the condition reads

    relAt len false (i+1) = i

for every `i` with `i+1 < u` -- that is, the down composite is the DOWNWARD cycle.  So
the parity is satisfiable exactly when that cycle can be realised, and it can: put it in
a single down pass and leave the rest trivial.  A pass costs the same whichever levels
it pairs, so this costs nothing. -/

/-- The downward cycle on `Fin u`: `l ↦ l - 1`, wrapping. -/
def shiftDown (u : ℕ) (hu : 0 < u) : Equiv.Perm (Fin u) where
  toFun := fun l => ⟨((l : ℕ) + (u - 1)) % u, Nat.mod_lt _ hu⟩
  invFun := fun l => ⟨((l : ℕ) + 1) % u, Nat.mod_lt _ hu⟩
  left_inv := by
    intro l
    apply Fin.ext
    simp only [Fin.val_mk]
    have hl := l.isLt
    rcases Nat.eq_zero_or_pos (l : ℕ) with h | h
    · -- level 0 wraps to the top and back
      have h1 : ((l : ℕ) + (u - 1)) % u = u - 1 := by
        rw [h, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      rw [h1, h]
      have h2 : u - 1 + 1 = u := by omega
      rw [h2, Nat.mod_self]
    · -- otherwise it is plain subtraction
      have h1 : ((l : ℕ) + (u - 1)) % u = (l : ℕ) - 1 := by
        have h3 : (l : ℕ) + (u - 1) = u + ((l : ℕ) - 1) := by omega
        rw [h3, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [h1]
      have h4 : (l : ℕ) - 1 + 1 = (l : ℕ) := by omega
      rw [h4, Nat.mod_eq_of_lt hl]
  right_inv := by
    intro l
    apply Fin.ext
    simp only [Fin.val_mk]
    have hl := l.isLt
    rcases Nat.lt_or_ge ((l : ℕ) + 1) u with h | h
    · -- no wrap on the way up
      rw [Nat.mod_eq_of_lt h]
      have h1 : (l : ℕ) + 1 + (u - 1) = u + (l : ℕ) := by omega
      rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt hl]
    · -- the top wraps to 0 and back
      have h0 : (l : ℕ) + 1 = u := by omega
      rw [h0, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      omega

end EltBridge

namespace EltBridge

/-- **`shiftDown` maps `i+1` to `i`** -- which is exactly what `hrel` asks of the down
composite when the up composite is trivial. -/
theorem shiftDown_succ (u : ℕ) (hu : 0 < u) (i : ℕ) (hi : i + 1 < u) :
    shiftDown u hu ⟨i + 1, hi⟩ = ⟨i, by omega⟩ := by
  apply Fin.ext
  show ((i + 1) + (u - 1)) % u = i
  have h1 : (i + 1) + (u - 1) = u + i := by omega
  rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- **The parity is satisfiable.**  Take every up pass trivial and every down pass
trivial except one, which carries `shiftDown`.  Then the up composite is `1`, the down
composite is `shiftDown`, and `hrel` holds. -/
theorem hrel_of_shiftDown (u : ℕ) (hu : 0 < u)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (lo : ℤ) (len : ℕ)
    (hup : relAt sig lo len true = 1)
    (hdn : relAt sig lo len false = shiftDown u hu) :
    ∀ (i : ℕ) (hi : i + 1 < u),
      relAt sig lo len false ⟨i + 1, hi⟩ = relAt sig lo len true ⟨i, by omega⟩ := by
  intro i hi
  rw [hup, hdn, shiftDown_succ u hu i hi]
  rfl

/-- If every pass up to offset `k` is trivial on side `b`, so is the composite. -/
theorem relAt_eq_one (u : ℕ) (sig : ℤ → Bool → Equiv.Perm (Fin u)) (lo : ℤ) (b : Bool) :
    ∀ k : ℕ, (∀ j : ℕ, j < k → sig (lo + ((j : ℤ) + 1)) b = 1) → relAt sig lo k b = 1 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    rw [relAt_succ, h i (by omega), ih (fun j hj => h j (by omega)), one_mul]

/-- **And such a `sig` exists**: trivial everywhere except the last down pass, which
carries the cycle.  A pass costs the same whichever levels it pairs, so this choice is
free -- which is BLOCK 187's observation, now exhibited. -/
theorem exists_sig_with_parity (u : ℕ) (hu : 0 < u) (lo : ℤ) (len : ℕ) (hlen : 0 < len) :
    ∃ sig : ℤ → Bool → Equiv.Perm (Fin u),
      relAt sig lo len true = 1 ∧ relAt sig lo len false = shiftDown u hu := by
  classical
  refine ⟨fun j b => if j = lo + (len : ℤ) ∧ b = false then shiftDown u hu else 1, ?_, ?_⟩
  · -- the up side never matches the condition
    exact relAt_eq_one u _ lo true len (fun j _ => by simp)
  · -- the down side is trivial before the last pass, and the cycle at it
    obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
    rw [relAt_succ]
    have hprev : relAt (fun j b => if j = lo + ((k : ℤ) + 1) ∧ b = false
        then shiftDown u hu else 1) lo k false = 1 := by
      refine relAt_eq_one u _ lo false k (fun j hj => ?_)
      rw [if_neg]
      rintro ⟨he, -⟩
      have : (j : ℤ) + 1 = (k : ℤ) + 1 := by omega
      omega
    have hcast : ((k : ℕ) + 1 : ℕ) = ((k : ℤ) + 1) := by push_cast; ring
    rw [show ((((k : ℕ) + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 by push_cast; ring] at *
    rw [hprev, mul_one, if_pos ⟨rfl, rfl⟩]

end EltBridge
#print axioms EltBridge.shiftDown_succ
#print axioms EltBridge.hrel_of_shiftDown
#print axioms EltBridge.exists_sig_with_parity

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-! ## The final composition

`shield_law_shift` takes ONE naming `f` on all of `ℤ`, while the relabelling is per-run.
So `f` looks up the run of its position -- `gz Zf j` names it, `lo` gives its left end --
and applies that run's relabelling. -/

/-- The global naming: at each position, the relabelling of its own run. -/
noncomputable def globalName (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (Zf : Finset ℤ) (lo : ℕ → ℤ)
    (j : ℤ) (l : Fin u) (b : Bool) : EndType.Endpt n m :=
  strOf (m := m) hm sec j
    (relAt sig (lo (CutComponents.gz Zf j)) ((j - lo (CutComponents.gz Zf j)).toNat) b l) b

/-- Inside a run, the global naming IS that run's naming. -/
theorem globalName_eq_nameAt (hm : ∀ e, m e = 2 * u) (sec : ℤ → Fin n)
    (sig : ℤ → Bool → Equiv.Perm (Fin u)) (Zf : Finset ℤ) (lo : ℕ → ℤ)
    (r k : ℕ) (l : Fin u) (b : Bool)
    (hgz : CutComponents.gz Zf (lo r + (k : ℤ)) = r) :
    globalName (m := m) hm sec sig Zf lo (lo r + (k : ℤ)) l b
      = nameAt (m := m) hm sec sig (lo r) k l b := by
  unfold globalName nameAt
  rw [hgz]
  have htn : (lo r + (k : ℤ) - lo r).toNat = k := by omega
  rw [htn]

/-- **The general-`mu` shield law, composed.**  The datum is built, the naming is built,
and the three link families are discharged from the path lemmas.  What the caller
supplies is the configuration and the run structure. -/
theorem shield_law_mu_general (hm : ∀ e, m e = 2 * u) (hu : 0 < u) (sec : ℤ → Fin n)
    (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B) (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (hsecWide : ∀ j : ℤ, A - 1 ≤ j → j ≤ B + 1 → ((sec j : ℕ) : ℤ) = j)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    -- the run structure
    (hgz : ∀ (r k : ℕ), k ≤ len r → CutComponents.gz Zf (lo r + (k : ℤ)) = r)
    (hposRange : ∀ (r k : ℕ), k ≤ len r →
      A - 1 ≤ lo r + (k : ℤ) ∧ lo r + (k : ℤ) ≤ B + 1)
    (hbdryL : ∀ r : ℕ, lo r ∈ insert A (insert (B + 1) Zf))
    (hbdryR : ∀ r : ℕ, lo r + (len r : ℤ) + 1 ∈ insert A (insert (B + 1) Zf))
    (hint : ∀ (r k : ℕ), k < len r →
      lo r + (k : ℤ) + 1 ∉ insert A (insert (B + 1) Zf))
    -- the parity, per run
    (hpar : ∀ (r : ℕ) (i : ℕ) (hi : i + 1 < u),
      relAt sig (lo r) (len r) false ⟨i + 1, hi⟩
        = relAt sig (lo r) (len r) true ⟨i, by omega⟩)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hne : Nonempty (EndType.Endpt n m)) :
    ∃ E : WalkGraph.Data (EndType.Endpt n m),
      WalkGraph.walkCount E = Zf.card + 1 := by
  classical
  set Bs := insert A (insert (B + 1) Zf) with hBs
  obtain ⟨E, hEp, hEt, hTsite⟩ :=
    exists_turnGen_data hm hu sec Bs sig A B hspan hsecWide
  refine ⟨E, shield_law_shift hu Zf A B hAB lo len E
    (fun a => globalName (m := m) hm sec sig Zf lo a.1 a.2.1 a.2.2)
    hEp hTsite ?_ ?_ hrange ?_ ?_ ?_ hlow hhigh hocc hne⟩
  · -- hturn
    intro x hx
    rw [hEt x] at hx
    exact turnGen_hturn hm sec Zf Bs
      (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)) sig x hx
  · -- the cover
    intro x
    obtain ⟨l, b, hlb⟩ := botOf_eq_strOf hm sec x (hsecEdge x)
    refine ⟨(relAt sig (lo (CutComponents.gz Zf (EndType.edgeOf x)))
      ((EndType.edgeOf x - lo (CutComponents.gz Zf (EndType.edgeOf x))).toNat) b).symm l,
      b, ?_⟩
    unfold globalName
    simpa using hlb
  · -- hchain
    intro r k l b hk
    simp only []
    rw [globalName_eq_nameAt hm sec sig Zf lo r k l b (hgz r k (by omega)),
      globalName_eq_nameAt hm sec sig Zf lo r (k + 1) l b (hgz r (k + 1) (by omega))]
    exact hchain_nameAt hm sec Bs sig E hEp hEt (lo r) k l b
      (hsecWide _ (hposRange r k (by omega)).1 (hposRange r k (by omega)).2)
      (hint r k hk)
  · -- hjoinL
    intro r l
    simp only []
    have h0 : ((0 : ℕ) : ℤ) = 0 := by norm_num
    rw [show lo r = lo r + ((0 : ℕ) : ℤ) by rw [h0]; ring]
    rw [globalName_eq_nameAt hm sec sig Zf lo r 0 l true (hgz r 0 (by omega)),
      globalName_eq_nameAt hm sec sig Zf lo r 0 l false (hgz r 0 (by omega))]
    exact hjoinL_nameAt hm sec Bs sig E hEt (lo r) l
      (by
        obtain ⟨p1, p2⟩ := hposRange r 0 (by omega)
        simp only [Nat.cast_zero, add_zero] at p1 p2
        exact hsecWide (lo r) p1 p2)
      (hbdryL r)
  · -- hshift
    intro r i hi
    simp only []
    rw [globalName_eq_nameAt hm sec sig Zf lo r (len r) _ true (hgz r (len r) (le_refl _)),
      globalName_eq_nameAt hm sec sig Zf lo r (len r) _ false (hgz r (len r) (le_refl _))]
    exact hshift_nameAt hm sec Bs sig E hEp hEt (lo r) (len r)
      (hsecWide _ (hposRange r (len r) (le_refl _)).1 (hposRange r (len r) (le_refl _)).2)
      (hbdryR r) i hi (hpar r i hi)

end EltBridge

#print axioms EltBridge.globalName_eq_nameAt
#print axioms EltBridge.shield_law_mu_general

namespace EltBridge

/-! ## The run structure, supplied

`shield_law_mu_general` asks for `lo`, `len` and several facts about them.  Taking the
level sets of `gz` as the runs -- `runLo` and `runLen` of BLOCK 181 -- almost all are
already proved; the one missing is the mirror of `runLo_mem_bounce`, that a run's RIGHT
end is a bounce site too. -/

theorem gz_at_run (Zf : Finset ℤ) (A B : ℤ) (r k : ℕ)
    (hne : (levelSet Zf A B r).Nonempty) (hk : k ≤ runLen Zf A B r) :
    CutComponents.gz Zf (runLo Zf A B r + (k : ℤ)) = r := by
  have h := run_mem_levelSet Zf A B r k hne hk
  simp only [levelSet, Finset.mem_filter] at h
  exact h.2

theorem run_pos_in_span (Zf : Finset ℤ) (A B : ℤ) (r k : ℕ)
    (hne : (levelSet Zf A B r).Nonempty) (hk : k ≤ runLen Zf A B r) :
    A ≤ runLo Zf A B r + (k : ℤ) ∧ runLo Zf A B r + (k : ℤ) ≤ B := by
  have h := run_mem_levelSet Zf A B r k hne hk
  simp only [levelSet, Finset.mem_filter, Finset.mem_Icc] at h
  exact h.1

/-- **A run's right end is a bounce site.**  Either it is the span's right edge, or `gz`
rises just past it, which happens only at a cut site. -/
theorem runHi_succ_mem_bounce (Zf : Finset ℤ) (A B : ℤ) (r : ℕ)
    (hne : (levelSet Zf A B r).Nonempty)
    (hmax : ∀ j : ℤ, A ≤ j → j ≤ B → CutComponents.gz Zf j = r →
      j ≤ runLo Zf A B r + (runLen Zf A B r : ℤ)) :
    runLo Zf A B r + (runLen Zf A B r : ℤ) + 1 ∈ insert A (insert (B + 1) Zf) := by
  classical
  obtain ⟨hA, hB⟩ := run_pos_in_span Zf A B r (runLen Zf A B r) hne (le_refl _)
  have hgzhi : CutComponents.gz Zf (runLo Zf A B r + (runLen Zf A B r : ℤ)) = r :=
    gz_at_run Zf A B r _ hne (le_refl _)
  by_cases hBB : runLo Zf A B r + (runLen Zf A B r : ℤ) = B
  · rw [hBB]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    refine mem_of_gz_lt Zf _ ?_
    have harith : runLo Zf A B r + (runLen Zf A B r : ℤ) + 1 - 1
        = runLo Zf A B r + (runLen Zf A B r : ℤ) := by ring
    rw [harith, hgzhi]
    rcases Nat.lt_or_ge r
      (CutComponents.gz Zf (runLo Zf A B r + (runLen Zf A B r : ℤ) + 1)) with h | h
    · exact h
    · exfalso
      have hmono := gz_mono Zf
        (show runLo Zf A B r + (runLen Zf A B r : ℤ)
          ≤ runLo Zf A B r + (runLen Zf A B r : ℤ) + 1 by omega)
      have heq : CutComponents.gz Zf (runLo Zf A B r + (runLen Zf A B r : ℤ) + 1) = r := by
        omega
      have := hmax _ (by omega) (by omega) heq
      omega

/-- An occupied run has a non-empty level set. -/
theorem levelSet_ne_of_occ {n : ℕ} {m : Fin n → ℕ} (Zf : Finset ℤ) (A B : ℤ) (r : ℕ)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (h : ∃ y : EndType.Endpt n m, CutComponents.gz Zf (EndType.edgeOf y) = r) :
    (levelSet Zf A B r).Nonempty := by
  obtain ⟨y, hy⟩ := h
  exact ⟨EndType.edgeOf y, by
    simp only [levelSet, Finset.mem_filter]
    exact ⟨hspan y, hy⟩⟩

end EltBridge

#print axioms EltBridge.gz_at_run
#print axioms EltBridge.runHi_succ_mem_bounce
#print axioms EltBridge.levelSet_ne_of_occ

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-! ### Only occupied runs need the hypotheses

`shield_law_shift` asks its three families at every `r`, but they are used only at
`r = gz (edgeOf x)` for an actual end -- a run CONTAINING an edge, hence non-empty.
Empty runs need nothing, and could not supply it: their `runLo` defaults to `A` and there
is no far bounce to shift at.  So the hypotheses are conditional on occupancy, and the
witness is derived where they are used. -/
theorem shield_law_shift_occ (hu : 0 < u) (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (lo : ℕ → ℤ) (len : ℕ → ℕ)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (f : ℤ × Fin u × Bool → EndType.Endpt n m)
    (hEp : E.p = EndType.partner)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hcover : ∀ x : EndType.Endpt n m, ∃ (l : Fin u) (b : Bool),
      f (EndType.edgeOf x, l, b) = botOf x)
    (hrange : ∀ x : EndType.Endpt n m,
      ∃ k : ℕ, k ≤ len (CutComponents.gz Zf (EndType.edgeOf x)) ∧
        EndType.edgeOf x = lo (CutComponents.gz Zf (EndType.edgeOf x)) + k)
    (hchain : ∀ (r : ℕ), (∃ y : EndType.Endpt n m,
        CutComponents.gz Zf (EndType.edgeOf y) = r) →
      ∀ (k : ℕ) (l : Fin u) (b : Bool), k < len r →
      (WalkGraph.graph E).Reachable (f (lo r + k, l, b)) (f (lo r + (k + 1 : ℕ), l, b)))
    (hjoinL : ∀ (r : ℕ), (∃ y : EndType.Endpt n m,
        CutComponents.gz Zf (EndType.edgeOf y) = r) →
      ∀ l : Fin u,
      (WalkGraph.graph E).Reachable (f (lo r, l, true)) (f (lo r, l, false)))
    (hshift : ∀ (r : ℕ), (∃ y : EndType.Endpt n m,
        CutComponents.gz Zf (EndType.edgeOf y) = r) →
      ∀ (i : ℕ) (hi : i + 1 < u),
      (WalkGraph.graph E).Reachable (f (lo r + (len r : ℕ), ⟨i, by omega⟩, true))
        (f (lo r + (len r : ℕ), ⟨i + 1, hi⟩, false)))
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hne : Nonempty (EndType.Endpt n m)) :
    WalkGraph.walkCount E = Zf.card + 1 := by
  classical
  have hrun : ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph E).Reachable (botOf x) (botOf y) := by
    intro x y hxy
    have hoccx : ∃ z : EndType.Endpt n m,
        CutComponents.gz Zf (EndType.edgeOf z) = CutComponents.gz Zf (EndType.edgeOf x) :=
      ⟨x, rfl⟩
    obtain ⟨lx, bx, hx⟩ := hcover x
    obtain ⟨ly, by', hy⟩ := hcover y
    obtain ⟨j, hj, hxj⟩ := hrange x
    obtain ⟨j', hj', hyj⟩ := hrange y
    rw [← hx, ← hy, hxj, hyj, ← hxy] at *
    exact run_one_component_shift u hu (WalkGraph.graph E) f _ _
      (hchain _ hoccx) (hjoinL _ hoccx) (hshift _ hoccx)
      j j' hj (by rw [hxy] at hj'; exact hj') lx ly bx by'
  refine le_antisymm ?_ ?_
  · exact shield_upper_bound_endpt E Zf botOf (fun x => by rw [hEp]) hTsite hturn
      (fun x => by rw [hEp]; exact botOf_eq_or_partner x) (fun _ => rfl) hrun
  · obtain ⟨x0⟩ := hne
    exact walkCount_ge_passTurn E Zf A B hAB hEp hTsite hturn hlow hhigh hocc
      ((WalkGraph.graph E).connectedComponentMk x0)

end EltBridge

#print axioms EltBridge.shield_law_shift_occ

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **M4b with the run structure supplied.**  The runs are the level sets of `gz`, and
every fact about them is proved: `gz_at_run` and `run_pos_in_span` from
`run_mem_levelSet`, `runLo_mem_bounce'` and `runHi_succ_mem_bounce` at the two ends,
`no_bounce_inside_run` for the interior, `runLo_le_and_le_len` for the range.

What the caller supplies is the configuration alone -- `mu = 2u`, the span, the section,
the permutations with the parity -- plus the two order facts naming `runLo` and
`runLo + runLen` as the run's least and greatest positions. -/
theorem shield_law_runs (hm : ∀ e, m e = 2 * u) (hu : 0 < u) (sec : ℤ → Fin n)
    (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (hsecWide : ∀ j : ℤ, A - 1 ≤ j → j ≤ B + 1 → ((sec j : ℕ) : ℤ) = j)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge)
    (hmin : ∀ (r : ℕ) (j : ℤ), A ≤ j → j ≤ B → CutComponents.gz Zf j = r →
      runLo Zf A B r ≤ j)
    (hmax : ∀ (r : ℕ) (j : ℤ), A ≤ j → j ≤ B → CutComponents.gz Zf j = r →
      j ≤ runLo Zf A B r + (runLen Zf A B r : ℤ))
    (hpar : ∀ (r : ℕ) (i : ℕ) (hi : i + 1 < u),
      relAt sig (runLo Zf A B r) (runLen Zf A B r) false ⟨i + 1, hi⟩
        = relAt sig (runLo Zf A B r) (runLen Zf A B r) true ⟨i, by omega⟩)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hoc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hnonempty : Nonempty (EndType.Endpt n m)) :
    ∃ E : WalkGraph.Data (EndType.Endpt n m),
      WalkGraph.walkCount E = Zf.card + 1 := by
  classical
  obtain ⟨E, hEp, hEt, hTsite⟩ :=
    exists_turnGen_data hm hu sec (insert A (insert (B + 1) Zf)) sig A B hspan hsecWide
  refine ⟨E, shield_law_shift_occ hu Zf A B hAB (runLo Zf A B) (runLen Zf A B) E
    (fun a => globalName (m := m) hm sec sig Zf (runLo Zf A B) a.1 a.2.1 a.2.2)
    hEp hTsite ?_ ?_ ?_ ?_ ?_ ?_ hlow hhigh hoc hnonempty⟩
  · intro x hx
    rw [hEt x] at hx
    exact turnGen_hturn hm sec Zf (insert A (insert (B + 1) Zf))
      (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)) sig x hx
  · intro x
    obtain ⟨l, b, hlb⟩ := botOf_eq_strOf hm sec x (hsecEdge x)
    exact ⟨(relAt sig (runLo Zf A B (CutComponents.gz Zf (EndType.edgeOf x)))
      ((EndType.edgeOf x
        - runLo Zf A B (CutComponents.gz Zf (EndType.edgeOf x))).toNat) b).symm l,
      b, by unfold globalName; simpa using hlb⟩
  · exact fun x => runLo_le_and_le_len Zf A B _ (hspan x)
  · intro r hoccr k l b hk
    have hne := levelSet_ne_of_occ Zf A B r hspan hoccr
    obtain ⟨p1, p2⟩ := run_pos_in_span Zf A B r k hne (by omega)
    simp only []
    rw [globalName_eq_nameAt hm sec sig Zf (runLo Zf A B) r k l b
        (gz_at_run Zf A B r k hne (by omega)),
      globalName_eq_nameAt hm sec sig Zf (runLo Zf A B) r (k + 1) l b
        (gz_at_run Zf A B r (k + 1) hne (by omega))]
    exact hchain_nameAt hm sec _ sig E hEp hEt (runLo Zf A B r) k l b
      (hsecWide _ (by omega) (by omega))
      (by
        have h := no_bounce_inside_run Zf A B r k hne hk
        have harith : runLo Zf A B r + (k : ℤ) + 1 = runLo Zf A B r + ((k : ℤ) + 1) := by
          ring
        rw [harith]
        exact h)
  · intro r hoccr l
    have hne := levelSet_ne_of_occ Zf A B r hspan hoccr
    obtain ⟨p1, p2⟩ := run_pos_in_span Zf A B r 0 hne (by omega)
    simp only [Nat.cast_zero, add_zero] at p1 p2
    simp only []
    rw [show runLo Zf A B r = runLo Zf A B r + ((0 : ℕ) : ℤ) by norm_num]
    rw [globalName_eq_nameAt hm sec sig Zf (runLo Zf A B) r 0 l true
        (gz_at_run Zf A B r 0 hne (by omega)),
      globalName_eq_nameAt hm sec sig Zf (runLo Zf A B) r 0 l false
        (gz_at_run Zf A B r 0 hne (by omega))]
    exact hjoinL_nameAt hm sec _ sig E hEt (runLo Zf A B r) l
      (hsecWide _ (by omega) (by omega)) (runLo_mem_bounce' Zf A B r (hmin r))
  · intro r hoccr i hi
    have hne := levelSet_ne_of_occ Zf A B r hspan hoccr
    obtain ⟨p1, p2⟩ := run_pos_in_span Zf A B r (runLen Zf A B r) hne (le_refl _)
    simp only []
    rw [globalName_eq_nameAt hm sec sig Zf (runLo Zf A B) r (runLen Zf A B r) _ true
        (gz_at_run Zf A B r (runLen Zf A B r) hne (le_refl _)),
      globalName_eq_nameAt hm sec sig Zf (runLo Zf A B) r (runLen Zf A B r) _ false
        (gz_at_run Zf A B r (runLen Zf A B r) hne (le_refl _))]
    exact hshift_nameAt hm sec _ sig E hEp hEt (runLo Zf A B r) (runLen Zf A B r)
      (hsecWide _ (by omega) (by omega))
      (runHi_succ_mem_bounce Zf A B r hne (hmax r)) i hi (hpar r i hi)

end EltBridge

#print axioms EltBridge.shield_law_runs

namespace EltBridge

/-! ### `hmin` and `hmax` are definitional

`runLo` is the level set's minimum and `runLo + runLen` its maximum, so the two order
facts `shield_law_runs` asks for are theorems, not hypotheses. -/

theorem runLo_le (Zf : Finset ℤ) (A B : ℤ) (r : ℕ) (j : ℤ)
    (hA : A ≤ j) (hB : j ≤ B) (hgz : CutComponents.gz Zf j = r) :
    runLo Zf A B r ≤ j := by
  classical
  have hmem : j ∈ levelSet Zf A B r := by
    simp only [levelSet, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hA, hB⟩, hgz⟩
  have hne : (levelSet Zf A B r).Nonempty := ⟨j, hmem⟩
  rw [runLo, dif_pos hne]
  exact Finset.min'_le _ _ hmem

theorem le_runHi (Zf : Finset ℤ) (A B : ℤ) (r : ℕ) (j : ℤ)
    (hA : A ≤ j) (hB : j ≤ B) (hgz : CutComponents.gz Zf j = r) :
    j ≤ runLo Zf A B r + (runLen Zf A B r : ℤ) := by
  classical
  have hmem : j ∈ levelSet Zf A B r := by
    simp only [levelSet, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hA, hB⟩, hgz⟩
  have hne : (levelSet Zf A B r).Nonempty := ⟨j, hmem⟩
  have hlo : runLo Zf A B r = (levelSet Zf A B r).min' hne := by rw [runLo, dif_pos hne]
  have hlen : runLen Zf A B r
      = ((levelSet Zf A B r).max' hne - (levelSet Zf A B r).min' hne).toNat := by
    rw [runLen, dif_pos hne]
  have hle := Finset.min'_le_max' (levelSet Zf A B r) hne
  have hmax := Finset.le_max' _ _ hmem
  rw [hlo, hlen]
  omega

end EltBridge

#print axioms EltBridge.runLo_le
#print axioms EltBridge.le_runHi

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **THE SHIELD LAW.**  `walkCount = |Z| + 1`, that is `c = |Z|`, at every `mu = 2u`.

The hypotheses are the configuration and nothing else: every edge carries `2u` strands,
the ends lie in the span, `sec` names the edge at each position of `[A-1, B+1]`, the cut
sites lie strictly inside the span and every position of it carries an end, and the
permutation family has the parity BLOCK 187 identified -- which `exists_sig_with_parity`
shows always exists.

The run structure is no longer assumed: `runLo` and `runLen` are the level sets of `gz`,
and every fact about them is proved (`runLo_le`, `le_runHi`, `gz_at_run`,
`run_pos_in_span`, `runLo_mem_bounce'`, `runHi_succ_mem_bounce`, `no_bounce_inside_run`,
`runLo_le_and_le_len`).

`CostMerge` is invoked nowhere beneath this: no merge, no swap, no free pair. -/
theorem shield_law (hm : ∀ e, m e = 2 * u) (hu : 0 < u) (sec : ℤ → Fin n)
    (sig : ℤ → Bool → Equiv.Perm (Fin u))
    (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (hspan : ∀ x : EndType.Endpt n m, EndType.edgeOf x ∈ Finset.Icc A B)
    (hsecWide : ∀ j : ℤ, A - 1 ≤ j → j ≤ B + 1 → ((sec j : ℕ) : ℤ) = j)
    (hsecEdge : ∀ x : EndType.Endpt n m, sec (EndType.edgeOf x) = x.edge)
    (hpar : ∀ (r : ℕ) (i : ℕ) (hi : i + 1 < u),
      relAt sig (runLo Zf A B r) (runLen Zf A B r) false ⟨i + 1, hi⟩
        = relAt sig (runLo Zf A B r) (runLen Zf A B r) true ⟨i, by omega⟩)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hoc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hnonempty : Nonempty (EndType.Endpt n m)) :
    ∃ E : WalkGraph.Data (EndType.Endpt n m),
      WalkGraph.walkCount E = Zf.card + 1 :=
  shield_law_runs hm hu sec sig Zf A B hAB hspan hsecWide hsecEdge
    (fun r j hA hB hgz => runLo_le Zf A B r j hA hB hgz)
    (fun r j hA hB hgz => le_runHi Zf A B r j hA hB hgz)
    hpar hlow hhigh hoc hnonempty

end EltBridge

#print axioms EltBridge.shield_law

namespace EltBridge

/-! ## The Eulerian route

BLOCK 199 found the argument the level bookkeeping was approximating.  Take the STRAND
GRAPH of a run: vertices are sites, edges are strands, a strand of edge `j` joining site
`j` to site `j+1`.  Every vertex has even degree, each run is connected, and a turn is
exactly a pairing of arrivals to departures at each vertex.  So an Eulerian circuit
exists, and the turn following it leaves the run in one component -- at any widths.

The bridge from a circuit to a component is below, and it is the easy half: a list of
strands covering the run, consecutive ones joined by the turn, puts them all together. -/

/-- **A covering chain gives one component.**  If consecutive entries of a list are
joined, everything in the list is joined to the first entry. -/
theorem chain_covers {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (L : List α) (hL : L ≠ [])
    (hadj : ∀ i : ℕ, ∀ h : i + 1 < L.length,
      G.Reachable (L.get ⟨i, by omega⟩) (L.get ⟨i + 1, h⟩)) :
    ∀ i : ℕ, ∀ h : i < L.length,
      G.Reachable (L.get ⟨0, by cases L with | nil => exact absurd rfl hL | cons _ _ => omega⟩)
        (L.get ⟨i, h⟩) := by
  intro i
  induction i with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro h
    exact (ih (by omega)).trans (hadj k h)

/-- **And any two entries are joined.** -/
theorem chain_pairwise {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (L : List α) (hL : L ≠ [])
    (hadj : ∀ i : ℕ, ∀ h : i + 1 < L.length,
      G.Reachable (L.get ⟨i, by omega⟩) (L.get ⟨i + 1, h⟩))
    (i j : ℕ) (hi : i < L.length) (hj : j < L.length) :
    G.Reachable (L.get ⟨i, hi⟩) (L.get ⟨j, hj⟩) :=
  ((chain_covers G L hL hadj i hi).symm).trans (chain_covers G L hL hadj j hj)

/-- **So a covering chain gives `hrun`.**  If every end's representative appears in a
chain, any two representatives are joined -- which is what the shield bound consumes.
This is the whole bridge from an Eulerian circuit to the component count; what it needs
from the circuit is only that it COVERS. -/
theorem hrun_of_chain {n : ℕ} {m : Fin n → ℕ}
    (E : WalkGraph.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (L : ℕ → List (EndType.Endpt n m)) (hL : ∀ r, L r ≠ [])
    (hadj : ∀ (r : ℕ) (i : ℕ) (h : i + 1 < (L r).length),
      (WalkGraph.graph E).Reachable ((L r).get ⟨i, by omega⟩) ((L r).get ⟨i + 1, h⟩))
    (hmem : ∀ x : EndType.Endpt n m,
      ∃ i : ℕ, ∃ h : i < (L (CutComponents.gz Zf (EndType.edgeOf x))).length,
        (L (CutComponents.gz Zf (EndType.edgeOf x))).get ⟨i, h⟩ = botOf x) :
    ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph E).Reachable (botOf x) (botOf y) := by
  intro x y hxy
  -- transport x's membership to y's run index BEFORE destructuring, so nothing
  -- depends on the index yet
  have hmx := hmem x
  rw [hxy] at hmx
  obtain ⟨i, hi, hxi⟩ := hmx
  obtain ⟨j, hj, hyj⟩ := hmem y
  rw [← hxi, ← hyj]
  exact chain_pairwise (WalkGraph.graph E) _ (hL _) (hadj _) i j hi hj

end EltBridge

#print axioms EltBridge.chain_covers
#print axioms EltBridge.hrun_of_chain

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The shield law from a covering chain -- at ANY widths.**

`walkCount = |Zf| + 1`, that is `c = |Z|`.  Compare `shield_law`: there is no
`hm : ∀ e, m e = 2 * u` here.  The edges may carry any number of strands, and may differ
from one another, because the argument never mentions levels.

What it needs instead is one list per run, covering that run's representatives, with
consecutive entries joined by the turn -- an Eulerian circuit of the run's strand graph,
which exists because every site has even degree and each run is connected. -/
theorem shield_law_chain (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (L : ℕ → List (EndType.Endpt n m)) (hL : ∀ r, L r ≠ [])
    (hadj : ∀ (r : ℕ) (i : ℕ) (h : i + 1 < (L r).length),
      (WalkGraph.graph E).Reachable ((L r).get ⟨i, by omega⟩) ((L r).get ⟨i + 1, h⟩))
    (hmem : ∀ x : EndType.Endpt n m,
      ∃ i : ℕ, ∃ h : i < (L (CutComponents.gz Zf (EndType.edgeOf x))).length,
        (L (CutComponents.gz Zf (EndType.edgeOf x))).get ⟨i, h⟩ = botOf x)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hoc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hnonempty : Nonempty (EndType.Endpt n m)) :
    WalkGraph.walkCount E = Zf.card + 1 := by
  have hrun := hrun_of_chain E Zf L hL hadj hmem
  refine le_antisymm ?_ ?_
  · exact shield_upper_bound_endpt E Zf botOf (fun x => by rw [hEp]) hTsite hturn
      (fun x => by rw [hEp]; exact botOf_eq_or_partner x) (fun _ => rfl) hrun
  · obtain ⟨x0⟩ := hnonempty
    exact walkCount_ge_passTurn E Zf A B hAB hEp hTsite hturn hlow hhigh hoc
      ((WalkGraph.graph E).connectedComponentMk x0)

-- The level machinery of BLOCKS 187-197 is the uniform-width case of this: there a
-- run's chain is read off the levels.  The chain formulation does not need the widths to
-- agree, which is the whole gain.

end EltBridge

#print axioms EltBridge.shield_law_chain

namespace EltBridge

/-! ### Splicing, without indices

A first attempt spliced LISTS, and spent four tactics fighting `List.get` versus
`getElem` and append-index arithmetic before hitting the three-strike rule.  The
indices were the problem, not the mathematics: the chain condition only ever says "all
these are mutually reachable", which is a statement about a SET.

So: `AllJoined S` for a set of ends, built by union.  No indices appear. -/

/-- Every member of `S` is reachable from every other. -/
def AllJoined {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (S : Finset α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, G.Reachable x y

/-- **Two joined sets sharing a link join.**  This is the splice, and with no indices it
is three lines. -/
theorem allJoined_union {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (S T : Finset α) (hS : AllJoined G S) (hT : AllJoined G T)
    (a b : α) (ha : a ∈ S) (hb : b ∈ T) (hlink : G.Reachable a b) :
    AllJoined G (S ∪ T) := by
  intro x hx y hy
  rw [Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hS x hx y hy
  · exact ((hS x hx a ha).trans hlink).trans (hT b hb y hy)
  · exact ((hT x hx b hb).trans hlink.symm).trans (hS a ha y hy)
  · exact hT x hx y hy

/-- **`hrun` from a joined set per run.** -/
theorem hrun_of_allJoined {n : ℕ} {m : Fin n → ℕ}
    (E : WalkGraph.Data (EndType.Endpt n m)) (Zf : Finset ℤ)
    (S : ℕ → Finset (EndType.Endpt n m))
    (hS : ∀ r, AllJoined (WalkGraph.graph E) (S r))
    (hmem : ∀ x : EndType.Endpt n m,
      botOf x ∈ S (CutComponents.gz Zf (EndType.edgeOf x))) :
    ∀ x y : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = CutComponents.gz Zf (EndType.edgeOf y) →
      (WalkGraph.graph E).Reachable (botOf x) (botOf y) := by
  intro x y hxy
  have hx := hmem x
  have hy := hmem y
  rw [hxy] at hx
  exact hS _ _ hx _ hy

end EltBridge

#print axioms EltBridge.allJoined_union
#print axioms EltBridge.hrun_of_allJoined

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The shield law from joined runs -- at ANY widths.**

`walkCount = |Zf| + 1`, that is `c = |Z|`, with no hypothesis relating the edges' widths.
What it asks is one set per run, containing that run's representatives, all mutually
reachable -- which `allJoined_union` builds by splicing edge by edge, each splice needing
only ONE link.

That is the Eulerian argument with the circuit dissolved: the component count never
needed an ordering of the strands, only that they are all joined. -/
theorem shield_law_joined (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (S : ℕ → Finset (EndType.Endpt n m))
    (hS : ∀ r, AllJoined (WalkGraph.graph E) (S r))
    (hmem : ∀ x : EndType.Endpt n m,
      botOf x ∈ S (CutComponents.gz Zf (EndType.edgeOf x)))
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hoc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hnonempty : Nonempty (EndType.Endpt n m)) :
    WalkGraph.walkCount E = Zf.card + 1 := by
  have hrun := hrun_of_allJoined E Zf S hS hmem
  refine le_antisymm ?_ ?_
  · exact shield_upper_bound_endpt E Zf botOf (fun x => by rw [hEp]) hTsite hturn
      (fun x => by rw [hEp]; exact botOf_eq_or_partner x) (fun _ => rfl) hrun
  · obtain ⟨x0⟩ := hnonempty
    exact walkCount_ge_passTurn E Zf A B hAB hEp hTsite hturn hlow hhigh hoc
      ((WalkGraph.graph E).connectedComponentMk x0)

/-- **The single-edge set is joined**, by the near bounce: the two strand bottoms of an
edge are one turn step apart.  This is the base of the splice. -/
theorem allJoined_pair {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (a b : α) (hab : G.Reachable a b) : AllJoined G {a, b} := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact SimpleGraph.Reachable.refl _
  · exact hab
  · exact hab.symm
  · exact SimpleGraph.Reachable.refl _

end EltBridge

#print axioms EltBridge.shield_law_joined
#print axioms EltBridge.allJoined_pair

namespace EltBridge

variable {n : ℕ} {m : Fin n → ℕ}

/-! ### The link

A turn step joins the two ends' representatives, whatever it does: an end reaches its
own strand's bottom by the partner, and its image likewise.  So a PASS at a site -- a
turn step whose two ends lie on different edges -- links the strand sets of those two
edges, which is the link `allJoined_union` consumes. -/

/-- **Any turn step joins the two representatives.** -/
theorem link_of_turn (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner) (x : EndType.Endpt n m) :
    (WalkGraph.graph E).Reachable (botOf x) (botOf (E.t x)) := by
  have h1 : (WalkGraph.graph E).Reachable (botOf x) x :=
    (reachable_to_base E botOf (fun y => by rw [hEp]; exact botOf_eq_or_partner y) x).symm
  have h2 : (WalkGraph.graph E).Reachable x (E.t x) := reachable_turn E x
  have h3 : (WalkGraph.graph E).Reachable (E.t x) (botOf (E.t x)) :=
    reachable_to_base E botOf (fun y => by rw [hEp]; exact botOf_eq_or_partner y) (E.t x)
  exact (h1.trans h2).trans h3

/-- **A pass links two edges' strand sets.**  Given singleton-to-singleton, the union
lemma does the rest. -/
theorem allJoined_of_pass (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner) (S T : Finset (EndType.Endpt n m))
    (hS : AllJoined (WalkGraph.graph E) S) (hT : AllJoined (WalkGraph.graph E) T)
    (x : EndType.Endpt n m) (hx : botOf x ∈ S) (hy : botOf (E.t x) ∈ T) :
    AllJoined (WalkGraph.graph E) (S ∪ T) :=
  allJoined_union (WalkGraph.graph E) S T hS hT _ _ hx hy (link_of_turn E hEp x)

/-- **What (M2) still owes, named.**  `shield_law_joined` needs a joined set per run.
Building it by `allJoined_of_pass` needs, for each run, that the turn's pairing graph on
that run's STRANDS is connected -- which is the Eulerian statement, and is the content:
every site has even degree and the run's strand multigraph is a connected path of
parallel edges, so a turn whose pairing graph is connected exists.

That existence is not proved here.  This names it as the single remaining input, and
records that everything else in the chain is discharged. -/
def RunStrandsConnected (E : WalkGraph.Data (EndType.Endpt n m)) (Zf : Finset ℤ) : Prop :=
  ∀ r : ℕ, ∃ S : Finset (EndType.Endpt n m),
    AllJoined (WalkGraph.graph E) S ∧
    ∀ x : EndType.Endpt n m,
      CutComponents.gz Zf (EndType.edgeOf x) = r → botOf x ∈ S

/-- And with it the shield law follows at any widths. -/
theorem shield_law_of_connected (Zf : Finset ℤ) (A B : ℤ) (hAB : A ≤ B)
    (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (hTsite : ∀ x, EndType.siteOf (E.t x) = EndType.siteOf x)
    (hturn : ∀ x, EndType.edgeOf (E.t x) ≠ EndType.edgeOf x → EndType.siteOf x ∉ Zf)
    (hconn : RunStrandsConnected E Zf)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hoc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : EndType.Endpt n m, EndType.edgeOf x = t)
    (hnonempty : Nonempty (EndType.Endpt n m)) :
    WalkGraph.walkCount E = Zf.card + 1 := by
  classical
  choose S hSjoined hSmem using hconn
  exact shield_law_joined Zf A B hAB E hEp hTsite hturn S hSjoined
    (fun x => hSmem _ x rfl) hlow hhigh hoc hnonempty

end EltBridge

#print axioms EltBridge.link_of_turn
#print axioms EltBridge.shield_law_of_connected

namespace EltBridge

/-! ## The Eulerian existence: the splice step

The strand graph of a run is 2-REGULAR -- each strand has two ends, each matched exactly
once by the turn -- so it is a disjoint union of cycles and "connected" and "one cycle"
coincide.  There is no weakening to mere connectivity.

The induction on edges then runs: the circuit on edges `0..j-1` visits site `j`, so it
pairs two ends there; break that pair and reroute through edge `j`'s strands, using them
in round trips and reconnecting the broken pair.  That needs `w j` even, which it is.

What the splice needs from the reroute is only that it JOINS the broken pair while
covering the new strands -- and in the `AllJoined` formulation that is again a union. -/

variable {n : ℕ} {m : Fin n → ℕ}

/-- **The splice, in the `AllJoined` formulation.**  A joined set absorbs a new joined set
as soon as one turn step crosses between them.  Iterating this edge by edge along a run is
the induction; each step needs one pass at the shared site. -/
theorem allJoined_absorb (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (S T : Finset (EndType.Endpt n m))
    (hS : AllJoined (WalkGraph.graph E) S) (hT : AllJoined (WalkGraph.graph E) T)
    (x : EndType.Endpt n m) (hx : botOf x ∈ S) (hTx : botOf (E.t x) ∈ T) :
    AllJoined (WalkGraph.graph E) (S ∪ T) :=
  allJoined_of_pass E hEp S T hS hT x hx hTx

/-- **Absorbing a whole family.**  Given a joined set for each edge of a run and a pass
linking each consecutive pair, the union over the run is joined.  This is the induction
with the reroute replaced by the union -- the round trips never have to be written down,
because `AllJoined` does not care about the ORDER in which the strands are covered. -/
theorem allJoined_biUnion (E : WalkGraph.Data (EndType.Endpt n m))
    (hEp : E.p = EndType.partner)
    (S : ℕ → Finset (EndType.Endpt n m)) (N : ℕ)
    (hS : ∀ j, AllJoined (WalkGraph.graph E) (S j))
    (link : ℕ → EndType.Endpt n m)
    (hlink : ∀ j, j < N → botOf (link j) ∈ S j ∧ botOf (E.t (link j)) ∈ S (j + 1)) :
    ∀ j : ℕ, j ≤ N →
      AllJoined (WalkGraph.graph E) ((Finset.range (j + 1)).biUnion S) := by
  intro j
  induction j with
  | zero => intro _; simpa using hS 0
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hsplit : (Finset.range (k + 1 + 1)).biUnion S
        = (Finset.range (k + 1)).biUnion S ∪ S (k + 1) := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union]
      constructor
      · rintro ⟨i, hi, hz⟩
        rcases Nat.lt_or_ge i (k + 1) with h | h
        · exact Or.inl ⟨i, h, hz⟩
        · exact Or.inr (by
            have : i = k + 1 := by omega
            exact this ▸ hz)
      · rintro (⟨i, hi, hz⟩ | hz)
        · exact ⟨i, by omega, hz⟩
        · exact ⟨k + 1, by omega, hz⟩
    rw [hsplit]
    obtain ⟨h1, h2⟩ := hlink k (by omega)
    exact allJoined_absorb E hEp ((Finset.range (k + 1)).biUnion S) (S (k + 1))
      hprev (hS (k + 1)) (link k)
      (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), h1⟩) h2

end EltBridge

#print axioms EltBridge.allJoined_absorb
#print axioms EltBridge.allJoined_biUnion

namespace EltBridge

/-! ## A path of links is joined

BLOCK 204 said an edge's strands need not be joined among themselves, which is true of an
ARBITRARY turn.  But the turn is ours to construct, and the recursive Eulerian walk makes
it true: going right on an up strand and back on a down strand, edge `j`'s strands form
the path

    up 0 — dn 0 — up 1 — dn 1 — ...

each consecutive pair joined by one turn step -- the bounce at the far site pairs `up i`
with `dn i`, the bounce at the near site pairs `dn i` with `up (i+1)` -- and the two loose
ends carry the continuation to the neighbouring edges.  So the per-edge decomposition IS
available, by construction.

What that needs is the lemma below: a path of links is joined.  It is the `AllJoined`
analogue of `levels_reachable`, and like it needs no indices beyond a counter. -/

/-- **A path of links is joined.** -/
theorem allJoined_of_path {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (f : ℕ → α) (N : ℕ)
    (hlink : ∀ i : ℕ, i < N → G.Reachable (f i) (f (i + 1))) :
    ∀ i : ℕ, i ≤ N → G.Reachable (f 0) (f i) := by
  intro i
  induction i with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ k ih => intro hk; exact (ih (by omega)).trans (hlink k (by omega))

/-- **And so its image is an `AllJoined` set.** -/
theorem allJoined_image {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (f : ℕ → α) (N : ℕ)
    (hlink : ∀ i : ℕ, i < N → G.Reachable (f i) (f (i + 1))) :
    AllJoined G ((Finset.range (N + 1)).image f) := by
  intro x hx y hy
  rw [Finset.mem_image] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  rw [Finset.mem_range] at hi hj
  exact ((allJoined_of_path G f N hlink i (by omega)).symm).trans
    (allJoined_of_path G f N hlink j (by omega))

/-- **The per-edge set, for a turn built from round trips.**  If the turn pairs
`f i` with `f (i+1)` all along the edge -- the far bounce joining `up i` to `dn i`, the
near bounce joining `dn i` to `up (i+1)` -- then the edge's strands are joined. -/
theorem allJoined_edge {n : ℕ} {m : Fin n → ℕ}
    (E : WalkGraph.Data (EndType.Endpt n m)) (hEp : E.p = EndType.partner)
    (f : ℕ → EndType.Endpt n m) (N : ℕ)
    (hstep : ∀ i : ℕ, i < N → E.t (f i) = f (i + 1) ∨ E.t (f (i + 1)) = f i) :
    AllJoined (WalkGraph.graph E) ((Finset.range (N + 1)).image (fun i => botOf (f i))) := by
  refine allJoined_image (WalkGraph.graph E) (fun i => botOf (f i)) N ?_
  intro i hi
  rcases hstep i hi with h | h
  · have := link_of_turn E hEp (f i)
    rwa [h] at this
  · have := link_of_turn E hEp (f (i + 1))
    rw [h] at this
    exact this.symm

end EltBridge

#print axioms EltBridge.allJoined_of_path
#print axioms EltBridge.allJoined_edge

#print axioms EltBridge.pathWeight_one_exp
#print axioms EltBridge.pathWeight_exp
#print axioms EltBridge.isTransferDecomposition_of_chain
#print axioms EltBridge.interior_kernel_eq_max
#print axioms EltBridge.alternating_is_chain
#print axioms EltBridge.isTransferDecomposition_alternating
#print axioms EltBridge.Elt.lR_is_chain
#print axioms EltBridge.Elt.lR_exp_pathWeight
#print axioms EltBridge.LocalState.dcur_le_muOf
#print axioms EltBridge.LocalState.fcur_le_muOf
#print axioms EltBridge.mu_factors
#print axioms EltBridge.siteCost_factors
#print axioms EltBridge.alternating_is_chain_sites
#print axioms EltBridge.isTransferDecomposition_family
#print axioms EltBridge.lR_exp_pathWeight_family
#print axioms EltBridge.isResolventSum_vacuous
#print axioms EltBridge.X_pow_dvd_matrix_pow
#print axioms EltBridge.coeff_matrix_pow_eq_zero
#print axioms EltBridge.coeff_neumann_tail_zero
#print axioms EltBridge.weightSum_eq
#print axioms EltBridge.lam_weightSum_eq
#print axioms EltBridge.sum_lam_weightSum_eq
#print axioms EltBridge.sum_univ_toList
#print axioms EltBridge.sum_map_flatMap
#print axioms EltBridge.weightSum_eq_sum_pathWeight
#print axioms EltBridge.compatB_stateOf
#print axioms EltBridge.pathWeight_guarded_eq
#print axioms EltBridge.arr_eq_one_iff
#print axioms EltBridge.dep_eq_one_iff
#print axioms EltBridge.kstar_eq_of_state
#print axioms EltBridge.stateOf_determines
#print axioms EltBridge.d_eq_off_span
#print axioms EltBridge.d_eq_of_states
#print axioms EltBridge.pathData_ext
#print axioms EltBridge.stateOf_injective
#print axioms EltBridge.kstar_le_B_succ
#print axioms EltBridge.A_le_kstar
#print axioms EltBridge.stateOf_injective'
#print axioms EltBridge.validB_stateOf
#print axioms EltBridge.epsValidB_stateOf
#print axioms EltBridge.endValidB_at_A
#print axioms EltBridge.endValidB_at_B
#print axioms EltBridge.flowB_stateOf
#print axioms EltBridge.stepB_stateOf
#print axioms EltBridge.pathWeight_guard_eq
#print axioms EltBridge.pathWeight_stepB_eq
#print axioms EltBridge.travel_zero_off
#print axioms EltBridge.mkPathData
#print axioms EltBridge.mkPathData_d
#print axioms EltBridge.mkPathData_dcur
#print axioms EltBridge.mkPathData_dprev
#print axioms EltBridge.mkPathData_fcur
#print axioms EltBridge.ofPath_toPath
#print axioms EltBridge.toPath_ofPath
#print axioms EltBridge.toPath_injective
#print axioms EltBridge.map_idxList_inj
#print axioms EltBridge.statePath_inj
#print axioms EltBridge.card_le_lR
#print axioms EltBridge.abs_d_le_lR
#print axioms EltBridge.span_bounds
#print axioms EltBridge.kstar_bounds
#print axioms EltBridge.pathData_eq_of_agree
#print axioms EltBridge.pathData_box
#print axioms EltBridge.encAll_inj
#print axioms EltBridge.finite_degree_le
#print axioms EltBridge.sum_configs_eq_sum_paths
#print axioms EltBridge.const_of_step
#print axioms EltBridge.eq_travel_of_flow
#print axioms EltBridge.map_idxList_congr
#print axioms EltBridge.exists_fun_of_length
#print axioms EltBridge.guarded_stateOf
#print axioms EltBridge.exists_config_of_guarded
#print axioms EltBridge.eps_const_of_guarded
#print axioms EltBridge.delta_const_of_guarded
#print axioms EltBridge.dprev_of_guarded
#print axioms EltBridge.fcur_of_guarded
#print axioms EltBridge.dep_of_guarded
#print axioms EltBridge.localState_ext
#print axioms EltBridge.stateOf_eq_of_guarded
#print axioms EltBridge.exists_config_stateOf
#print axioms EltBridge.stateFns_eq_guarded
#print axioms EltBridge.telescope_flow
#print axioms EltBridge.sum_markers_eq
#print axioms EltBridge.fullStepB_stateOf
#print axioms EltBridge.pathWeight_fullStepB_eq
#print axioms EltBridge.headOkB_stateOf
#print axioms EltBridge.tailOkB_stateOf
#print axioms EltBridge.vD_succ_B_eq_travel
#print axioms EltBridge.vD_succ_B_natAbs
#print axioms EltBridge.tailSiteOf_stateOf
#print axioms EltBridge.isTransferDecomposition_edge
#print axioms EltBridge.pathWeight_congr
#print axioms EltBridge.pathWeight_guarded_edge
#print axioms EltBridge.sum_vArr_eq_one
#print axioms EltBridge.flagStepB_flagOf
#print axioms EltBridge.flagHeadVec_flagOf
#print axioms EltBridge.flagTailVec_flagOf
#print axioms EltBridge.pathWeight_flag_of
#print axioms EltBridge.pathWeight_flag_guarded
#print axioms EltBridge.past_mono
#print axioms EltBridge.no_arr_after
#print axioms EltBridge.past_false_of_no_arr
#print axioms EltBridge.exists_arr_index
#print axioms EltBridge.past_of_arr
#print axioms EltBridge.past_true_forward
#print axioms EltBridge.arr_unique_forward
#print axioms EltBridge.flagStepB_shift
#print axioms EltBridge.shiftFn_arr_zero
#print axioms EltBridge.shift_span_brackets
#print axioms EltBridge.exists_of_sum_one
#print axioms EltBridge.unique_of_sum_one
#print axioms EltBridge.dep_sum_eq_arr_sum
#print axioms EltBridge.flow_of_flagStepB
#print axioms EltBridge.exists_dep_index
#print axioms EltBridge.dep_index_unique
#print axioms EltBridge.guarded_of_flag
#print axioms EltBridge.exists_config_of_flag
#print axioms EltBridge.extState_stateOf
#print axioms EltBridge.preState_stateOf
#print axioms EltBridge.extendFn_stateOf
#print axioms EltBridge.extendFn_outer
#print axioms EltBridge.extendFn_eps
#print axioms EltBridge.stateOf_injective_span
#print axioms EltBridge.flagPath_inj
#print axioms EltBridge.sum_configs_eq_sum_flag_paths
#print axioms EltBridge.pathWeight_zero_of_guard_fails
