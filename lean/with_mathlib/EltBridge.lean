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
