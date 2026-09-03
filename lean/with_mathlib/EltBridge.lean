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
