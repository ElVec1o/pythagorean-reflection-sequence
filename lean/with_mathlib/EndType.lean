/-
The end type of a configuration, and the transport of `EdgeData.mult_pos`.

Edges are indexed by `Fin n`; edge `e` carries `m e` crossings, and each crossing
has two ends.  So an end is a crossing together with a choice of which of its two
ends this is:

    Endpt n m = (Σ e : Fin n, Fin (m e)) × Bool

which is a `Fintype` automatically.  `edgeOf` reads off the edge.

`exists_end_of_mult_pos` is the transport: an edge with at least one crossing
carries an end.  That is the hypothesis `hcross` of
`GapFreeAssembly.shared_site_constructed`, and `EdgeData.mult_pos` is what supplies
its premise for a gap-free edge.  With it, the chain from gap-freeness to the
shared site has no assumptions left.
-/
import Mathlib.Tactic
import EdgeData

namespace EndType

/-- Ends of a configuration: a crossing of some edge, and which of its two ends.

A structure with named fields rather than a nested pair.  The earlier encoding, a
sigma type paired with a boolean, made ends fail to destructure without unfolding
and forced an edge equality to be transported through the crossing index's type.
Named fields remove both. -/
structure Endpt (n : ℕ) (m : Fin n → ℕ) where
  /-- the edge this end's crossing lies on -/
  edge : Fin n
  /-- which crossing of that edge -/
  idx : Fin (m edge)
  /-- whether this is the crossing's top end -/
  top : Bool
  deriving DecidableEq

/-- Ends correspond to a crossing together with a choice of end. -/
def endptEquiv (n : ℕ) (m : Fin n → ℕ) :
    Endpt n m ≃ (Σ e : Fin n, Fin (m e)) × Bool where
  toFun x := (⟨x.edge, x.idx⟩, x.top)
  invFun y := ⟨y.1.1, y.1.2, y.2⟩
  left_inv := by rintro ⟨e, i, b⟩; rfl
  right_inv := by rintro ⟨⟨e, i⟩, b⟩; rfl

instance (n : ℕ) (m : Fin n → ℕ) : Fintype (Endpt n m) :=
  Fintype.ofEquiv _ (endptEquiv n m).symm

/-- The edge an end belongs to. -/
def edgeOf {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : ℤ := (x.edge : ℤ)

/-- Which of the crossing's two ends. -/
def atTop {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : Bool := x.top

/-- **The transport.**  An edge with a crossing carries an end.  This is `hcross`. -/
theorem exists_end_of_mult_pos {n : ℕ} {m : Fin n → ℕ} (e : Fin n) (h : 0 < m e) :
    ∃ x : Endpt n m, edgeOf x = (e : ℤ) :=
  ⟨⟨e, ⟨0, h⟩, true⟩, rfl⟩

/-- Every end lies on an edge of the index range, which gives the two span bounds
`GapFreeAssembly.shared_site_constructed` also needs. -/
theorem edgeOf_nonneg {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : 0 ≤ edgeOf x := by
  unfold edgeOf; exact Int.natCast_nonneg _

theorem edgeOf_lt {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : edgeOf x < (n : ℤ) := by
  unfold edgeOf
  exact_mod_cast x.edge.isLt

/-- The multiplicity of a gap-free edge is positive as a natural number, which is
the form the transport needs. -/
theorem mult_natPos {d f : ℤ} (hf : EdgeData.IsTravel f) (hpar : (d - f) % 2 = 0)
    (hgap : ¬ EdgeData.IsGap d f) : 0 < (max |d| |f|).toNat := by
  have h := EdgeData.mult_pos hf hpar hgap
  omega

/-! ### Non-vacuity -/

/-- Two edges, one crossing each: an end exists on edge `0`. -/
theorem witness_end_exists :
    ∃ x : Endpt 2 (fun _ => 1), edgeOf x = (0 : ℤ) :=
  exists_end_of_mult_pos ⟨0, by norm_num⟩ (by norm_num)

/-- An edge with no crossings carries no end, so the hypothesis is doing work. -/
theorem witness_no_end : ¬ ∃ x : Endpt 1 (fun _ => 0), True := by
  rintro ⟨⟨_, i⟩, _⟩
  exact absurd i.isLt (Nat.not_lt_zero _)

/-! ### The crossing-partner map

The first of the two involutions a `WalkGraph.Data` needs, constructed on the
concrete end type.  It exchanges the two ends of a crossing, so it fixes the edge
and flips which end this is, which are exactly the two conditions the walk-graph
data asks of it. -/

/-- Exchange the two ends of a crossing. -/
def partner {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : Endpt n m :=
  ⟨x.edge, x.idx, !x.top⟩

@[simp] theorem partner_edge {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    (partner x).edge = x.edge := rfl

@[simp] theorem partner_top {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    (partner x).top = !x.top := rfl

theorem partner_invol {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    partner (partner x) = x := by
  cases x; simp [partner]

theorem partner_ne {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : partner x ≠ x := by
  intro h
  have := congrArg Endpt.top h
  simp only [partner_top] at this
  exact (Bool.not_ne_self x.top) this

theorem partner_edgeOf {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    edgeOf (partner x) = edgeOf x := rfl

theorem partner_atTop {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    atTop (partner x) = !atTop x := rfl

/-- The two ends of a crossing sit at consecutive sites, one at the edge's index
and one at the next: this is what makes the crossing map move between sites while
the turn stays at one, which is the condition the walk graph needs to have two
distinct neighbours at every end. -/
theorem partner_site_ne {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) :
    (edgeOf (partner x) + (if atTop (partner x) then 1 else 0))
      ≠ (edgeOf x + (if atTop x then 1 else 0)) := by
  rw [partner_edgeOf, partner_atTop]
  cases h : atTop x <;> simp [h]

/-! ### Up-crossings, and the arrival predicate

Counting arrivals and departures at a site needs to know which crossings of an edge
go up.  That has been implicit; here it is a datum, an up-count per edge, with the
first `up e` crossings taken to be the up ones.

An up-crossing arrives at its top end and departs from its bottom one; a
down-crossing does the reverse.  So the arrival predicate is the agreement of "is
this crossing up" with "is this the top end", which is the same rule
`StrandEnds.isArr` states abstractly. -/

/-- Whether a crossing goes up: the first `up e` crossings of edge `e` do. -/
def isUp {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (x : Endpt n m) : Bool :=
  decide (x.idx.val < up x.edge)

/-- An end opens a pair exactly when its crossing's direction agrees with which end
it is. -/
def isArrOf {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (x : Endpt n m) : Bool :=
  isUp up x == atTop x

@[simp] theorem isArrOf_up_top {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (x : Endpt n m) (hu : isUp up x = true) (ht : atTop x = true) :
    isArrOf up x = true := by
  unfold isArrOf; rw [hu, ht]; rfl

@[simp] theorem isArrOf_up_bottom {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (x : Endpt n m) (hu : isUp up x = true) (ht : atTop x = false) :
    isArrOf up x = false := by
  unfold isArrOf; rw [hu, ht]; rfl

/-- The crossing partner of an end has the same direction but the other end, so it
has the opposite role: one of the two ends of a crossing arrives and the other
departs.  This is what makes arrivals and departures at a site pair up at all. -/
theorem isArrOf_partner {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (x : Endpt n m) :
    isArrOf up (partner x) = !isArrOf up x := by
  unfold isArrOf isUp partner atTop
  cases x with
  | mk e i b => cases b <;> simp

/-! ### Arrivals and departures at a site

The two sets the local turn pairs.  Disjointness is immediate from the role
predicate; the card equality is the balance, and is the one obligation left in the
construction. -/

/-- The site of an end. -/
def siteOf {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) : ℤ :=
  edgeOf x + (if atTop x then 1 else 0)

/-- Arrivals at a site. -/
noncomputable def arrAt {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ) :
    Finset (Endpt n m) := by
  classical
  exact Finset.univ.filter (fun x => siteOf x = s ∧ isArrOf up x = true)

/-- Departures at a site. -/
noncomputable def depAt {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ) :
    Finset (Endpt n m) := by
  classical
  exact Finset.univ.filter (fun x => siteOf x = s ∧ isArrOf up x = false)

theorem mem_arrAt {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ) (x : Endpt n m) :
    x ∈ arrAt up s ↔ (siteOf x = s ∧ isArrOf up x = true) := by
  classical
  unfold arrAt
  simp

theorem mem_depAt {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ) (x : Endpt n m) :
    x ∈ depAt up s ↔ (siteOf x = s ∧ isArrOf up x = false) := by
  classical
  unfold depAt
  simp

/-- **Disjointness.**  An end either opens a pair or closes one, never both. -/
theorem arrAt_disjoint_depAt {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ) :
    Disjoint (arrAt (m := m) up s) (depAt (m := m) up s) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_arrAt] at hx
  rw [mem_depAt] at hx'
  rw [hx.2] at hx'
  exact Bool.noConfusion hx'.2

/-! ### Counting, piece one: split by which end

Every end is a top end or a bottom end, so any set of ends splits in two, and the
two parts are the ones that come from the two adjacent edges. This is the first
step of the count and is pure bookkeeping. -/

theorem card_split_atTop {n : ℕ} {m : Fin n → ℕ} (S : Finset (Endpt n m)) :
    (S.filter (fun x => atTop x = true)).card
      + (S.filter (fun x => atTop x = false)).card = S.card := by
  classical
  have h : ∀ x : Endpt n m, (atTop x = false) ↔ ¬ (atTop x = true) := by
    intro x; cases h : atTop x <;> simp [h]
  rw [Finset.filter_congr (fun x _ => (h x))]
  exact Finset.filter_card_add_filter_neg_card_eq_card _

/-- A top end at site `s` sits on edge `s - 1`, and a bottom end on edge `s`.  This
is what identifies the two parts of the split with the two adjacent edges. -/
theorem edge_of_site_top {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) (s : ℤ)
    (hs : siteOf x = s) (ht : atTop x = true) : edgeOf x = s - 1 := by
  unfold siteOf at hs
  rw [ht] at hs
  simp only [if_true] at hs
  omega

theorem edge_of_site_bottom {n : ℕ} {m : Fin n → ℕ} (x : Endpt n m) (s : ℤ)
    (hs : siteOf x = s) (ht : atTop x = false) : edgeOf x = s := by
  unfold siteOf at hs
  rw [ht] at hs
  simpa using hs

/-! ### Counting, piece two: what each part of the split is

A top-end arrival is an up-crossing, since the role is the agreement of direction
with which end this is; and it lies on the edge below its site.  A bottom-end
arrival is a down-crossing on the edge above.  The departures are the two
complementary descriptions. -/

theorem arr_top_iff {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ) (x : Endpt n m) :
    (x ∈ arrAt up s ∧ atTop x = true)
      ↔ (edgeOf x = s - 1 ∧ atTop x = true ∧ isUp up x = true) := by
  classical
  rw [mem_arrAt]
  constructor
  · rintro ⟨⟨hs, ha⟩, ht⟩
    refine ⟨edge_of_site_top x s hs ht, ht, ?_⟩
    unfold isArrOf at ha
    rw [ht] at ha
    simpa using ha
  · rintro ⟨he, ht, hu⟩
    refine ⟨⟨?_, ?_⟩, ht⟩
    · unfold siteOf; rw [ht, he]; simp
    · unfold isArrOf; rw [ht, hu]; rfl

theorem arr_bottom_iff {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ)
    (x : Endpt n m) :
    (x ∈ arrAt up s ∧ atTop x = false)
      ↔ (edgeOf x = s ∧ atTop x = false ∧ isUp up x = false) := by
  classical
  rw [mem_arrAt]
  constructor
  · rintro ⟨⟨hs, ha⟩, ht⟩
    refine ⟨edge_of_site_bottom x s hs ht, ht, ?_⟩
    unfold isArrOf at ha
    rw [ht] at ha
    simpa using ha
  · rintro ⟨he, ht, hu⟩
    refine ⟨⟨?_, ?_⟩, ht⟩
    · unfold siteOf; rw [ht, he]; simp
    · unfold isArrOf; rw [ht, hu]; rfl

/-! ### Counting, piece three: crossing indices below the up-count

On a single edge the up-crossings are the indices below the up-count, so counting
them is counting `{i : Fin N // i < k}`.  That is `min k N`, and with the up-count
bounded by the crossing count it is just the up-count. -/

theorem card_fin_lt (N k : ℕ) :
    (Finset.univ.filter (fun i : Fin N => i.val < k)).card = min k N := by
  classical
  by_cases h : N ≤ k
  · have hall : ∀ i : Fin N, i.val < k := fun i => lt_of_lt_of_le i.isLt h
    rw [Finset.filter_true_of_mem (fun i _ => hall i)]
    simp [min_eq_right h]
  · push Not at h
    have heq : (Finset.univ.filter (fun i : Fin N => i.val < k))
        = Finset.Iio (⟨k, h⟩ : Fin N) := by
      ext i
      simp [Fin.lt_def]
    rw [heq, Fin.card_Iio]
    simp [min_eq_left (le_of_lt h)]

/-! ### Counting, piece four: the whole end type

The remaining transport is across the dependent pair.  Writing the count as a sum
over edges avoids the difficulty directly: `Fintype.card_sigma` turns a count over
`(Σ e, Fin (m e))` into a sum of per-edge counts, and each of those is `card_fin_lt`
on that edge.

The obstruction to doing it pointwise is worth recording, since it is not a gap in
the argument but a feature of the encoding: constraining `x.1.1 = e` leaves
`x.1.2 : Fin (m x.1.1)`, which is not definitionally `Fin (m e)`, so a per-edge
filter has to transport along that equality rather than simply match. The sum form
sidesteps it. -/

/-- The end type has twice as many elements as there are crossings. -/
theorem card_endpt (n : ℕ) (m : Fin n → ℕ) :
    Fintype.card (Endpt n m) = (∑ e : Fin n, m e) * 2 := by
  classical
  rw [Fintype.card_congr (endptEquiv n m), Fintype.card_prod, Fintype.card_sigma]
  simp [Fintype.card_fin]

/-- The crossings on an edge split into up and down, whose counts add to the
crossing count once the up-count is bounded by it.  This is the per-edge form the
sum needs. -/
theorem up_add_down (N k : ℕ) (h : k ≤ N) :
    (Finset.univ.filter (fun i : Fin N => i.val < k)).card
      + (Finset.univ.filter (fun i : Fin N => ¬ (i.val < k))).card = N := by
  classical
  rw [Finset.filter_card_add_filter_neg_card_eq_card]
  simp

/-! ### The card equality

Assembling the four counting pieces.  Each of the two sets splits by which end it
is, the two parts are the up- and down-crossings of the two adjacent edges, and the
balance says the totals agree.

The four per-edge counts appear as hypotheses.  They are what the sum-over-edges
transport supplies, and they are stated in terms of up- and down-counts rather than
by subtracting, so no truncated subtraction enters. -/

theorem card_arr_eq_card_dep {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ)
    (upLo dnLo upHi dnHi : ℕ)
    (harrTop : ((arrAt (m := m) up s).filter (fun x => atTop x = true)).card = upLo)
    (harrBot : ((arrAt (m := m) up s).filter (fun x => atTop x = false)).card = dnHi)
    (hdepTop : ((depAt (m := m) up s).filter (fun x => atTop x = true)).card = dnLo)
    (hdepBot : ((depAt (m := m) up s).filter (fun x => atTop x = false)).card = upHi)
    (hbal : upLo + dnHi = dnLo + upHi) :
    (arrAt (m := m) up s).card = (depAt (m := m) up s).card := by
  classical
  rw [← card_split_atTop (arrAt (m := m) up s), ← card_split_atTop (depAt (m := m) up s),
      harrTop, harrBot, hdepTop, hdepBot]
  exact hbal

/-- With the card equality and the disjointness already proved, the local turn
exists at that site: the two sets are disjoint and equinumerous, which is exactly
what the involution construction takes. -/
theorem local_turn_exists {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ) (s : ℤ)
    (hcard : (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    Disjoint (arrAt (m := m) up s) (depAt (m := m) up s) ∧
      (arrAt (m := m) up s).card = (depAt (m := m) up s).card :=
  ⟨arrAt_disjoint_depAt up s, hcard⟩

/-! ### Counting, piece five: the obligation, and why it resists

The four per-edge counts are the last link.  Each says that the ends on one edge
with one direction and one choice of end number `min (up e) (m e)`.  The content is
`card_fin_lt`, already proved; what is left is transporting it across the encoding.

Two attempts are recorded rather than a broken proof.  The first tried to identify
the set with the image of a filter on that edge's indices under an injection, and
the second tried destructuring an end and substituting the edge equality.  Both
foundered on the same point: `Endpt` is a definition rather than a structure, so an
end does not destructure without unfolding, and once unfolded the crossing index
carries the edge in its type, so an equality of edges has to move it.

The favourable observation, which any next attempt should start from, is that the
up-condition is on `x.1.2.val`, a natural number, so it needs no coercion at all.
Only the identification of the two edges does.  Making `Endpt` a structure with
named fields, or working throughout with `Finset.sigma` rather than a filter over
the whole type, would remove the difficulty; both are changes to the encoding
rather than to the mathematics.
-/

/-- **The per-edge count.**  With named fields an end destructures directly and the
edge equality substitutes, so the set is the image of a filter on that edge's
crossing indices under an injection. -/
theorem card_ends_edge_dir {n : ℕ} {m : Fin n → ℕ} (up : Fin n → ℕ)
    (e : Fin n) (b : Bool) :
    (Finset.univ.filter (fun x : Endpt n m =>
        x.edge = e ∧ x.top = b ∧ x.idx.val < up e)).card = min (up e) (m e) := by
  classical
  have hset : (Finset.univ.filter (fun x : Endpt n m =>
      x.edge = e ∧ x.top = b ∧ x.idx.val < up e))
      = (Finset.univ.filter (fun i : Fin (m e) => i.val < up e)).image
          (fun i => (⟨e, i, b⟩ : Endpt n m)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨e', i, b'⟩ := x
      cases h1; cases h2
      exact ⟨i, h3, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨rfl, rfl, hj⟩
  rw [hset, Finset.card_image_of_injective _ ?_, card_fin_lt]
  intro a c hac
  simpa using hac

-- Certification (Rule 5).
#print axioms EndType.exists_end_of_mult_pos
#print axioms EndType.edgeOf_nonneg
#print axioms EndType.edgeOf_lt
#print axioms EndType.mult_natPos
#print axioms EndType.witness_end_exists
#print axioms EndType.witness_no_end
#print axioms EndType.partner_invol
#print axioms EndType.partner_ne
#print axioms EndType.partner_edgeOf
#print axioms EndType.partner_site_ne
#print axioms EndType.isArrOf_partner
#print axioms EndType.mem_arrAt
#print axioms EndType.arrAt_disjoint_depAt
#print axioms EndType.card_split_atTop
#print axioms EndType.edge_of_site_top
#print axioms EndType.edge_of_site_bottom
#print axioms EndType.arr_top_iff
#print axioms EndType.arr_bottom_iff
#print axioms EndType.card_fin_lt
#print axioms EndType.card_endpt
#print axioms EndType.up_add_down
#print axioms EndType.card_arr_eq_card_dep
#print axioms EndType.local_turn_exists
#print axioms EndType.card_ends_edge_dir

end EndType
