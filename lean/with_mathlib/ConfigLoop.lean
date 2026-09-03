/-
The merge loop, on an actual lamp configuration.

`merges_to_one` is stated for abstract walk-graph data.  A configuration supplies
every component of its invariant from lemmas already proved: the crossing map is
`partner` by definition, the turn respects sites by `turnAt_site`, and it alternates
arrival with departure by `turn_arr_flip`.

The one genuine input is the covering hypothesis -- that an edge immediately left of
some end carries a top end.  That is what gap-freeness provides, and it is stated
without reference to the pairing, since whether an edge carries a top end does not
depend on how ends are matched.
-/
import Mathlib.Tactic
import DataBuild
import WalkSupport
import CostMerge
import EdgeData
import GroupElt
import NoGapCutFree
import CutComponents
import SiteCost

namespace ConfigLoop

open EndType DataBuild WalkGraph WalkSupport

variable {n : ℕ} {m : Fin n → ℕ}

/-- A configuration satisfies the merge invariant. -/
theorem merges_dataOf (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    Merges siteOf (isArrOf up) partner (dataOf up hbal) :=
  ⟨rfl, fun e => turnAt_site up hbal e, fun e => turn_arr_flip up hbal e⟩

/-- **The merge loop on a configuration.**  Given the covering property, the walks of
a lamp configuration merge down to a single walk. -/
theorem config_merges_to_one (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hcov0 : ∀ j : ℤ, (∃ u : Endpt n m, edgeOf u = j) → (∃ v : Endpt n m, edgeOf v < j) →
      ∃ y : Endpt n m, edgeOf y = j - 1 ∧ atTop y = true) :
    ∃ D' : Data (Endpt n m),
      Merges siteOf (isArrOf up) partner D' ∧ walkCount D' ≤ 1 :=
  merges_to_one (α := Endpt n m) (edgeOf (n := n) (m := m)) (siteOf (n := n) (m := m))
    (atTop (n := n) (m := m)) (isArrOf up) (partner (n := n) (m := m))
    (fun _ => rfl) (fun x => partner_edgeOf x) (fun x => partner_top x)
    hcov0 (dataOf up hbal) (merges_dataOf up hbal)

/-- **The covering hypothesis holds when every edge carries a crossing.**

With `j` pinned to be some end's edge, `j` lies in `[0, n)`; the second antecedent
forces `j ≥ 1`, so `j - 1` is a genuine edge index.  Gap-freeness makes its
multiplicity positive, and the top end of its first crossing is the witness.

(The hypothesis was first stated for *all* `j : ℤ`, which is false for every
non-empty configuration -- take `j` beyond the last edge -- and would have made the
statement vacuous.) -/
theorem covering_of_mult_pos (hm : ∀ e : Fin n, 0 < m e) :
    ∀ j : ℤ, (∃ u : Endpt n m, edgeOf u = j) → (∃ v : Endpt n m, edgeOf v < j) →
      ∃ y : Endpt n m, edgeOf y = j - 1 ∧ atTop y = true := by
  rintro j ⟨u, hu⟩ ⟨v, hv⟩
  have hv0 : (0 : ℤ) ≤ edgeOf v := by
    unfold edgeOf; exact Int.natCast_nonneg _
  have hjn : j < (n : ℤ) := by
    rw [← hu]; unfold edgeOf; exact_mod_cast u.edge.isLt
  have hlt : (j - 1).toNat < n := by omega
  refine ⟨⟨⟨(j - 1).toNat, hlt⟩, ⟨0, hm _⟩, true⟩, ?_, rfl⟩
  show ((((j - 1).toNat : ℕ) : ℤ)) = j - 1
  omega

/-- **A gap-free configuration merges to a single walk.**  Nothing is assumed beyond
the balance that defines the turn and the positivity of every multiplicity, which is
what gap-freeness gives. -/
theorem gapfree_merges_to_one (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hm : ∀ e : Fin n, 0 < m e) :
    ∃ D' : Data (Endpt n m),
      Merges siteOf (isArrOf up) partner D' ∧ walkCount D' ≤ 1 :=
  config_merges_to_one up hbal (covering_of_mult_pos hm)

/-! ### Balance at the boundary

`card_arr_eq_card_dep_of_edges` needs edges on *both* sides of a site.  At the two
ends of the strip one side is missing, and there the balance is a condition on a
single edge.  These lemmas supply it. -/

/-- With no edge at `s - 1`, no end at site `s` is a top end. -/
theorem no_top_at (up : Fin n → ℕ) (s : ℤ) (hno : ∀ e : Fin n, (e : ℤ) ≠ s - 1) :
    ((arrAt (m := m) up s).filter (fun x => atTop x = true)).card = 0 ∧
    ((depAt (m := m) up s).filter (fun x => atTop x = true)).card = 0 := by
  constructor <;> rw [Finset.card_eq_zero] <;> ext x <;>
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  · intro hx ht
    exact hno x.edge (((arr_top_iff up s x).mp ⟨hx, ht⟩).1)
  · intro hx ht
    exact hno x.edge (((dep_top_iff up s x).mp ⟨hx, ht⟩).1)

/-- With no edge at `s`, no end at site `s` is a bottom end. -/
theorem no_bottom_at (up : Fin n → ℕ) (s : ℤ) (hno : ∀ e : Fin n, (e : ℤ) ≠ s) :
    ((arrAt (m := m) up s).filter (fun x => atTop x = false)).card = 0 ∧
    ((depAt (m := m) up s).filter (fun x => atTop x = false)).card = 0 := by
  constructor <;> rw [Finset.card_eq_zero] <;> ext x <;>
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  · intro hx ht
    exact hno x.edge (((arr_bottom_iff up s x).mp ⟨hx, ht⟩).1)
  · intro hx ht
    exact hno x.edge (((dep_bottom_iff up s x).mp ⟨hx, ht⟩).1)

/-- **Balance at the left boundary.**  Only the edge at `s` contributes, so the site
balances exactly when that edge's crossings split evenly. -/
theorem balance_left (up : Fin n → ℕ) (s : ℤ) (e : Fin n) (he : (e : ℤ) = s)
    (hno : ∀ e' : Fin n, (e' : ℤ) ≠ s - 1)
    (hsplit : m e - min (up e) (m e) = min (up e) (m e)) :
    (arrAt (m := m) up s).card = (depAt (m := m) up s).card := by
  obtain ⟨h1, h2⟩ := no_top_at (m := m) up s hno
  rw [← card_split_atTop (arrAt (m := m) up s), ← card_split_atTop (depAt (m := m) up s),
    h1, h2, card_arr_bottom up s e he, card_dep_bottom up s e he, hsplit]

/-- **Balance at the right boundary.**  Symmetrically, only the edge at `s - 1`
contributes. -/
theorem balance_right (up : Fin n → ℕ) (s : ℤ) (e : Fin n) (he : (e : ℤ) = s - 1)
    (hno : ∀ e' : Fin n, (e' : ℤ) ≠ s)
    (hsplit : min (up e) (m e) = m e - min (up e) (m e)) :
    (arrAt (m := m) up s).card = (depAt (m := m) up s).card := by
  obtain ⟨h1, h2⟩ := no_bottom_at (m := m) up s hno
  rw [← card_split_atTop (arrAt (m := m) up s), ← card_split_atTop (depAt (m := m) up s),
    h1, h2, card_arr_top up s e he, card_dep_top up s e he]
  omega

/-- **A site with no adjacent edge is empty**, so it balances trivially. -/
theorem balance_empty (up : Fin n → ℕ) (s : ℤ)
    (hlo : ∀ e : Fin n, (e : ℤ) ≠ s - 1) (hhi : ∀ e : Fin n, (e : ℤ) ≠ s) :
    (arrAt (m := m) up s).card = (depAt (m := m) up s).card := by
  obtain ⟨h1, h2⟩ := no_top_at (m := m) up s hlo
  obtain ⟨h3, h4⟩ := no_bottom_at (m := m) up s hhi
  rw [← card_split_atTop (arrAt (m := m) up s), ← card_split_atTop (depAt (m := m) up s),
    h1, h2, h3, h4]

/-! ### Non-vacuity

`gapfree_merges_to_one` carries two hypotheses.  The empty configuration satisfies
both, which settles that they are consistent -- but it is a weak witness, and the
substantive one is below. -/

/-- The empty configuration: no edges, hence no ends, and every count is zero. -/
theorem empty_hbal (up : Fin 0 → ℕ) :
    ∀ s : ℤ, (arrAt (m := fun _ => 0) up s).card = (depAt (m := fun _ => 0) up s).card := by
  intro s
  have : ∀ (t : Finset (Endpt 0 (fun _ => 0))), t.card = 0 := by
    intro t
    rw [Finset.card_eq_zero]
    ext x
    exact absurd x.edge.isLt (Nat.not_lt_zero _)
  rw [this, this]

/-- So the hypotheses of `gapfree_merges_to_one` are consistent. -/
theorem gapfree_not_vacuous (up : Fin 0 → ℕ) :
    ∃ D' : Data (Endpt 0 (fun _ => 0)),
      Merges siteOf (isArrOf up) partner D' ∧ walkCount D' ≤ 1 :=
  gapfree_merges_to_one up (empty_hbal up) (fun e => absurd e.isLt (Nat.not_lt_zero _))

/-! ### The substantive witness

One edge carrying two crossings, one of them up.  Both of its sites are boundaries:
site `0` holds the two bottom ends and site `1` the two top ends, and each balances
because `min 1 2 = 1 = 2 - 1`.  Unlike the empty configuration this has `m e > 0`, so
`covering_of_mult_pos` is genuinely exercised. -/

/-- Every edge index of `Fin 1` is `0`. -/
theorem fin_one_edge (e : Fin 1) : ((e : ℕ) : ℤ) = 0 := by
  have := e.isLt; omega

/-- The one-edge configuration balances at every site. -/
theorem one_edge_hbal :
    ∀ s : ℤ, (arrAt (m := fun _ : Fin 1 => 2) (fun _ => 1) s).card
           = (depAt (m := fun _ : Fin 1 => 2) (fun _ => 1) s).card := by
  intro s
  by_cases h0 : s = 0
  · subst h0
    exact balance_left (m := fun _ : Fin 1 => 2) (fun _ => 1) 0 0
      (fin_one_edge 0) (fun e => by rw [fin_one_edge e]; norm_num) (by norm_num)
  by_cases h1 : s = 1
  · subst h1
    exact balance_right (m := fun _ : Fin 1 => 2) (fun _ => 1) 1 0
      (by rw [fin_one_edge 0]; norm_num)
      (fun e => by rw [fin_one_edge e]; norm_num) (by norm_num)
  · exact balance_empty (m := fun _ : Fin 1 => 2) (fun _ => 1) s
      (fun e => by rw [fin_one_edge e]; omega)
      (fun e => by rw [fin_one_edge e]; omega)

/-- **The substantive witness.**  A configuration with a real edge, real crossings and
a positive multiplicity merges to a single walk. -/
theorem one_edge_merges :
    ∃ D' : Data (Endpt 1 (fun _ => 2)),
      Merges siteOf (isArrOf (fun _ => 1)) partner D' ∧ walkCount D' ≤ 1 :=
  gapfree_merges_to_one (m := fun _ : Fin 1 => 2) (fun _ => 1)
    one_edge_hbal (fun _ => by norm_num)

/-! ### Exactly one walk

`gapfree_merges_to_one` gives `walkCount ≤ 1`.  What `thm:nogap` asserts is that the
defect vanishes, which is *exactly one* walk, so the lower bound is wanted too.  It
holds as soon as there is an end at all. -/

/-- A positive multiplicity puts an end on the edge. -/
theorem end_of_mult (e : Fin n) (h : 0 < m e) : Nonempty (Endpt n m) :=
  ⟨⟨e, ⟨0, h⟩, true⟩⟩

/-- **A gap-free configuration has exactly one walk.**  This is `thm:nogap`'s
conclusion in the walk model: the defect is zero. -/
theorem gapfree_single_walk (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hm : ∀ e : Fin n, 0 < m e) (e0 : Fin n) :
    ∃ D' : Data (Endpt n m),
      Merges siteOf (isArrOf up) partner D' ∧ walkCount D' = 1 := by
  classical
  obtain ⟨D', hM, hle⟩ := gapfree_merges_to_one up hbal hm
  refine ⟨D', hM, le_antisymm hle ?_⟩
  have : Nonempty (Endpt n m) := end_of_mult e0 (hm e0)
  have hne : Nonempty (graph D').ConnectedComponent :=
    ⟨(graph D').connectedComponentMk (Classical.arbitrary _)⟩
  exact Fintype.card_pos_iff.mpr hne

/-- The one-edge configuration has exactly one walk. -/
theorem one_edge_single_walk :
    ∃ D' : Data (Endpt 1 (fun _ => 2)),
      Merges siteOf (isArrOf (fun _ : Fin 1 => 1)) partner D' ∧ walkCount D' = 1 :=
  gapfree_single_walk (m := fun _ : Fin 1 => 2) (fun _ => 1)
    one_edge_hbal (fun _ => by norm_num) 0

/-! ### The defect, and what its identification with the paper's `c` still needs

The paper's `c(g)` counts **isolated cycles**: a realisation is one open walk together
with `c` closed cycles, and `thm:nogap` says `c = 0`.

In this model the turn is a *total* involution on all ends, so the walk graph is
2-regular everywhere and every component is a closed cycle -- the open strand is
closed up.  The component count is therefore `1 + c` **provided one component is
designated as the open walk**.  Nothing here designates one, and all components are
symmetric under the structure as formalised.

So `defect` below is the walk-model defect, and `gapfree_defect_zero` is `thm:nogap`
in that model.  The identification `defect = c` is a MODELLING CLAIM and is recorded
as such rather than asserted: it needs a basepoint, or an argument that the open walk
is distinguishable.  This is the same kind of claim that was wrong twice in this
development, so it is not being made on inspection. -/

/-- The walk-model defect: components beyond the first. -/
noncomputable def defect {α : Type*} [Fintype α] [DecidableEq α] (D : Data α) : ℕ :=
  walkCount D - 1

/-- **`thm:nogap` in the walk model.**  A gap-free configuration has zero defect. -/
theorem gapfree_defect_zero (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hm : ∀ e : Fin n, 0 < m e) (e0 : Fin n) :
    ∃ D' : Data (Endpt n m),
      Merges siteOf (isArrOf up) partner D' ∧ defect D' = 0 := by
  obtain ⟨D', hM, h1⟩ := gapfree_single_walk up hbal hm e0
  exact ⟨D', hM, by unfold defect; omega⟩

/-! ### The basepoint closes the identification

The missing ingredient was a designated open walk.  A realisation has one: the word
has a start.  Marking any end `b`, the isolated cycles are exactly the components
*other than* `b`'s, and that count is `walkCount - 1` unconditionally.  So with a
basepoint, `defect` is the isolated-cycle count by definition rather than by a
modelling claim. -/

/-- The components other than the marked one -- the isolated cycles. -/
noncomputable def otherComponents {α : Type*} [Fintype α] [DecidableEq α]
    (D : Data α) (b : α) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun k : (graph D).ConnectedComponent => k ≠ (graph D).connectedComponentMk b)).card

/-- **The isolated-cycle count is the defect.**  Unconditional, for any basepoint. -/
theorem otherComponents_eq_defect {α : Type*} [Fintype α] [DecidableEq α]
    (D : Data α) (b : α) : otherComponents D b = defect D := by
  classical
  unfold otherComponents defect walkCount
  have h : (Finset.univ.filter
      (fun k : (graph D).ConnectedComponent => k ≠ (graph D).connectedComponentMk b))
      = Finset.univ.erase ((graph D).connectedComponentMk b) := by
    ext k; simp [Finset.mem_erase]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- **`thm:nogap`, with the isolated cycles counted against a basepoint.**  A gap-free
configuration has no isolated cycles. -/
theorem gapfree_no_isolated_cycles (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hm : ∀ e : Fin n, 0 < m e) (e0 : Fin n) :
    ∃ D' : Data (Endpt n m), Merges siteOf (isArrOf up) partner D' ∧
      ∀ b : Endpt n m, otherComponents D' b = 0 := by
  obtain ⟨D', hM, hz⟩ := gapfree_defect_zero up hbal hm e0
  exact ⟨D', hM, fun b => by rw [otherComponents_eq_defect D' b, hz]⟩

/-! ### `thm:nogap`

The paper states: *if `g` has no gap edge then `c(g) = 0`.*

Below is that statement in one place, so the correspondence with the paper is
checkable without reassembling it from eight files.

**What is formalised.**  A lamp configuration is given by multiplicities `m` and
up-counts `up`.  "No gap edge" is `∀ e, 0 < m e` -- every edge carries a crossing.
`hbal` is the arrival/departure balance that makes the turn exist, which is a
property of the configuration, proved at interior sites by
`EndType.card_arr_eq_card_dep_of_edges` and at the two boundaries by `balance_left`
and `balance_right`.  The conclusion is that some realisation of the configuration
has no isolated cycle, against any basepoint -- `c(g) = 0`.

**What is not.**  The passage from a group element `g` to its configuration, and the
cost-minimality of the realisation produced, are not formalised here; the merge
preserves `Merges`, not a cost.  So this is `thm:nogap` for configurations, which is
where its content lies, and not a formal proof of the paper's sentence about `g`. -/
theorem thm_nogap (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hnogap : ∀ e : Fin n, 0 < m e) (e0 : Fin n) :
    ∃ D' : Data (Endpt n m),
      Merges siteOf (isArrOf up) partner D' ∧
      walkCount D' = 1 ∧
      ∀ b : Endpt n m, otherComponents D' b = 0 := by
  obtain ⟨D', hM, hone⟩ := gapfree_single_walk up hbal hnogap e0
  refine ⟨D', hM, hone, fun b => ?_⟩
  rw [otherComponents_eq_defect D' b]
  unfold defect
  omega

/-- `thm:nogap` on the one-edge configuration, so the statement above is known to
have content. -/
theorem thm_nogap_witness :
    ∃ D' : Data (Endpt 1 (fun _ => 2)),
      Merges siteOf (isArrOf (fun _ : Fin 1 => 1)) partner D' ∧
      walkCount D' = 1 ∧
      ∀ b : Endpt 1 (fun _ => 2), otherComponents D' b = 0 :=
  thm_nogap (m := fun _ : Fin 1 => 2) (fun _ => 1) one_edge_hbal (fun _ => by norm_num) 0

/-! ### The cost-minimal merge on a configuration

`EndData.Data` for a lamp configuration takes `side = atTop` and `isArr = isArrOf up`;
the deposit signs are whatever the configuration's deposits give, and nothing below
depends on which. -/

/-- The end data of a configuration. -/
def endDataOf (up : Fin n → ℕ) (ds : Bool → Bool) : EndData.Data (Endpt n m) :=
  ⟨atTop, isArrOf up, ds⟩

/-- **A gap-free configuration has a cost-minimal realisation with exactly one walk.**

This is `thm:nogap` with cost carried: not merely *some* realisation with no isolated
cycle, but a **cost-minimal** one -- which is what the paper's statement is about. -/
theorem config_min_single_walk (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hm : ∀ e : Fin n, 0 < m e) (e0 : Fin n) (ds : Bool → Bool) :
    ∃ D' : Data (Endpt n m),
      CostMerge.MergesMin siteOf (isArrOf up) partner (endDataOf (m := m) up ds) D' ∧
      walkCount D' = 1 := by
  classical
  obtain ⟨E, hE⟩ := CostMerge.exists_mergesMin siteOf partner (endDataOf (m := m) up ds)
    (dataOf up hbal) (merges_dataOf up hbal)
  obtain ⟨D', hD', hle⟩ := CostMerge.min_merges_to_one edgeOf siteOf atTop partner
    (endDataOf (m := m) up ds) (fun _ => rfl) (fun _ => rfl)
    (fun x => partner_edgeOf x) (fun x => partner_top x)
    (covering_of_mult_pos hm) ⟨e0, ⟨0, hm e0⟩, true⟩ E hE
  refine ⟨D', hD', le_antisymm hle ?_⟩
  have : Nonempty (Endpt n m) := end_of_mult e0 (hm e0)
  exact Fintype.card_pos_iff.mpr ⟨(graph D').connectedComponentMk (Classical.arbitrary _)⟩

/-! ### `thm:nogap`, final form

The paper: *if `g` has no gap edge then `c(g) = 0`* -- where `c` counts isolated
cycles of a **relaxed-optimal** realisation.

**Formalised.**  A configuration is `(m, up)`; "no gap edge" is `∀ e, 0 < m e`; `hbal`
is the arrival/departure balance that makes the turn exist, proved at interior sites
by `EndType.card_arr_eq_card_dep_of_edges` and at the two boundaries by
`balance_left`/`balance_right`.  The conclusion is that a **cost-minimal** realisation
has exactly one walk, hence no isolated cycle against any basepoint.  Cost-minimality
is over the whole class of realisations of the configuration, so this is the paper's
"relaxed-optimal", not merely "some realisation".

**Not formalised.**  The passage from a group element `g` to its configuration.  That
is the one remaining link, and it is bookkeeping about how `m` and `up` are read off
`g` -- not part of the merge argument.

The earlier `thm_nogap` above is the cost-free version, kept because it is what the
combinatorial chain proves on its own. -/
theorem thm_nogap_optimal (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hnogap : ∀ e : Fin n, 0 < m e) (e0 : Fin n) (ds : Bool → Bool) :
    ∃ D' : Data (Endpt n m),
      CostMerge.MergesMin siteOf (isArrOf up) partner (endDataOf (m := m) up ds) D' ∧
      walkCount D' = 1 ∧
      ∀ b : Endpt n m, otherComponents D' b = 0 := by
  obtain ⟨D', hM, hone⟩ := config_min_single_walk up hbal hnogap e0 ds
  refine ⟨D', hM, hone, fun b => ?_⟩
  rw [otherComponents_eq_defect D' b]
  unfold defect
  omega

/-- `thm:nogap` in final form on the one-edge configuration, so it is known to have
content. -/
theorem thm_nogap_optimal_witness (ds : Bool → Bool) :
    ∃ D' : Data (Endpt 1 (fun _ => 2)),
      CostMerge.MergesMin siteOf (isArrOf (fun _ : Fin 1 => 1)) partner
        (endDataOf (m := fun _ : Fin 1 => 2) (fun _ => 1) ds) D' ∧
      walkCount D' = 1 ∧
      ∀ b : Endpt 1 (fun _ => 2), otherComponents D' b = 0 :=
  thm_nogap_optimal (m := fun _ : Fin 1 => 2) (fun _ => 1) one_edge_hbal
    (fun _ => by norm_num) 0 ds

/-! ### `cor:localzero`

The paper: *if the lamp support of `g` lies inside its travel interval then
`c(g) = 0`*, proved by observing that no edge is then a gap edge and applying
`thm:nogap`.  Both halves are available: `GroupElt.no_gap_of_pure_travel` for the
first and `thm_nogap_optimal` for the second.  What links them is that a non-gap edge
has positive multiplicity. -/

/-- **No gap edge gives positive multiplicity at every edge.** -/
theorem mult_pos_of_config (dep trav : Fin n → ℤ)
    (hf : ∀ e, EdgeData.IsTravel (trav e))
    (hpar : ∀ e, (dep e - trav e) % 2 = 0)
    (hmdef : ∀ e, m e = (max |dep e| |trav e|).toNat)
    (hng : ∀ e, ¬ EdgeData.IsGap (dep e) (trav e)) :
    ∀ e : Fin n, 0 < m e := by
  intro e
  have h := EdgeData.mult_pos (hf e) (hpar e) (hng e)
  rw [hmdef e]
  omega

/-- **`cor:localzero`.**  If no edge is a gap edge -- which is what lamp support
inside the travel interval gives, by `GroupElt.no_gap_of_pure_travel` -- then a
cost-minimal realisation has one walk and no isolated cycle. -/
theorem cor_localzero (up : Fin n → ℕ) (dep trav : Fin n → ℤ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hf : ∀ e, EdgeData.IsTravel (trav e))
    (hpar : ∀ e, (dep e - trav e) % 2 = 0)
    (hmdef : ∀ e, m e = (max |dep e| |trav e|).toNat)
    (hng : ∀ e, ¬ EdgeData.IsGap (dep e) (trav e))
    (e0 : Fin n) (ds : Bool → Bool) :
    ∃ D' : Data (Endpt n m),
      CostMerge.MergesMin siteOf (isArrOf up) partner (endDataOf (m := m) up ds) D' ∧
      walkCount D' = 1 ∧
      ∀ b : Endpt n m, otherComponents D' b = 0 :=
  thm_nogap_optimal up hbal (mult_pos_of_config dep trav hf hpar hmdef hng) e0 ds

/-- **`cor:localzero` from the paper's hypothesis.**  Lamp support inside the travel
interval, read off edge by edge, gives no gap edge, hence a cost-minimal realisation
with one walk and no isolated cycle. -/
theorem cor_localzero_pure (k : ℤ) (lamps : ℤ → ℤ) (up : Fin n → ℕ)
    (dep trav : Fin n → ℤ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hf : ∀ e, EdgeData.IsTravel (trav e))
    (hpar : ∀ e, (dep e - trav e) % 2 = 0)
    (hmdef : ∀ e, m e = (max |dep e| |trav e|).toNat)
    (hdep : ∀ e : Fin n, dep e = lamps (e : ℤ))
    (htrav : ∀ e : Fin n, trav e = NoGapCutFree.f k (e : ℤ))
    (hpure : ∀ i : ℤ, lamps i ≠ 0 → GroupElt.InTravel k i)
    (hspan : ∀ e : Fin n, lamps (e : ℤ) ≠ 0 ∨ GroupElt.InTravel k (e : ℤ))
    (e0 : Fin n) (ds : Bool → Bool) :
    ∃ D' : Data (Endpt n m),
      CostMerge.MergesMin siteOf (isArrOf up) partner (endDataOf (m := m) up ds) D' ∧
      walkCount D' = 1 ∧
      ∀ b : Endpt n m, otherComponents D' b = 0 := by
  refine cor_localzero up dep trav hbal hf hpar hmdef (fun e => ?_) e0 ds
  rw [hdep e, htrav e]
  exact GroupElt.no_gap_of_pure_travel hpure (hspan e)

/-! ### `prop:travelinv`

The paper's argument: a pure-travel element has no gap edge, so `thm:nogap` gives a
relaxed-optimal realisation with no isolated cycle; that realisation is a single open
walk, hence admissible for `ℓ_T`, so `ℓ_T ≤ ℓ_R`; and `ℓ_T ≥ ℓ_R` because the relaxed
minimum ranges over a superset.  Therefore `ℓ_T = ℓ_R` on pure-travel elements.

Here `ℓ_R` is the minimum cost over all realisations and `ℓ_T` the minimum over those
with a single walk.  The content is that **the relaxed minimum is attained by a
one-walk realisation** -- everything else is the trivial inclusion.

Note what is *not* used: the metric identity `ℓ_T = ℓ_R + 2c`, whose lower bound is
open.  Only `ℓ_T ≤ ℓ_R` is needed, and it comes from the exhibited realisation. -/
theorem travel_minima_agree (up : Fin n → ℕ) (dep trav : Fin n → ℤ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hf : ∀ e, EdgeData.IsTravel (trav e))
    (hpar : ∀ e, (dep e - trav e) % 2 = 0)
    (hmdef : ∀ e, m e = (max |dep e| |trav e|).toNat)
    (hng : ∀ e, ¬ EdgeData.IsGap (dep e) (trav e))
    (e0 : Fin n) (ds : Bool → Bool) :
    ∃ D' : Data (Endpt n m),
      WalkSupport.Merges siteOf (isArrOf up) partner D' ∧
      walkCount D' = 1 ∧
      -- `D'` attains the relaxed minimum `ℓ_R`
      (∀ F : Data (Endpt n m), WalkSupport.Merges siteOf (isArrOf up) partner F →
        CostMerge.costOf (endDataOf (m := m) up ds) D' ≤ CostMerge.costOf (endDataOf (m := m) up ds) F) ∧
      -- and a fortiori the true minimum `ℓ_T`, over single-walk realisations
      (∀ F : Data (Endpt n m), WalkSupport.Merges siteOf (isArrOf up) partner F →
        walkCount F = 1 →
        CostMerge.costOf (endDataOf (m := m) up ds) D' ≤ CostMerge.costOf (endDataOf (m := m) up ds) F) := by
  obtain ⟨D', ⟨hM, hmin⟩, hone, _⟩ := cor_localzero up dep trav hbal hf hpar hmdef hng e0 ds
  exact ⟨D', hM, hone, hmin, fun F hF _ => hmin F hF⟩

/-! ### Occupancy

`prop:cut`'s counting step needs every site of the span to carry an end.  A site `s`
carries one exactly when edge `s` has a crossing (its bottom end sits at `s`) or edge
`s - 1` does (its top end sits at `s`).  So occupancy fails only where **two adjacent
gap edges** meet -- a condition on the configuration, not a consequence of anything
proved here, and it is carried as a hypothesis rather than assumed away. -/

/-- A crossing on edge `e` puts an end at site `e` (its bottom). -/
theorem site_occupied_bottom (e : Fin n) (he : 0 < m e) :
    ∃ x : Endpt n m, siteOf x = (e : ℤ) := by
  refine ⟨⟨e, ⟨0, he⟩, false⟩, ?_⟩
  unfold siteOf edgeOf atTop
  simp

/-- A crossing on edge `e` also puts an end at site `e + 1` (its top). -/
theorem site_occupied_top (e : Fin n) (he : 0 < m e) :
    ∃ x : Endpt n m, siteOf x = (e : ℤ) + 1 := by
  refine ⟨⟨e, ⟨0, he⟩, true⟩, ?_⟩
  unfold siteOf edgeOf atTop
  simp

/-! ### The cut condition, from its actual definition

`prop:cut` calls a site of the span **cut** when `α_s = β_s = Φ_s = 0`, and takes `Z`
to be the cut sites *interior* to the span.  Since `SiteCost.siteValue` is exactly
`max (|α|, |β|, |Φ|)`, being cut is the same as that value vanishing -- so the paper's
`Z` is the set of interior sites of zero site-value.

This is the correct foundation, replacing the shifted gap edges retracted above. -/

/-- **Cut is exactly zero site-value.** -/
theorem isCut_iff_siteValue_zero (Ap Am Bp Bm Cp Cm Dp Dm : ℕ) :
    SiteCost.siteValue Ap Am Bp Bm Cp Cm Dp Dm = 0 ↔
      (SiteCost.alpha Ap Am Cp Cm = 0 ∧ SiteCost.beta Bp Bm Dp Dm = 0 ∧
        SiteCost.Phi Ap Am Cp Cm = 0) := by
  unfold SiteCost.siteValue
  rw [Nat.max_eq_zero_iff, Nat.max_eq_zero_iff, Int.natAbs_eq_zero, Int.natAbs_eq_zero,
    Int.natAbs_eq_zero]
  tauto

/-- A cut site costs nothing, since the site cost is its value. -/
theorem cut_site_value (Ap Am Bp Bm Cp Cm Dp Dm : ℕ)
    (h : SiteCost.alpha Ap Am Cp Cm = 0) (h2 : SiteCost.beta Bp Bm Dp Dm = 0)
    (h3 : SiteCost.Phi Ap Am Cp Cm = 0) :
    SiteCost.siteValue Ap Am Bp Bm Cp Cm Dp Dm = 0 :=
  (isCut_iff_siteValue_zero Ap Am Bp Bm Cp Cm Dp Dm).mpr ⟨h, h2, h3⟩

/-! ### `Local` with the right position function

**CORRECTION (2026-08-23).**  `walk_graph_local` above uses `pos = siteOf`.  That is
the wrong choice, and it is why its gap hypothesis looked unnatural.

A strand crosses site `s` when it goes from edge `s-1` to edge `s`, which in the walk
graph is a **turn** at site `s`.  A **crossing** edge joins the two ends of one
crossing and stays on a single edge.  So the position of an end is its **edge**, and:

* a crossing edge does not move `pos` -- the condition is vacuous on it;
* a turn edge at site `s` joins an end of edge `s-1` to an end of edge `s`, moving
  `pos` from `s-1` to `s`, and `Local` then demands `s ∉ Z`.

That demand is exactly `prop:cut`'s first sentence: *at a cut site every minimum-cost
pairing matches each arrival with a departure on its own side, so no strand crosses
`s`*.  It is a theorem about minimum-cost pairings, carried here as a hypothesis. -/
theorem walk_graph_local_edge (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (Zf : Finset ℤ)
    (hturn : ∀ x : Endpt n m, edgeOf (turn up x) ≠ edgeOf x → siteOf x ∉ Zf) :
    CutComponents.Local (graph (dataOf up hbal)) edgeOf Zf := by
  intro x y hxy
  rcases hxy with h | h
  · -- a crossing edge: both ends lie on the same edge, so `pos` does not move
    subst h
    exact ⟨edgeOf x, Or.inr rfl, Or.inr (partner_edgeOf x), fun hne =>
      absurd (partner_edgeOf x).symm hne⟩
  · -- a turn edge: the two ends lie on edges `s - 1` and `s` for `s` the site
    subst h
    refine ⟨siteOf x, ?_, ?_, fun hne => hturn x (Ne.symm hne)⟩
    · unfold siteOf edgeOf atTop; cases x.top <;> simp
    · have h2 : siteOf ((dataOf up hbal).t x) = siteOf x := turnAt_site up hbal x
      have h3 : edgeOf ((dataOf up hbal).t x)
          + (if atTop ((dataOf up hbal).t x) then (1:ℤ) else 0)
          = siteOf ((dataOf up hbal).t x) := rfl
      cases hb : atTop ((dataOf up hbal).t x)
      · right; rw [hb] at h3; simp at h3; omega
      · left; rw [hb] at h3; simp at h3; omega

/-! ### `Z`, correctly

The cut sites of the span: `d_{s-1} = 0`, `d_s = 0`, `f_{s-1} = 0`.  All three
conditions, unlike the retracted `gapSites`, which omitted `d_s = 0` and so counted
one site too many per gap run. -/

/-- The paper's `Z`: the cut sites interior to the span `[A, B]`.

**CORRECTION (2026-08-23).**  An earlier version omitted `s ≠ 0` and `s ≠ kstar`.
`SiteCost.PathData.cut` is `α_s = β_s = Φ_s = 0`, and

  α_s = d(s-1) - vArr s + ε·vL s,  β_s = d s - ε·vR s,  Φ_s = f(s-1) + vArr s - vL s

where `vArr s = [s = 0]` and `vL, vR` vanish off `s = kstar`.  So the plain conditions
`d(s-1) = d s = f(s-1) = 0` characterise cut **only away from the two virtual events**
-- exactly the `hnov` hypothesis of `Realisation.gap_run_cut`.  Without it a site
carrying a virtual event could be counted as cut when it is not. -/
noncomputable def cutSitesZ (d f : ℤ → ℤ) (kstar : ℤ) (A B : ℤ) : Finset ℤ :=
  (Finset.Icc A B).filter
    (fun s => s ≠ 0 ∧ s ≠ kstar ∧ d (s - 1) = 0 ∧ d s = 0 ∧ f (s - 1) = 0)

theorem mem_cutSitesZ {d f : ℤ → ℤ} {kstar A B s : ℤ} :
    s ∈ cutSitesZ d f kstar A B ↔
      (A ≤ s ∧ s ≤ B) ∧ s ≠ 0 ∧ s ≠ kstar ∧
        d (s - 1) = 0 ∧ d s = 0 ∧ f (s - 1) = 0 := by
  simp [cutSitesZ, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- **`prop:cut` with the correct `Z` and position function.**  At least `|Z|` walks
carry neither virtual event.

The two inputs are the ones the paper argues for: no strand crosses a cut site
(`hturn`, its first sentence), and every edge of the span carries a crossing (`hocc`,
which `m ≥ 2` on `f = 0` edges supplies). -/
theorem prop_cut_correct (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (d f : ℤ → ℤ) (kstar A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ cutSitesZ d f kstar A B, A < z) (hhigh : ∀ z ∈ cutSitesZ d f kstar A B, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : Endpt n m, edgeOf x = t)
    (hturn : ∀ x : Endpt n m, edgeOf (turn up x) ≠ edgeOf x →
      siteOf x ∉ cutSitesZ d f kstar A B)
    (c0 : (graph (dataOf up hbal)).ConnectedComponent) :
    ∃ F : Fin (cutSitesZ d f kstar A B).card → (graph (dataOf up hbal)).ConnectedComponent,
      Function.Injective F ∧ ∀ i, F i ≠ c0 :=
  CutComponents.exists_injective_components_avoiding
    (walk_graph_local_edge up hbal (cutSitesZ d f kstar A B) hturn)
    A B hAB hlow hhigh hocc c0

/-! ### No strand crosses a cut site

`Plan.cost` is `2·(same-side sign flips) + cross`, so the cross mass never exceeds the
cost.  At a cut site the site value is `0`, so a minimum-cost plan costs `0` and
therefore crosses `0` times -- which is `prop:cut`'s first sentence, and the `hturn`
input of `prop_cut_correct`. -/

theorem cross_le_cost {Ap Am Bp Bm Cp Cm Dp Dm : ℕ}
    (p : SiteCost.Plan Ap Am Bp Bm Cp Cm Dp Dm) : p.cross ≤ p.cost := by
  unfold SiteCost.Plan.cost SiteCost.Plan.cross
  omega

/-- **At a cut site no strand crosses.**  A zero-cost plan has zero cross mass. -/
theorem cross_eq_zero_of_cost_zero {Ap Am Bp Bm Cp Cm Dp Dm : ℕ}
    (p : SiteCost.Plan Ap Am Bp Bm Cp Cm Dp Dm) (h : p.cost = 0) : p.cross = 0 := by
  have := cross_le_cost p
  omega

/-- The same, read off the cut condition: `α = β = Φ = 0` makes the site value zero,
so any plan attaining it costs nothing and crosses nothing. -/
theorem no_cross_at_cut {Ap Am Bp Bm Cp Cm Dp Dm : ℕ}
    (p : SiteCost.Plan Ap Am Bp Bm Cp Cm Dp Dm)
    (halpha : SiteCost.alpha Ap Am Cp Cm = 0) (hbeta : SiteCost.beta Bp Bm Dp Dm = 0)
    (hphi : SiteCost.Phi Ap Am Cp Cm = 0)
    (hmin : p.cost = SiteCost.siteValue Ap Am Bp Bm Cp Cm Dp Dm) :
    p.cross = 0 :=
  cross_eq_zero_of_cost_zero p
    (by rw [hmin, cut_site_value Ap Am Bp Bm Cp Cm Dp Dm halpha hbeta hphi])

/-! ### A `Plan` from a turn

`SiteCost.Plan` is a 4x4 transportation matrix whose rows count arrivals by class and
whose columns count departures by class.  A turn at a site is a bijection from the
arrivals there to the departures, so setting `x_ij` to the number of class-`i`
arrivals whose turn lands in class `j` gives a plan.

The row equations are fiberwise counting; the column equations are the same on the
departures, through the inverse.  Both are recorded here as the general counting
step, which is what the construction rests on. -/

/-- **Rows.**  Splitting a class by where its turn lands recovers the class count. -/
theorem row_sum_of_fiber {β : Type*} [DecidableEq β] [Fintype β]
    (S : Finset β) (cls : β → Fin 4) :
    ∑ j : Fin 4, (S.filter (fun a => cls a = j)).card = S.card :=
  (Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (cls a))).symm

/-- **Columns.**  The same count taken through a bijection: if `t` maps `S` onto `T`
injectively, the fibres of `cls ∘ t` over `S` have the same cardinalities as the
fibres of `cls` over `T`. -/
theorem col_sum_of_bij {β : Type*} [DecidableEq β] [Fintype β]
    (S T : Finset β) (t : β → β) (cls : β → Fin 4)
    (hmaps : ∀ a ∈ S, t a ∈ T) (hinj : Set.InjOn t S)
    (hsurj : ∀ b ∈ T, ∃ a ∈ S, t a = b) (j : Fin 4) :
    (S.filter (fun a => cls (t a) = j)).card = (T.filter (fun b => cls b = j)).card := by
  refine Finset.card_bij (fun a _ => t a) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨hmaps a ha.1, ha.2⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    exact hinj ha.1 hb.1 hab
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨a, haS, hab⟩ := hsurj b hb.1
    exact ⟨a, Finset.mem_filter.mpr ⟨haS, by rw [hab]; exact hb.2⟩, hab⟩

/-- The transportation entry: class-`i` arrivals whose turn lands in class `j`. -/
noncomputable def xEntry {β : Type*} [DecidableEq β] [Fintype β]
    (S : Finset β) (t : β → β) (cls : β → Fin 4) (i j : Fin 4) : ℕ := by
  classical
  exact (S.filter (fun a => cls a = i ∧ cls (t a) = j)).card

/-- **Row equation.**  Summing an arrival class over the classes its turns land in
recovers that class's count. -/
theorem xEntry_row {β : Type*} [DecidableEq β] [Fintype β]
    (S : Finset β) (t : β → β) (cls : β → Fin 4) (i : Fin 4) :
    ∑ j : Fin 4, xEntry S t cls i j = (S.filter (fun a => cls a = i)).card := by
  classical
  rw [← row_sum_of_fiber (S.filter (fun a => cls a = i)) (fun a => cls (t a))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold xEntry
  rw [Finset.filter_filter]

/-- **Column equation.**  Summing a departure class over the arrival classes that feed
it recovers that class's count, through the bijection. -/
theorem xEntry_col {β : Type*} [DecidableEq β] [Fintype β]
    (S T : Finset β) (t : β → β) (cls : β → Fin 4)
    (hmaps : ∀ a ∈ S, t a ∈ T) (hinj : Set.InjOn t S)
    (hsurj : ∀ b ∈ T, ∃ a ∈ S, t a = b) (j : Fin 4) :
    ∑ i : Fin 4, xEntry S t cls i j = (T.filter (fun b => cls b = j)).card := by
  classical
  have h1 : ∑ i : Fin 4, xEntry S t cls i j
      = (S.filter (fun a => cls (t a) = j)).card := by
    rw [← row_sum_of_fiber (S.filter (fun a => cls (t a) = j)) cls]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold xEntry
    rw [Finset.filter_filter]
    congr 1
    ext a
    simp [and_comm]
  rw [h1]
  exact col_sum_of_bij S T t cls hmaps hinj hsurj j

/-- **A `Plan` from a turn.**  The transportation plan whose entry `(i, j)` counts the
class-`i` arrivals whose turn lands in class `j`.  Its eight constraints are the row
and column equations above. -/
noncomputable def planOfTurn {β : Type*} [DecidableEq β] [Fintype β]
    (S T : Finset β) (t : β → β) (cls : β → Fin 4)
    (hmaps : ∀ a ∈ S, t a ∈ T) (hinj : Set.InjOn t S)
    (hsurj : ∀ b ∈ T, ∃ a ∈ S, t a = b) :
    SiteCost.Plan
      (S.filter (fun a => cls a = 0)).card (S.filter (fun a => cls a = 1)).card
      (S.filter (fun a => cls a = 2)).card (S.filter (fun a => cls a = 3)).card
      (T.filter (fun b => cls b = 0)).card (T.filter (fun b => cls b = 1)).card
      (T.filter (fun b => cls b = 2)).card (T.filter (fun b => cls b = 3)).card where
  x00 := xEntry S t cls 0 0
  x01 := xEntry S t cls 0 1
  x02 := xEntry S t cls 0 2
  x03 := xEntry S t cls 0 3
  x10 := xEntry S t cls 1 0
  x11 := xEntry S t cls 1 1
  x12 := xEntry S t cls 1 2
  x13 := xEntry S t cls 1 3
  x20 := xEntry S t cls 2 0
  x21 := xEntry S t cls 2 1
  x22 := xEntry S t cls 2 2
  x23 := xEntry S t cls 2 3
  x30 := xEntry S t cls 3 0
  x31 := xEntry S t cls 3 1
  x32 := xEntry S t cls 3 2
  x33 := xEntry S t cls 3 3
  row0 := by have h := xEntry_row S t cls 0; rwa [Fin.sum_univ_four] at h
  row1 := by have h := xEntry_row S t cls 1; rwa [Fin.sum_univ_four] at h
  row2 := by have h := xEntry_row S t cls 2; rwa [Fin.sum_univ_four] at h
  row3 := by have h := xEntry_row S t cls 3; rwa [Fin.sum_univ_four] at h
  col0 := by have h := xEntry_col S T t cls hmaps hinj hsurj 0; rwa [Fin.sum_univ_four] at h
  col1 := by have h := xEntry_col S T t cls hmaps hinj hsurj 1; rwa [Fin.sum_univ_four] at h
  col2 := by have h := xEntry_col S T t cls hmaps hinj hsurj 2; rwa [Fin.sum_univ_four] at h
  col3 := by have h := xEntry_col S T t cls hmaps hinj hsurj 3; rwa [Fin.sum_univ_four] at h

/-- An arrival contributes to its own entry, so that entry is non-zero. -/
theorem xEntry_ne_zero {β : Type*} [DecidableEq β] [Fintype β]
    (S : Finset β) (t : β → β) (cls : β → Fin 4) {a : β} (ha : a ∈ S) :
    xEntry S t cls (cls a) (cls (t a)) ≠ 0 := by
  classical
  unfold xEntry
  intro hzero
  rw [Finset.card_eq_zero] at hzero
  have hmem : a ∈ S.filter (fun b => cls b = cls a ∧ cls (t b) = cls (t a)) :=
    Finset.mem_filter.mpr ⟨ha, rfl, rfl⟩
  rw [hzero] at hmem
  exact absurd hmem (Finset.notMem_empty a)

/-- **Zero cross mass means no turn changes side.**  Classes `0, 1` are the left side
and `2, 3` the right, and `Plan.cross` is exactly the eight entries that move between
them -- so if it vanishes, every arrival's turn stays on its own side. -/
theorem no_side_change_of_cross_zero {β : Type*} [DecidableEq β] [Fintype β]
    (S T : Finset β) (t : β → β) (cls : β → Fin 4)
    (hmaps : ∀ a ∈ S, t a ∈ T) (hinj : Set.InjOn t S)
    (hsurj : ∀ b ∈ T, ∃ a ∈ S, t a = b)
    (h : (planOfTurn S T t cls hmaps hinj hsurj).cross = 0) :
    ∀ a ∈ S, ((cls a : ℕ) < 2 ↔ ((cls (t a) : ℕ) < 2)) := by
  intro a ha
  -- all eight crossing entries vanish
  have hz : ∀ i j : Fin 4, ((i : ℕ) < 2 ∧ 2 ≤ (j : ℕ)) ∨ (2 ≤ (i : ℕ) ∧ (j : ℕ) < 2) →
      xEntry S t cls i j = 0 := by
    have hc : (planOfTurn S T t cls hmaps hinj hsurj).cross
        = (xEntry S t cls 0 2 + xEntry S t cls 0 3 + xEntry S t cls 1 2 + xEntry S t cls 1 3)
          + (xEntry S t cls 2 0 + xEntry S t cls 2 1 + xEntry S t cls 3 0
             + xEntry S t cls 3 1) := rfl
    rw [hc] at h
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  by_contra hcon
  exact xEntry_ne_zero S t cls ha (hz _ _ (by omega))

/-! ### The plan at a site of a configuration

`planOfTurn` instantiated with the site's arrivals and departures and the local turn.
The class of an end is its side and its sign: top ends belong to the left edge, so
they are classes `0, 1`, and bottom ends to the right edge, classes `2, 3`. -/

/-- The four classes at a site: `(L,+) (L,-) (R,+) (R,-)`. -/
def clsOf (up : Fin n → ℕ) (ds : Bool → Bool) (x : Endpt n m) : Fin 4 :=
  (if atTop x then 0 else 2) + (if EndData.sgn (endDataOf (m := m) up ds) x then 0 else 1)

/-- The local turn is injective. -/
theorem turnAt_injOn (up : Fin n → ℕ) (s : ℤ) (S : Finset (Endpt n m)) :
    Set.InjOn (turnAt up s) (S : Set (Endpt n m)) := by
  intro a _ b _ hab
  have h := congrArg (turnAt up s) hab
  rwa [turnAt_invol up s a, turnAt_invol up s b] at h

/-- Every departure at a site is the turn of an arrival there. -/
theorem turnAt_surjOn (up : Fin n → ℕ) (s : ℤ)
    (h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    ∀ b ∈ depAt (m := m) up s, ∃ a ∈ arrAt (m := m) up s, turnAt up s a = b := by
  intro b hb
  exact ⟨turnAt up s b, turnAt_dep up s h b hb, turnAt_invol up s b⟩

/-- **The plan at a site.** -/
noncomputable def planAt (up : Fin n → ℕ) (ds : Bool → Bool) (s : ℤ)
    (h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    SiteCost.Plan
      ((arrAt (m := m) up s).filter (fun a => clsOf up ds a = 0)).card
      ((arrAt (m := m) up s).filter (fun a => clsOf up ds a = 1)).card
      ((arrAt (m := m) up s).filter (fun a => clsOf up ds a = 2)).card
      ((arrAt (m := m) up s).filter (fun a => clsOf up ds a = 3)).card
      ((depAt (m := m) up s).filter (fun b => clsOf up ds b = 0)).card
      ((depAt (m := m) up s).filter (fun b => clsOf up ds b = 1)).card
      ((depAt (m := m) up s).filter (fun b => clsOf up ds b = 2)).card
      ((depAt (m := m) up s).filter (fun b => clsOf up ds b = 3)).card :=
  planOfTurn (arrAt (m := m) up s) (depAt (m := m) up s) (turnAt up s) (clsOf up ds)
    (turnAt_arr up s h) (turnAt_injOn up s _) (turnAt_surjOn up s h)

/-! ### Side change is edge change

At a site `s` an end is either a top end, on edge `s - 1`, or a bottom end, on edge
`s`.  So two ends at the same site lie on the same edge exactly when they are on the
same side -- which turns `no_side_change_of_cross_zero` into `hturn`. -/

/-- The class's side bit is `atTop`. -/
theorem clsOf_lt_two_iff (up : Fin n → ℕ) (ds : Bool → Bool) (x : Endpt n m) :
    ((clsOf up ds x : ℕ) < 2 ↔ atTop x = true) := by
  unfold clsOf
  cases hx : atTop x <;>
    cases EndData.sgn (endDataOf (m := m) up ds) x <;> simp

/-- At a site, the side determines the edge. -/
theorem edge_of_site (x : Endpt n m) (s : ℤ) (hs : siteOf x = s) :
    edgeOf x = if atTop x then s - 1 else s := by
  have h : edgeOf x + (if atTop x then (1:ℤ) else 0) = s := hs
  cases hx : atTop x <;> simp [hx] at h ⊢ <;> omega

/-- **Same site and same side gives the same edge.** -/
theorem same_edge_of_same_side (x y : Endpt n m) (s : ℤ)
    (hsx : siteOf x = s) (hsy : siteOf y = s) (h : atTop x = atTop y) :
    edgeOf x = edgeOf y := by
  rw [edge_of_site x s hsx, edge_of_site y s hsy, h]

/-- **`hturn` at a cut site.**  If the site's plan has no cross mass then no turn
there moves between the two adjacent edges.

This is the last link: `no_side_change_of_cross_zero` gives that the turn preserves
the class's side bit, `clsOf_lt_two_iff` identifies that bit with `atTop`, and
`same_edge_of_same_side` turns equal sides at one site into equal edges. -/
theorem turn_keeps_edge_of_cross_zero (up : Fin n → ℕ) (ds : Bool → Bool) (s : ℤ)
    (h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hcross : (planAt up ds s h).cross = 0) :
    ∀ x ∈ arrAt (m := m) up s, edgeOf (turnAt up s x) = edgeOf x := by
  intro x hx
  have hside := no_side_change_of_cross_zero (arrAt (m := m) up s) (depAt (m := m) up s)
    (turnAt up s) (clsOf up ds) (turnAt_arr up s h) (turnAt_injOn up s _)
    (turnAt_surjOn up s h) hcross x hx
  rw [clsOf_lt_two_iff, clsOf_lt_two_iff] at hside
  -- the arrival and its departure sit at the same site
  have hsx : siteOf x = s := ((EndType.mem_arrAt up s x).mp hx).1
  have hst : siteOf (turnAt up s x) = s :=
    ((EndType.mem_depAt up s _).mp (turnAt_arr up s h x hx)).1
  refine same_edge_of_same_side _ _ s hst hsx ?_
  cases hax : atTop x <;> cases hat : atTop (turnAt up s x) <;> simp_all

/-! ### Summing by class pair

A cost that depends only on the pair of classes `(cls a, cls (t a))` sums to the
transportation entries weighted by that cost.  This is what identifies the site's
contribution to `costOf` with its plan's `Plan.cost`. -/

/-- **A class-pair-determined cost sums to the weighted entries.** -/
theorem sum_by_class_pair {β : Type*} [DecidableEq β] [Fintype β]
    (A : Finset β) (t : β → β) (cls : β → Fin 4) (f : β → ℤ) (w : Fin 4 → Fin 4 → ℤ)
    (hf : ∀ a ∈ A, f a = w (cls a) (cls (t a))) :
    ∑ a ∈ A, f a = ∑ i : Fin 4, ∑ j : Fin 4, (xEntry A t cls i j : ℤ) * w i j := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := cls) (fun a _ => Finset.mem_univ (cls a)) f]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun a => cls (t a))
    (fun a _ => Finset.mem_univ (cls (t a))) f]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hblock : (A.filter (fun a => cls a = i)).filter (fun a => cls (t a) = j)
      = A.filter (fun a => cls a = i ∧ cls (t a) = j) := Finset.filter_filter _ _ _
  rw [hblock]
  have hconst : ∀ a ∈ A.filter (fun a => cls a = i ∧ cls (t a) = j), f a = w i j := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [hf a ha.1, ha.2.1, ha.2.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  unfold xEntry
  rfl

/-- The pairing cost as a function of the two classes: `0` on the same side with the
same sign, `2` on the same side with opposite signs, `1` across. -/
def pcostW (i j : Fin 4) : ℤ :=
  if ((i : ℕ) < 2 ↔ (j : ℕ) < 2) then (if i = j then 0 else 2) else 1

/-- **The weighted entries are exactly `Plan.cost`.** -/
theorem weighted_sum_eq_cost (x : Fin 4 → Fin 4 → ℕ) :
    ∑ i : Fin 4, ∑ j : Fin 4, (x i j : ℤ) * pcostW i j
      = 2 * ((x 0 1 : ℤ) + x 1 0) + 2 * ((x 2 3 : ℤ) + x 3 2)
        + (((x 0 2 : ℤ) + x 0 3 + x 1 2 + x 1 3) + ((x 2 0 : ℤ) + x 2 1 + x 3 0 + x 3 1)) := by
  simp [Fin.sum_univ_four, pcostW]
  ring

/-- The class determines, and is determined by, the side and the sign. -/
theorem clsOf_eq_iff (up : Fin n → ℕ) (ds : Bool → Bool) (a b : Endpt n m) :
    clsOf up ds a = clsOf up ds b ↔
      (atTop a = atTop b ∧
        EndData.sgn (endDataOf (m := m) up ds) a
          = EndData.sgn (endDataOf (m := m) up ds) b) := by
  unfold clsOf
  cases atTop a <;> cases atTop b <;>
    cases EndData.sgn (endDataOf (m := m) up ds) a <;>
    cases EndData.sgn (endDataOf (m := m) up ds) b <;> simp

/-- **The pairing cost is the class-pair weight.**  `pcostF` splits on side then sign,
and `clsOf` encodes exactly those two bits. -/
theorem pcostF_eq_pcostW (up : Fin n → ℕ) (ds : Bool → Bool) (a b : Endpt n m) :
    EndData.pcostF (endDataOf (m := m) up ds) a b
      = pcostW (clsOf up ds a) (clsOf up ds b) := by
  unfold EndData.pcostF pcostW
  have hside : ((clsOf up ds a : ℕ) < 2 ↔ (clsOf up ds b : ℕ) < 2)
      ↔ ((endDataOf (m := m) up ds).side a = (endDataOf (m := m) up ds).side b) := by
    rw [clsOf_lt_two_iff, clsOf_lt_two_iff]
    show _ ↔ (atTop a = atTop b)
    cases atTop a <;> cases atTop b <;> simp
  rw [if_congr hside rfl rfl]
  by_cases hs : (endDataOf (m := m) up ds).side a = (endDataOf (m := m) up ds).side b
  · rw [if_pos hs, if_pos hs]
    congr 1
    rw [eq_iff_iff, clsOf_eq_iff]
    exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩
  · rw [if_neg hs, if_neg hs]

/-- **The site's cost contribution is its plan's cost.**  This is what makes
site-wise minimality of `costOf` the same thing as the site's plan being
minimum-cost. -/
theorem site_sum_eq_plan_cost (up : Fin n → ℕ) (ds : Bool → Bool) (s : ℤ)
    (h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    ∑ a ∈ arrAt (m := m) up s,
        EndData.pcostF (endDataOf (m := m) up ds) a (turnAt up s a)
      = ((planAt up ds s h).cost : ℤ) := by
  classical
  rw [sum_by_class_pair (arrAt (m := m) up s) (turnAt up s) (clsOf up ds) _ pcostW
    (fun a _ => pcostF_eq_pcostW up ds a _)]
  rw [weighted_sum_eq_cost (fun i j => xEntry (arrAt (m := m) up s) (turnAt up s)
    (clsOf up ds) i j)]
  simp only [SiteCost.Plan.cost, planAt, planOfTurn]
  push_cast
  ring

/-! ### `prop:cut`, assembled

The paper: *at a cut site every minimum-cost pairing matches each arrival with a
departure on its own side, so no strand crosses `s`; consequently every minimum-cost
realisation has at least `|Z| + 1` components and `c ≥ |Z|`.*

Below, with the cut sites' plans known to have no cross mass -- which is what
`no_cross_at_cut` gives once the site's plan is minimum-cost, and
`site_sum_eq_plan_cost` together with `site_cost_le_of_global` supplies that from
global minimality. -/

/-- The turn keeps its edge at a cut site, for **every** end, arrival or departure:
a departure's turn is an arrival at the same site, and the two share their turn edge. -/
theorem turn_keeps_edge_all (up : Fin n → ℕ) (ds : Bool → Bool)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (s : ℤ) (hcross : (planAt up ds s (hbal s)).cross = 0)
    (x : Endpt n m) (hx : siteOf x = s) :
    edgeOf (turnAt up s x) = edgeOf x := by
  by_cases ha : isArrOf up x = true
  · exact turn_keeps_edge_of_cross_zero up ds s (hbal s) hcross x
      ((EndType.mem_arrAt up s x).mpr ⟨hx, ha⟩)
  · -- a departure: apply the arrival case to its turn, then use the involution
    simp only [Bool.not_eq_true] at ha
    have hxd : x ∈ depAt (m := m) up s := (EndType.mem_depAt up s x).mpr ⟨hx, ha⟩
    have haa : turnAt up s x ∈ arrAt (m := m) up s := turnAt_dep up s (hbal s) x hxd
    have := turn_keeps_edge_of_cross_zero up ds s (hbal s) hcross _ haa
    rw [turnAt_invol up s x] at this
    exact this.symm
    
/-- **`prop:cut`, assembled.**  At least `|Z|` walks carry neither virtual event.

The one hypothesis about the realisation is `hcut`: at each cut site the plan has no
cross mass.  That is what global cost-minimality delivers, through
`site_cost_le_of_global` and `site_sum_eq_plan_cost` to `no_cross_at_cut`. -/
theorem prop_cut_assembled (up : Fin n → ℕ) (ds : Bool → Bool)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (d f : ℤ → ℤ) (kstar A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ cutSitesZ d f kstar A B, A < z) (hhigh : ∀ z ∈ cutSitesZ d f kstar A B, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : Endpt n m, edgeOf x = t)
    (hcut : ∀ s ∈ cutSitesZ d f kstar A B, (planAt up ds s (hbal s)).cross = 0)
    (c0 : (graph (dataOf up hbal)).ConnectedComponent) :
    ∃ F : Fin (cutSitesZ d f kstar A B).card → (graph (dataOf up hbal)).ConnectedComponent,
      Function.Injective F ∧ ∀ i, F i ≠ c0 := by
  refine prop_cut_correct up hbal d f kstar A B hAB hlow hhigh hocc ?_ c0
  intro x hne hmem
  exact hne (turn_keeps_edge_all up ds hbal (siteOf x) (hcut _ hmem) x rfl)

/-! ### `cutSitesZ` agrees with `PathData.cut`

Away from the two virtual events the three quantities reduce to the deposits and the
travel indicator, so the two definitions of *cut* coincide.  Proving it turns the
correspondence into a theorem, which is what both `gapSites` attempts lacked. -/

/-- **Away from the virtual events, `cut` is the plain condition.** -/
theorem cut_iff_plain (P : SiteCost.PathData) (s : ℤ) (h0 : s ≠ 0) (hk : s ≠ P.kstar) :
    P.cut s ↔ (P.d (s - 1) = 0 ∧ P.d s = 0 ∧ P.f (s - 1) = 0) := by
  unfold SiteCost.PathData.cut SiteCost.PathData.alphaAt SiteCost.PathData.betaAt
    SiteCost.PathData.PhiAt SiteCost.PathData.vL SiteCost.PathData.vR
    SiteCost.PathData.vD SiteCost.vArr
  rw [if_neg h0, if_neg hk]
  cases P.delta <;> simp

/-- **The set matches.**  A site of the span lies in `cutSitesZ` exactly when it is a
cut site with no virtual event. -/
theorem mem_cutSitesZ_iff_cut (P : SiteCost.PathData) (A B s : ℤ) :
    s ∈ cutSitesZ P.d P.f P.kstar A B ↔
      ((A ≤ s ∧ s ≤ B) ∧ s ≠ 0 ∧ s ≠ P.kstar ∧ P.cut s) := by
  rw [mem_cutSitesZ]
  constructor
  · rintro ⟨hs, h0, hk, hd1, hd2, hf⟩
    exact ⟨hs, h0, hk, (cut_iff_plain P s h0 hk).mpr ⟨hd1, hd2, hf⟩⟩
  · rintro ⟨hs, h0, hk, hcut⟩
    obtain ⟨hd1, hd2, hf⟩ := (cut_iff_plain P s h0 hk).mp hcut
    exact ⟨hs, h0, hk, hd1, hd2, hf⟩

/-! ### Why the merge chain and `prop:cut` do not conflict

`min_merges_to_one` merges a cost-minimal datum to **one** walk at unchanged cost,
while `prop:cut` says every minimum-cost realisation has at least `|Z| + 1`
components.  With `Z ≠ ∅` those would conflict.  They do not, and the reason is
sharp: **a cut site carries no ends at all**, so the merge chain's covering
hypothesis already excludes cut sites.

`EndData.sgn` *derives* the sign from the side and the role, so on one side every
arrival carries one sign and every departure the opposite.  Writing `A` for the left
arrivals and `C` for the left departures, that makes `α = -(A + C)`, and `α = 0`
forces `A = C = 0` -- there is nothing at the site.  The chain assumes `0 < m e` at
every edge, which puts ends at every site, so it never meets one. -/

/-- **A cut site carries no ends**, in the derived sign model: with all left arrivals
of one sign and all left departures of the other, `α = 0` forces both counts to
vanish. -/
theorem no_ends_of_alpha_zero (A C : ℕ)
    (h : SiteCost.alpha A 0 0 C = 0) : A = 0 ∧ C = 0 := by
  unfold SiteCost.alpha at h
  omega

/-- The same on the right, from `β`. -/
theorem no_ends_of_beta_zero (B D : ℕ)
    (h : SiteCost.beta B 0 0 D = 0) : B = 0 ∧ D = 0 := by
  unfold SiteCost.beta at h
  omega

/-! ### Covering on a run

`c ≤ |Z|` says the cut sites are the only obstruction.  The descent's covering
hypothesis currently asks for a crossing on *every* edge, which forces `Z = ∅`.
Restricting it to a run between cut sites is the first step: on such a run the
multiplicities are positive, so the covering holds there. -/

/-- **Covering within a run.**  If every edge of `[l, r]` carries a crossing then the
edge immediately left of any `j` in `(l, r]` carries a top end. -/
theorem covering_on_run (l r : ℤ) (hl : 0 ≤ l)
    (hpos : ∀ e : Fin n, l ≤ (e : ℤ) → (e : ℤ) ≤ r → 0 < m e) :
    ∀ j : ℤ, l < j → j ≤ r → (∃ u : Endpt n m, edgeOf u = j) →
      ∃ y : Endpt n m, edgeOf y = j - 1 ∧ atTop y = true := by
  rintro j hlj hjr ⟨u, hu⟩
  -- `j` is an edge index, so `j - 1` is one too
  have hjn : j < (n : ℤ) := by
    rw [← hu]; unfold edgeOf; exact_mod_cast u.edge.isLt
  have hl0 : (0 : ℤ) ≤ j - 1 := by omega
  have hlt : (j - 1).toNat < n := by omega
  have hcast : (((⟨(j - 1).toNat, hlt⟩ : Fin n) : ℕ) : ℤ) = j - 1 := by
    show ((j - 1).toNat : ℤ) = j - 1
    omega
  have hm : 0 < m ⟨(j - 1).toNat, hlt⟩ :=
    hpos _ (by rw [hcast]; omega) (by rw [hcast]; omega)
  exact ⟨⟨⟨(j - 1).toNat, hlt⟩, ⟨0, hm⟩, true⟩, hcast, rfl⟩

/-- **The second walk's end, produced within a run.**  `WalkSupport.other_end_at_wLo`
with its global covering hypothesis replaced by `covering_on_run`: the maximiser's
leftmost edge need only lie inside a run whose edges all carry crossings, not in a
configuration free of gaps everywhere. -/
theorem other_end_at_wLo_run (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (l r : ℤ) (hl : 0 ≤ l)
    (hpos : ∀ e : Fin n, l ≤ (e : ℤ) → (e : ℤ) ≤ r → 0 < m e)
    (z z' : Endpt n m)
    (hsplit : ¬ (graph (dataOf up hbal)).Reachable z z')
    (hle : WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z'
      ≤ WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z)
    (hlz : l < WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z)
    (hzr : WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z ≤ r) :
    ∃ y : Endpt n m,
      siteOf y = WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z ∧
      ¬ (graph (dataOf up hbal)).Reachable z y := by
  refine WalkSupport.other_end_at_wLo edgeOf siteOf atTop (dataOf up hbal)
    (fun _ => rfl) (fun x => partner_edgeOf x) (fun x => partner_top x) z z' ?_ hsplit hle
  intro _ _
  obtain ⟨u, _, hue⟩ := WalkSupport.exists_end_at_wLo edgeOf (graph (dataOf up hbal)) z
  exact covering_on_run l r hl hpos _ hlz hzr ⟨u, hue⟩

/-! ### Walks do not cross a cut site

A crossing edge stays on one edge, and a turn at site `t` moves only between edges
`t - 1` and `t` -- which straddle `s` exactly when `t = s`.  So if the turn keeps its
edge at `s`, no adjacency crosses `s`, and neither does any walk. -/

/-- **No adjacency crosses a cut site.** -/
theorem adj_confined (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (s : ℤ)
    (hcut : ∀ x : Endpt n m, siteOf x = s → edgeOf (turnAt up s x) = edgeOf x)
    (a b : Endpt n m) (hab : (graph (dataOf up hbal)).Adj a b) :
    (edgeOf a < s ↔ edgeOf b < s) := by
  rcases hab with h | h
  · subst h
    show (edgeOf a < s ↔ edgeOf (partner a) < s)
    rw [partner_edgeOf]
  · subst h
    by_cases hs : siteOf a = s
    · have : edgeOf ((dataOf up hbal).t a) = edgeOf a := by
        show edgeOf (turnAt up (siteOf a) a) = edgeOf a
        rw [hs]; exact hcut a hs
      rw [this]
    · -- the turn stays at one site, and that site is not `s`
      have hb : siteOf ((dataOf up hbal).t a) = siteOf a := turnAt_site up hbal a
      have h1 := edge_of_site a (siteOf a) rfl
      have h2 := edge_of_site ((dataOf up hbal).t a) (siteOf a) hb
      cases atTop a <;> cases atTop ((dataOf up hbal).t a) <;>
        simp at h1 h2 <;> omega

/-- **No walk crosses a cut site.** -/
theorem walk_confined (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (s : ℤ)
    (hcut : ∀ x : Endpt n m, siteOf x = s → edgeOf (turnAt up s x) = edgeOf x)
    (x y : Endpt n m) (hr : (graph (dataOf up hbal)).Reachable x y) :
    (edgeOf x < s ↔ edgeOf y < s) := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (adj_confined up hbal s hcut _ _ hadj).trans ih

/-- **A free pair, from run-local covering.**  `CostMerge.hasFreePair_of_minimal` with
its covering hypothesis supplied by `covering_on_run`: the maximiser's leftmost edge
need only sit inside a run whose edges carry crossings. -/
theorem hasFreePair_run (up : Fin n → ℕ) (ds : Bool → Bool)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (l r : ℤ) (hl : 0 ≤ l)
    (hpos : ∀ e : Fin n, l ≤ (e : ℤ) → (e : ℤ) ≤ r → 0 < m e)
    (z : Endpt n m)
    (hzmax : ∀ w : Endpt n m,
      WalkSupport.wLo edgeOf (graph (dataOf up hbal)) w
        ≤ WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z)
    (hlz : l < WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z)
    (hzr : WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z ≤ r)
    (hmin : ∀ (b b' : Endpt n m), siteOf b = siteOf b' →
      isArrOf up b = true → isArrOf up b' = true → ∀ h1 h2 h3,
      ¬ CostMerge.costOf (endDataOf (m := m) up ds)
          (swapData (dataOf up hbal) b ((dataOf up hbal).t b) b'
            ((dataOf up hbal).t b') h1 h2 h3)
        < CostMerge.costOf (endDataOf (m := m) up ds) (dataOf up hbal)) :
    CostMerge.HasFreePair (endDataOf (m := m) up ds) siteOf (dataOf up hbal) := by
  refine CostMerge.hasFreePair_of_minimal (endDataOf (m := m) up ds) edgeOf siteOf atTop
    (dataOf up hbal) (fun _ => rfl) (fun _ => rfl)
    (fun x => partner_edgeOf x) (fun x => partner_top x)
    (fun e => turnAt_site up hbal e) (fun e => turn_arr_flip up hbal e)
    (WalkSupport.p_site_ne edgeOf siteOf atTop partner (fun _ => rfl)
      (fun x => partner_edgeOf x) (fun x => partner_top x))
    z hzmax ?_ hmin
  intro _ _
  obtain ⟨u, _, hue⟩ := WalkSupport.exists_end_at_wLo edgeOf (graph (dataOf up hbal)) z
  exact covering_on_run l r hl hpos _ hlz hzr ⟨u, hue⟩

/-! ### Counting the runs

`CutComponents.gz Zf t` counts the cut sites at or below `t`, so it is the run index,
and `CutComponents.blk` is it read off an end.  It never exceeds `|Z|`, so the run
index lands in `Fin (|Z| + 1)` -- there are at most `|Z| + 1` runs. -/

/-- **The run index is bounded by the number of cut sites.** -/
theorem gz_le_card (Zf : Finset ℤ) (t : ℤ) : CutComponents.gz Zf t ≤ Zf.card :=
  Finset.card_filter_le _ _

/-- The run index of an end, as an element of `Fin (|Z| + 1)`. -/
def runIndex (Zf : Finset ℤ) (x : Endpt n m) : Fin (Zf.card + 1) :=
  ⟨CutComponents.gz Zf (edgeOf x), Nat.lt_succ_of_le (gz_le_card Zf _)⟩

/-- **The run index is constant on walks**, since no walk crosses a cut site. -/
theorem runIndex_const (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (Zf : Finset ℤ)
    (hturn : ∀ x : Endpt n m, edgeOf (turn up x) ≠ edgeOf x → siteOf x ∉ Zf)
    (x y : Endpt n m) (hr : (graph (dataOf up hbal)).Reachable x y) :
    runIndex Zf x = runIndex Zf y := by
  have h := CutComponents.blk_reachable (walk_graph_local_edge up hbal Zf hturn) hr
  exact Fin.ext h

/-- **`c ≤ |Z|`, given separation.**  If ends of the same run always lie in the same
walk, there are at most `|Z| + 1` walks -- that is, at most `|Z|` isolated cycles.

Separation is the stuck condition of the run descent: where it fails, `hasFreePair_run`
supplies a free merge, so a datum on which the descent has halted satisfies it. -/
theorem walkCount_le_runs (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (Zf : Finset ℤ)
    (hturn : ∀ x : Endpt n m, edgeOf (turn up x) ≠ edgeOf x → siteOf x ∉ Zf)
    (hsep : ∀ x y : Endpt n m, runIndex Zf x = runIndex Zf y →
      (graph (dataOf up hbal)).Reachable x y) :
    walkCount (dataOf up hbal) ≤ Zf.card + 1 := by
  have h := ConfigMerge.walkCount_le_card (dataOf up hbal) (runIndex Zf)
    (runIndex_const up hbal Zf hturn) hsep
  simpa using h

/-- The counting, for any datum whose walk graph is `Local` for `Zf`. -/
theorem walkCount_le_runs_gen (D : Data (Endpt n m)) (Zf : Finset ℤ)
    (hlocal : CutComponents.Local (graph D) edgeOf Zf)
    (hsep : ∀ x y : Endpt n m, runIndex Zf x = runIndex Zf y → (graph D).Reachable x y) :
    walkCount D ≤ Zf.card + 1 := by
  have hconst : ∀ x y : Endpt n m, (graph D).Reachable x y →
      runIndex Zf x = runIndex Zf y :=
    fun x y hr => Fin.ext (CutComponents.blk_reachable hlocal hr)
  simpa using ConfigMerge.walkCount_le_card D (runIndex Zf) hconst hsep

/-- **`c ≤ |Z|`, composed.**  Descend while a merge exists; where none does, ends of
one run share a walk, and the count is at most `|Z| + 1`.

The step hypothesis is the run descent: a datum on which separation fails admits a
free merge, which is `hasFreePair_run` followed by `descent_of_split`. -/
theorem c_le_Z_of_step (Zf : Finset ℤ) (P : Data (Endpt n m) → Prop)
    (hlocal : ∀ E, P E → CutComponents.Local (graph E) edgeOf Zf)
    (hstep : ∀ E, P E →
      (∃ E', P E' ∧ walkCount E' < walkCount E) ∨
      (∀ x y : Endpt n m, runIndex Zf x = runIndex Zf y → (graph E).Reachable x y))
    (D : Data (Endpt n m)) (hD : P D) :
    ∃ E, P E ∧ walkCount E ≤ Zf.card + 1 := by
  obtain ⟨E, hPE, hsep⟩ :=
    ConfigMerge.reaches_stuck
      (Stuck := fun E => ∀ x y : Endpt n m,
        runIndex Zf x = runIndex Zf y → (graph E).Reachable x y)
      hstep D hD
  exact ⟨E, hPE, walkCount_le_runs_gen E Zf (hlocal E hPE) hsep⟩

/-! ### The cut condition survives a merge off the cut sites

`Local` for `Zf` is carried by `hturn`: a turn that changes edge sits at a non-cut
site.  The re-pairing moves only the four ends at one site, so if that site is not a
cut site the condition still holds -- and away from those four the turn is unchanged. -/

/-- **`hturn` survives the re-pairing**, provided the merge happens off the cut
sites. -/
theorem hturn_swapT (t : Endpt n m → Endpt n m) (Zf : Finset ℤ)
    (a d a' d' : Endpt n m)
    (hturn : ∀ x : Endpt n m, edgeOf (t x) ≠ edgeOf x → siteOf x ∉ Zf)
    (hsa : siteOf a ∉ Zf)
    (hd : siteOf d = siteOf a) (ha' : siteOf a' = siteOf a) (hd' : siteOf d' = siteOf a) :
    ∀ x : Endpt n m, edgeOf (swapT t a d a' d' x) ≠ edgeOf x → siteOf x ∉ Zf := by
  intro x hne
  by_cases h1 : x = a
  · subst h1; exact hsa
  by_cases h2 : x = d'
  · subst h2; rw [hd']; exact hsa
  by_cases h3 : x = a'
  · subst h3; rw [ha']; exact hsa
  by_cases h4 : x = d
  · subst h4; rw [hd]; exact hsa
  · refine hturn x ?_
    have hx : swapT t a d a' d' x = t x := by
      unfold swapT
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    rwa [hx] at hne

/-! ### The run bounds, re-derived

`hlz` and `hzr` refer to the maximiser of the *current* datum, so they cannot simply
be carried across a merge.  They do not need to be: a walk's leftmost edge lies on the
same side of every cut site as the walk itself, so the run bounds follow from where
the walk is, and `walk_confined` supplies that. -/

/-- **A walk's leftmost edge lies in the walk's own run.**  It is the edge of some end
of the walk, and no walk crosses a cut site. -/
theorem wLo_same_side (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (s : ℤ)
    (hcut : ∀ x : Endpt n m, siteOf x = s → edgeOf (turnAt up s x) = edgeOf x)
    (z : Endpt n m) :
    (WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z < s ↔ edgeOf z < s) := by
  obtain ⟨x, hzx, hxe⟩ := WalkSupport.exists_end_at_wLo edgeOf (graph (dataOf up hbal)) z
  rw [← hxe]
  exact (walk_confined up hbal s hcut z x hzx).symm

/-! ### The invariant survives a step

The descent's invariant is the cut condition `hturn`.  `step_of_split'` returns the
merged datum with an equation on its turn, and `hturn_swapT` carries the condition
across -- provided the merge site is not a cut site, which holds because cut sites
carry no ends. -/

/-- **The cut condition survives a descent step.** -/
theorem hturn_step (Zf : Finset ℤ) (isArr : Endpt n m → Bool)
    (hZ : ∀ x : Endpt n m, isArr x = true → siteOf x ∉ Zf)
    (D D' : Data (Endpt n m)) (a a' : Endpt n m)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hturn : ∀ x : Endpt n m, edgeOf (D.t x) ≠ edgeOf x → siteOf x ∉ Zf)
    (harr : isArr a = true) (hss : siteOf a' = siteOf a)
    (heq : D'.t = swapT D.t a (D.t a) a' (D.t a')) :
    ∀ x : Endpt n m, edgeOf (D'.t x) ≠ edgeOf x → siteOf x ∉ Zf := by
  rw [heq]
  exact hturn_swapT D.t Zf a (D.t a) a' (D.t a') hturn (hZ a harr)
    (hts a) hss (by rw [hts a', hss])

/-! ### The descent invariant, bundled

Everything the run descent must carry: the crossing map, the turn's site and role
laws, the cut condition, cost-minimality, and the covering. -/

/-- The run descent's invariant. -/
structure RunInv (up : Fin n → ℕ) (ds : Bool → Bool) (Zf : Finset ℤ)
    (E : Data (Endpt n m)) : Prop where
  hp : E.p = partner
  hts : ∀ e, siteOf (E.t e) = siteOf e
  hta : ∀ e, isArrOf up (E.t e) = !isArrOf up e
  hturn : ∀ x : Endpt n m, edgeOf (E.t x) ≠ edgeOf x → siteOf x ∉ Zf
  -- Stated without reference to `E`, so it survives a merge unchanged: whether an
  -- edge carries a top end does not depend on the pairing.
  --
  -- **RUN-LOCAL (2026-08-23).**  The antecedent asks for an end to the left of `j`
  -- *in the same run* -- equal `gz`, so no cut site in between.  The earlier global
  -- form, without that clause, was unsatisfiable whenever a cut site existed: a cut
  -- site needs two adjacent empty edges, and then for `j` right of the gap the
  -- antecedents held while `j - 1` was empty.  With the clause, that instance is
  -- excluded because the two sides have different `gz`.
  hcov : ∀ j : ℤ, (∃ u : Endpt n m, edgeOf u = j) →
    (∃ v : Endpt n m, edgeOf v < j ∧
      CutComponents.gz Zf (edgeOf v) = CutComponents.gz Zf j) →
    ∃ w : Endpt n m, edgeOf w = j - 1 ∧ atTop w = true
  hmin : ∀ F : Data (Endpt n m), F.p = partner →
    (∀ e, siteOf (F.t e) = siteOf e) →
    (∀ e, isArrOf up (F.t e) = !isArrOf up e) →
    CostMerge.costOf (endDataOf (m := m) up ds) E
      ≤ CostMerge.costOf (endDataOf (m := m) up ds) F

/-- **The descent step, packaged.**  Where separation fails the invariant yields a
strictly smaller datum still satisfying the cut condition; where it holds the datum is
stuck. -/
theorem run_step (up : Fin n → ℕ) (ds : Bool → Bool) (Zf : Finset ℤ)
    (hZ : ∀ x : Endpt n m, isArrOf up x = true → siteOf x ∉ Zf)
    (E : Data (Endpt n m)) (hE : RunInv up ds Zf E)
    (hcovE : ∀ z v : Endpt n m, edgeOf v < WalkSupport.wLo edgeOf (graph E) z →
      ∃ w : Endpt n m, edgeOf w = WalkSupport.wLo edgeOf (graph E) z - 1 ∧
        atTop w = true) :
    (∃ E' : Data (Endpt n m), RunInv up ds Zf E' ∧ walkCount E' < walkCount E) ∨
      (∀ x y : Endpt n m, runIndex Zf x = runIndex Zf y → (graph E).Reachable x y) := by
  classical
  by_cases hsep : ∀ x y : Endpt n m,
      runIndex Zf x = runIndex Zf y → (graph E).Reachable x y
  · exact Or.inr hsep
  · left
    obtain ⟨x, hx⟩ := not_forall.mp hsep
    obtain ⟨y, hy⟩ := not_forall.mp hx
    have hnr : ¬ (graph E).Reachable x y := fun hc => hy (fun _ => hc)
    have hpe' : ∀ w : Endpt n m, edgeOf (E.p w) = edgeOf w := by
      rw [hE.hp]; exact fun w => partner_edgeOf w
    have hpt' : ∀ w : Endpt n m, atTop (E.p w) = !atTop w := by
      rw [hE.hp]; exact fun w => partner_top w
    have hps : ∀ w : Endpt n m, siteOf (E.p w) ≠ siteOf w := by
      rw [hE.hp]
      exact WalkSupport.p_site_ne edgeOf siteOf atTop partner (fun _ => rfl)
        (fun w => partner_edgeOf w) (fun w => partner_top w)
    have hminE : ∀ (b b' : Endpt n m), siteOf b = siteOf b' →
        isArrOf up b = true → isArrOf up b' = true → ∀ h1 h2 h3,
        ¬ CostMerge.costOf (endDataOf (m := m) up ds)
            (swapData E b (E.t b) b' (E.t b') h1 h2 h3)
          < CostMerge.costOf (endDataOf (m := m) up ds) E := by
      intro b b' hbs hb hb' h1 h2 h3
      refine not_lt.mpr (hE.hmin _ hE.hp ?_ ?_)
      · exact swapT_site siteOf E.t b (E.t b) b' (E.t b') hE.hts (hE.hts b) hbs.symm
          (by rw [hE.hts b', hbs])
      · exact swapT_arr (isArrOf up) E.t b (E.t b) b' (E.t b') hE.hta rfl rfl hb hb'
    obtain ⟨E', hlt, hp', a, a', harr, harr', hss, hsplit, hshared, heq⟩ :=
      CostMerge.step_of_split' (endDataOf (m := m) up ds) edgeOf siteOf atTop E
        (fun _ => rfl) (fun _ => rfl) hpe' hpt' hE.hts hE.hta hps hcovE hminE x y hnr
    -- the merged datum satisfies every component of the invariant
    have hts' : ∀ e, siteOf (E'.t e) = siteOf e := by
      rw [heq]
      exact swapT_site siteOf E.t a (E.t a) a' (E.t a') hE.hts (hE.hts a) hss
        (by rw [hE.hts a', hss])
    have hta' : ∀ e, isArrOf up (E'.t e) = !isArrOf up e := by
      rw [heq]
      exact swapT_arr (isArrOf up) E.t a (E.t a) a' (E.t a') hE.hta rfl rfl harr harr'
    have hne : a ≠ a' := fun h => hsplit (h ▸ SimpleGraph.Reachable.refl _)
    have harrA : isArrOf up a = true := harr
    have harrA' : isArrOf up a' = true := harr'
    have hda : isArrOf up (E.t a) = false := by
      have h := hE.hta a
      rw [harrA] at h
      simpa using h
    have hda' : isArrOf up (E.t a') = false := by
      have h := hE.hta a'
      rw [harrA'] at h
      simpa using h
    have hcost : CostMerge.costOf (endDataOf (m := m) up ds) E'
        = CostMerge.costOf (endDataOf (m := m) up ds) E := by
      have haa2 : a' ≠ a := ConfigMerge.ne_of_split E hsplit
      have h1 := CostMerge.cost_swapData (endDataOf (m := m) up ds) E a a' harr harr'
        hda hda' hne hshared
        (swapT_invol E.t_invol rfl rfl (ConfigMerge.dep_ne_arr' E rfl)
          (ConfigMerge.dep_ne_other E rfl hsplit) haa2
          (ConfigMerge.dep_ne_dep' E rfl rfl haa2)
          (Ne.symm (ConfigMerge.dep_ne_arr' E rfl))
          (ConfigMerge.dep_ne_other' E rfl hsplit))
        (swapT_ne E.t a (E.t a) a' (E.t a') E.t_ne
          (ConfigMerge.dep_ne_other E rfl hsplit)
          (ConfigMerge.dep_ne_other' E rfl hsplit))
        (partner_ne_swapT siteOf E.p E.t a (E.t a) a' (E.t a')
          hps hE.hts (hE.hts a) hss (by rw [hE.hts a', hss]))
      exact (CostMerge.cost_congr (endDataOf (m := m) up ds) E' _
        (fun w _ => by rw [heq]; rfl)).trans h1
    exact ⟨E', ⟨by rw [hp', hE.hp], hts', hta',
      hturn_step Zf (isArrOf up) hZ E E' a a' hE.hts hE.hturn harr hss heq,
      hE.hcov, fun F hF1 hF2 hF3 => by rw [hcost]; exact hE.hmin F hF1 hF2 hF3⟩, hlt⟩

/-- **`Local` from the invariant**, for any datum -- `walk_graph_local_edge` is stated
for `dataOf`, and the descent produces merged data. -/
theorem local_of_hturn (E : Data (Endpt n m)) (Zf : Finset ℤ)
    (hp : E.p = partner)
    (hts : ∀ e, siteOf (E.t e) = siteOf e)
    (hturn : ∀ x : Endpt n m, edgeOf (E.t x) ≠ edgeOf x → siteOf x ∉ Zf) :
    CutComponents.Local (graph E) edgeOf Zf := by
  intro x y hxy
  rcases hxy with h | h
  · subst h
    refine ⟨edgeOf x, Or.inr rfl, Or.inr ?_, fun hne => absurd ?_ hne⟩
    · rw [hp]; exact partner_edgeOf x
    · rw [hp]; exact (partner_edgeOf x).symm
  · subst h
    refine ⟨siteOf x, ?_, ?_, fun hne => hturn x (Ne.symm hne)⟩
    · unfold siteOf edgeOf atTop; cases x.top <;> simp
    · have h2 : siteOf (E.t x) = siteOf x := hts x
      have h3 : edgeOf (E.t x) + (if atTop (E.t x) then (1:ℤ) else 0)
          = siteOf (E.t x) := rfl
      cases hb : atTop (E.t x)
      · right; rw [hb] at h3; simp at h3; omega
      · left; rw [hb] at h3; simp at h3; omega

/-- **`c ≤ |Z|`.**  A cost-minimal configuration merges, run by run, to at most
`|Z| + 1` walks -- that is, at most `|Z|` isolated cycles.

The descent runs while two ends of one run lie in different walks; where none do, the
run index separates the walks and the counting bounds them.  Every hypothesis is the
invariant `RunInv`, and `hZ` says cut sites carry no arrivals, which is
`no_ends_of_alpha_zero`. -/
theorem c_le_Z (up : Fin n → ℕ) (ds : Bool → Bool) (Zf : Finset ℤ)
    (hZ : ∀ x : Endpt n m, isArrOf up x = true → siteOf x ∉ Zf)
    (hcovAll : ∀ E : Data (Endpt n m), RunInv up ds Zf E →
      ∀ z v : Endpt n m, edgeOf v < WalkSupport.wLo edgeOf (graph E) z →
        ∃ w : Endpt n m, edgeOf w = WalkSupport.wLo edgeOf (graph E) z - 1 ∧
          atTop w = true)
    (D : Data (Endpt n m)) (hD : RunInv up ds Zf D) :
    ∃ E : Data (Endpt n m), RunInv up ds Zf E ∧ walkCount E ≤ Zf.card + 1 := by
  obtain ⟨E, hE, hsep⟩ :=
    ConfigMerge.reaches_stuck
      (Stuck := fun E => ∀ x y : Endpt n m,
        runIndex Zf x = runIndex Zf y → (graph E).Reachable x y)
      (fun E hE => run_step up ds Zf hZ E hE (hcovAll E hE)) D hD
  exact ⟨E, hE, walkCount_le_runs_gen E Zf
    (local_of_hturn E Zf hE.hp hE.hts hE.hturn) hsep⟩

/-- **`|Z| + 1 ≤ walkCount`.**  `prop_cut_assembled` gives `|Z|` components avoiding a
marked one; adding the marked one back gives `|Z| + 1` distinct components. -/
theorem walkCount_ge_of_avoiding (D : Data (Endpt n m)) (k : ℕ)
    (c0 : (graph D).ConnectedComponent)
    (F : Fin k → (graph D).ConnectedComponent)
    (hinj : Function.Injective F) (havoid : ∀ i, F i ≠ c0) :
    k + 1 ≤ walkCount D := by
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

/-! ### The shield law

Both inequalities together: a cost-minimal configuration has exactly `|Z| + 1` walks,
so `c = |Z|`.

`c ≥ |Z|` is `CutComponents.exists_injective_components_avoiding` fed by
`local_of_hturn`, converted by `walkCount_ge_of_avoiding`; `c ≤ |Z|` is `c_le_Z`. -/
theorem shield_law (up : Fin n → ℕ) (ds : Bool → Bool) (Zf : Finset ℤ)
    (hZ : ∀ x : Endpt n m, isArrOf up x = true → siteOf x ∉ Zf)
    (A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : Endpt n m, edgeOf x = t)
    (e0 : Endpt n m)
    (hcovAll : ∀ E : Data (Endpt n m), RunInv up ds Zf E →
      ∀ z v : Endpt n m, edgeOf v < WalkSupport.wLo edgeOf (graph E) z →
        ∃ w : Endpt n m, edgeOf w = WalkSupport.wLo edgeOf (graph E) z - 1 ∧
          atTop w = true)
    (D : Data (Endpt n m)) (hD : RunInv up ds Zf D) :
    ∃ E : Data (Endpt n m), RunInv up ds Zf E ∧ walkCount E = Zf.card + 1 := by
  obtain ⟨E, hE, hle⟩ := c_le_Z up ds Zf hZ hcovAll D hD
  refine ⟨E, hE, le_antisymm hle ?_⟩
  obtain ⟨F, hinj, havoid⟩ :=
    CutComponents.exists_injective_components_avoiding
      (local_of_hturn E Zf hE.hp hE.hts hE.hturn) A B hAB hlow hhigh hocc
      ((graph E).connectedComponentMk e0)
  exact walkCount_ge_of_avoiding E Zf.card _ F hinj havoid

/-! ### The shield law is not vacuous

`RunInv` bundles six conditions, and a bundle nothing satisfies proves nothing.  It is
exhibited here on a gap-free configuration, where `Z = ∅`: minimality comes from
`exists_mergesMin`, the structural laws from `Merges`, the covering from
`covering_of_mult_pos`, and the cut condition is vacuous on the empty set. -/

/-- **`RunInv` holds at a cost-minimal datum of a gap-free configuration.** -/
theorem runInv_of_gapfree (up : Fin n → ℕ) (ds : Bool → Bool)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hm : ∀ e : Fin n, 0 < m e) :
    ∃ E : Data (Endpt n m), RunInv up ds (∅ : Finset ℤ) E := by
  obtain ⟨E, ⟨hp, hts, hta⟩, hmin⟩ :=
    CostMerge.exists_mergesMin siteOf partner (endDataOf (m := m) up ds)
      (dataOf up hbal) (merges_dataOf up hbal)
  exact ⟨E, hp, hts, hta, (fun x _ => Finset.notMem_empty _),
    (fun j hu hv => covering_of_mult_pos hm j hu ⟨hv.choose, hv.choose_spec.1⟩),
    fun F h1 h2 h3 => hmin F ⟨h1, h2, h3⟩⟩

/-- The shield law, on the one-edge configuration: its hypotheses are satisfiable. -/
theorem shield_law_witness (ds : Bool → Bool) :
    ∃ E : Data (Endpt 1 (fun _ => 2)),
      RunInv (m := fun _ : Fin 1 => 2) (fun _ => 1) ds (∅ : Finset ℤ) E := by
  exact runInv_of_gapfree (m := fun _ : Fin 1 => 2) (fun _ => 1) ds one_edge_hbal
    (fun _ => by norm_num)

/-! ### The second end, from run-local covering

`other_end_at_wLo` applies its covering at exactly one point -- the bottom end of
`z'`'s walk, whose edge is `wLo z'`.  So when `z` and `z'` lie in the same run the
run-local covering suffices, and the global form is not needed. -/

/-- **The second walk's end, using only run-local covering.** -/
theorem other_end_runlocal (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (Zf : Finset ℤ)
    (hcov : ∀ j : ℤ, (∃ u : Endpt n m, edgeOf u = j) →
      (∃ v : Endpt n m, edgeOf v < j ∧
        CutComponents.gz Zf (edgeOf v) = CutComponents.gz Zf j) →
      ∃ w : Endpt n m, edgeOf w = j - 1 ∧ atTop w = true)
    (z z' : Endpt n m)
    (hsplit : ¬ (graph (dataOf up hbal)).Reachable z z')
    (hle : WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z'
      ≤ WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z)
    (hsame : CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z')
      = CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z)) :
    ∃ y : Endpt n m,
      siteOf y = WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z ∧
      ¬ (graph (dataOf up hbal)).Reachable z y := by
  obtain ⟨u, hur, hue, hub⟩ :=
    WalkSupport.exists_bottom_at_wLo edgeOf atTop (dataOf up hbal)
      (fun x => partner_edgeOf x) (fun x => partner_top x) z'
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- something lies strictly left, in the same run
    obtain ⟨w, hwe, hwt⟩ := hcov _
      (by obtain ⟨x, _, hxe⟩ :=
            WalkSupport.exists_end_at_wLo edgeOf (graph (dataOf up hbal)) z
          exact ⟨x, hxe⟩)
      ⟨u, by omega, by rw [hue]; exact hsame⟩
    obtain ⟨hys, hyn⟩ :=
      WalkSupport.shared_ends_at_wLo edgeOf siteOf atTop (graph (dataOf up hbal))
        (fun _ => rfl) z w hwe hwt
    exact ⟨w, hys, hyn⟩
  · -- the supports start together: `z'`'s own bottom end is at that site
    refine ⟨u, ?_, fun hc => hsplit (hc.trans hur.symm)⟩
    have h := edge_of_site u (siteOf u) rfl
    rw [hub] at h
    simp at h
    omega

/-- **A walk's run index is read off its leftmost edge as well as anywhere else.** -/
theorem gz_wLo (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (Zf : Finset ℤ)
    (hturn : ∀ x : Endpt n m, edgeOf (turn up x) ≠ edgeOf x → siteOf x ∉ Zf)
    (z : Endpt n m) :
    CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z)
      = CutComponents.gz Zf (edgeOf z) := by
  obtain ⟨x, hzx, hxe⟩ := WalkSupport.exists_end_at_wLo edgeOf (graph (dataOf up hbal)) z
  rw [← hxe]
  exact congrArg Fin.val (runIndex_const up hbal Zf hturn x z hzx.symm)

/-- **Two walks of one run have the same run index at their leftmost edges.** -/
theorem gz_wLo_eq (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (Zf : Finset ℤ)
    (hturn : ∀ x : Endpt n m, edgeOf (turn up x) ≠ edgeOf x → siteOf x ∉ Zf)
    (z z' : Endpt n m)
    (hsame : CutComponents.gz Zf (edgeOf z') = CutComponents.gz Zf (edgeOf z)) :
    CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z')
      = CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z) := by
  rw [gz_wLo up hbal Zf hturn z', gz_wLo up hbal Zf hturn z]
  exact hsame

/-- **The free pair, from run-local covering.**  `CostMerge.freePair_of_split` with
`other_end_runlocal` in place of `other_end_at_wLo`, so only the run-local covering is
needed.  The same-run hypothesis comes from the two ends sharing a run index. -/
theorem freePair_runlocal (up : Fin n → ℕ) (ds : Bool → Bool) (Zf : Finset ℤ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (hturn : ∀ x : Endpt n m, edgeOf (turn up x) ≠ edgeOf x → siteOf x ∉ Zf)
    (hcov : ∀ j : ℤ, (∃ u : Endpt n m, edgeOf u = j) →
      (∃ v : Endpt n m, edgeOf v < j ∧
        CutComponents.gz Zf (edgeOf v) = CutComponents.gz Zf j) →
      ∃ w : Endpt n m, edgeOf w = j - 1 ∧ atTop w = true)
    (hmin : ∀ (b b' : Endpt n m), siteOf b = siteOf b' →
      isArrOf up b = true → isArrOf up b' = true → ∀ h1 h2 h3,
      ¬ CostMerge.costOf (endDataOf (m := m) up ds)
          (swapData (dataOf up hbal) b ((dataOf up hbal).t b) b'
            ((dataOf up hbal).t b') h1 h2 h3)
        < CostMerge.costOf (endDataOf (m := m) up ds) (dataOf up hbal))
    (z z' : Endpt n m)
    (hzz' : ¬ (graph (dataOf up hbal)).Reachable z z')
    (hle : WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z'
      ≤ WalkSupport.wLo edgeOf (graph (dataOf up hbal)) z)
    (hsame : CutComponents.gz Zf (edgeOf z') = CutComponents.gz Zf (edgeOf z)) :
    ∃ a a' : Endpt n m,
      siteOf a = siteOf a' ∧ isArrOf up a = true ∧ isArrOf up a' = true ∧
      ¬ (graph (dataOf up hbal)).Reachable a a' ∧
      (atTop a = atTop a' ∨
        atTop ((dataOf up hbal).t a) = atTop ((dataOf up hbal).t a')) := by
  obtain ⟨a, hza, hasite, hab, haarr⟩ :=
    WalkSupport.maximiser_has_bottom_arrival edgeOf siteOf atTop (isArrOf up)
      (dataOf up hbal) (fun _ => rfl) (fun x => partner_edgeOf x)
      (fun x => partner_top x) (fun e => turnAt_site up hbal e)
      (fun e => turn_arr_flip up hbal e) z
  obtain ⟨y, hys, hyn⟩ :=
    other_end_runlocal up hbal Zf hcov z z' hzz' hle
      (gz_wLo_eq up hbal Zf hturn z z' hsame)
  obtain ⟨a', hya', ha'site, ha'arr⟩ :=
    WalkSupport.walk_has_arrival_at_site siteOf (isArrOf up) (dataOf up hbal)
      (fun e => turnAt_site up hbal e) (fun e => turn_arr_flip up hbal e) y y
      (SimpleGraph.Reachable.refl _) _ hys
  have hna' : ¬ (graph (dataOf up hbal)).Reachable z a' :=
    fun hc => hyn (hc.trans hya'.symm)
  have hsplit : ¬ (graph (dataOf up hbal)).Reachable a a' :=
    fun hc => hna' (hza.trans hc)
  have hss : siteOf a' = siteOf a := by rw [hasite, ha'site]
  have hne : a ≠ a' := fun h => hsplit (h ▸ SimpleGraph.Reachable.refl _)
  have hdb : atTop ((dataOf up hbal).t a) = false :=
    WalkSupport.maximiser_departure_bottom edgeOf siteOf atTop (dataOf up hbal)
      (fun _ => rfl) (fun e => turnAt_site up hbal e) z a hza hasite
  have hda : isArrOf up ((dataOf up hbal).t a) = false := by
    have h := turn_arr_flip up hbal a; rw [haarr] at h; simpa using h
  have hda' : isArrOf up ((dataOf up hbal).t a') = false := by
    have h := turn_arr_flip up hbal a'; rw [ha'arr] at h; simpa using h
  have haa2 : a' ≠ a := ConfigMerge.ne_of_split (dataOf up hbal) hsplit
  have h1 := swapT_invol (dataOf up hbal).t_invol rfl rfl
    (ConfigMerge.dep_ne_arr' (dataOf up hbal) rfl)
    (ConfigMerge.dep_ne_other (dataOf up hbal) rfl hsplit) haa2
    (ConfigMerge.dep_ne_dep' (dataOf up hbal) rfl rfl haa2)
    (Ne.symm (ConfigMerge.dep_ne_arr' (dataOf up hbal) rfl))
    (ConfigMerge.dep_ne_other' (dataOf up hbal) rfl hsplit)
  have h2 := swapT_ne (dataOf up hbal).t a ((dataOf up hbal).t a) a'
    ((dataOf up hbal).t a') (dataOf up hbal).t_ne
    (ConfigMerge.dep_ne_other (dataOf up hbal) rfl hsplit)
    (ConfigMerge.dep_ne_other' (dataOf up hbal) rfl hsplit)
  have h3 := partner_ne_swapT siteOf (dataOf up hbal).p (dataOf up hbal).t a
    ((dataOf up hbal).t a) a' ((dataOf up hbal).t a')
    (WalkSupport.p_site_ne edgeOf siteOf atTop partner (fun _ => rfl)
      (fun w => partner_edgeOf w) (fun w => partner_top w))
    (fun e => turnAt_site up hbal e) (turnAt_site up hbal a) hss
    (show siteOf ((dataOf up hbal).t a') = siteOf a from (turnAt_site up hbal a').trans hss)
  exact ⟨a, a', hss.symm, haarr, ha'arr, hsplit,
    CostMerge.free_pair_of_minimal (endDataOf (m := m) up ds) atTop (dataOf up hbal)
      a a' (fun _ => rfl) hab hdb haarr ha'arr hda hda' hne h1 h2 h3
      (hmin a a' hss.symm haarr ha'arr h1 h2 h3)⟩

/-! ### The run-local lemmas, for an arbitrary datum

The descent produces merged data, not `dataOf`, so the run-local lemmas must hold for
any datum carrying the structural laws.  `local_of_hturn` already supplies `Local` for
one; the rest follow. -/

/-- `runIndex` is constant on walks, for any datum. -/
theorem runIndex_const_gen (E : Data (Endpt n m)) (Zf : Finset ℤ)
    (hp : E.p = partner) (hts : ∀ e, siteOf (E.t e) = siteOf e)
    (hturn : ∀ x : Endpt n m, edgeOf (E.t x) ≠ edgeOf x → siteOf x ∉ Zf)
    (x y : Endpt n m) (hr : (graph E).Reachable x y) :
    runIndex Zf x = runIndex Zf y :=
  Fin.ext (CutComponents.blk_reachable (local_of_hturn E Zf hp hts hturn) hr)

/-- A walk's run index is read off its leftmost edge, for any datum. -/
theorem gz_wLo_gen (E : Data (Endpt n m)) (Zf : Finset ℤ)
    (hp : E.p = partner) (hts : ∀ e, siteOf (E.t e) = siteOf e)
    (hturn : ∀ x : Endpt n m, edgeOf (E.t x) ≠ edgeOf x → siteOf x ∉ Zf)
    (z : Endpt n m) :
    CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph E) z)
      = CutComponents.gz Zf (edgeOf z) := by
  obtain ⟨x, hzx, hxe⟩ := WalkSupport.exists_end_at_wLo edgeOf (graph E) z
  rw [← hxe]
  exact congrArg Fin.val (runIndex_const_gen E Zf hp hts hturn x z hzx.symm)

/-- Two walks of one run agree at their leftmost edges, for any datum. -/
theorem gz_wLo_eq_gen (E : Data (Endpt n m)) (Zf : Finset ℤ)
    (hp : E.p = partner) (hts : ∀ e, siteOf (E.t e) = siteOf e)
    (hturn : ∀ x : Endpt n m, edgeOf (E.t x) ≠ edgeOf x → siteOf x ∉ Zf)
    (z z' : Endpt n m)
    (hsame : CutComponents.gz Zf (edgeOf z') = CutComponents.gz Zf (edgeOf z)) :
    CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph E) z')
      = CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph E) z) := by
  rw [gz_wLo_gen E Zf hp hts hturn z', gz_wLo_gen E Zf hp hts hturn z]
  exact hsame

/-- **The second walk's end, run-local, for any datum.** -/
theorem other_end_runlocal_gen (E : Data (Endpt n m)) (Zf : Finset ℤ)
    (hpe : ∀ x : Endpt n m, edgeOf (E.p x) = edgeOf x)
    (hpt : ∀ x : Endpt n m, atTop (E.p x) = !atTop x)
    (hcov : ∀ j : ℤ, (∃ u : Endpt n m, edgeOf u = j) →
      (∃ v : Endpt n m, edgeOf v < j ∧
        CutComponents.gz Zf (edgeOf v) = CutComponents.gz Zf j) →
      ∃ w : Endpt n m, edgeOf w = j - 1 ∧ atTop w = true)
    (z z' : Endpt n m)
    (hsplit : ¬ (graph E).Reachable z z')
    (hle : WalkSupport.wLo edgeOf (graph E) z' ≤ WalkSupport.wLo edgeOf (graph E) z)
    (hsame : CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph E) z')
      = CutComponents.gz Zf (WalkSupport.wLo edgeOf (graph E) z)) :
    ∃ y : Endpt n m,
      siteOf y = WalkSupport.wLo edgeOf (graph E) z ∧ ¬ (graph E).Reachable z y := by
  obtain ⟨u, hur, hue, hub⟩ :=
    WalkSupport.exists_bottom_at_wLo edgeOf atTop E hpe hpt z'
  rcases lt_or_eq_of_le hle with hlt | heq
  · obtain ⟨w, hwe, hwt⟩ := hcov _
      (by obtain ⟨x, _, hxe⟩ := WalkSupport.exists_end_at_wLo edgeOf (graph E) z
          exact ⟨x, hxe⟩)
      ⟨u, by omega, by rw [hue]; exact hsame⟩
    obtain ⟨hys, hyn⟩ :=
      WalkSupport.shared_ends_at_wLo edgeOf siteOf atTop (graph E) (fun _ => rfl) z w hwe hwt
    exact ⟨w, hys, hyn⟩
  · refine ⟨u, ?_, fun hc => hsplit (hc.trans hur.symm)⟩
    have h := edge_of_site u (siteOf u) rfl
    rw [hub] at h
    simp at h
    omega

/-- **The free pair, run-local, for any datum.**  `CostMerge.freePair_of_split` with
`other_end_runlocal_gen` in place of `other_end_at_wLo`: only the run-local covering is
used, so this survives the presence of cut sites. -/
theorem freePair_runlocal_gen (up : Fin n → ℕ) (ds : Bool → Bool) (Zf : Finset ℤ)
    (E : Data (Endpt n m))
    (hp : E.p = partner) (hts : ∀ e, siteOf (E.t e) = siteOf e)
    (hta : ∀ e, isArrOf up (E.t e) = !isArrOf up e)
    (hturn : ∀ x : Endpt n m, edgeOf (E.t x) ≠ edgeOf x → siteOf x ∉ Zf)
    (hcov : ∀ j : ℤ, (∃ u : Endpt n m, edgeOf u = j) →
      (∃ v : Endpt n m, edgeOf v < j ∧
        CutComponents.gz Zf (edgeOf v) = CutComponents.gz Zf j) →
      ∃ w : Endpt n m, edgeOf w = j - 1 ∧ atTop w = true)
    (hmin : ∀ (b b' : Endpt n m), siteOf b = siteOf b' →
      isArrOf up b = true → isArrOf up b' = true → ∀ h1 h2 h3,
      ¬ CostMerge.costOf (endDataOf (m := m) up ds)
          (swapData E b (E.t b) b' (E.t b') h1 h2 h3)
        < CostMerge.costOf (endDataOf (m := m) up ds) E)
    (z z' : Endpt n m)
    (hzz' : ¬ (graph E).Reachable z z')
    (hle : WalkSupport.wLo edgeOf (graph E) z' ≤ WalkSupport.wLo edgeOf (graph E) z)
    (hsame : CutComponents.gz Zf (edgeOf z') = CutComponents.gz Zf (edgeOf z)) :
    ∃ a a' : Endpt n m,
      siteOf a' = siteOf a ∧ isArrOf up a = true ∧ isArrOf up a' = true ∧
      ¬ (graph E).Reachable a a' ∧
      (atTop a = atTop a' ∨ atTop (E.t a) = atTop (E.t a')) := by
  have hpe : ∀ x : Endpt n m, edgeOf (E.p x) = edgeOf x := by
    rw [hp]; exact fun x => partner_edgeOf x
  have hpt : ∀ x : Endpt n m, atTop (E.p x) = !atTop x := by
    rw [hp]; exact fun x => partner_top x
  have hps : ∀ x : Endpt n m, siteOf (E.p x) ≠ siteOf x := by
    rw [hp]
    exact WalkSupport.p_site_ne edgeOf siteOf atTop partner (fun _ => rfl)
      (fun x => partner_edgeOf x) (fun x => partner_top x)
  obtain ⟨a, hza, hasite, hab, haarr⟩ :=
    WalkSupport.maximiser_has_bottom_arrival edgeOf siteOf atTop (isArrOf up) E
      (fun _ => rfl) hpe hpt hts hta z
  obtain ⟨y, hys, hyn⟩ :=
    other_end_runlocal_gen E Zf hpe hpt hcov z z' hzz' hle
      (gz_wLo_eq_gen E Zf hp hts hturn z z' hsame)
  obtain ⟨a', hya', ha'site, ha'arr⟩ :=
    WalkSupport.walk_has_arrival_at_site siteOf (isArrOf up) E hts hta y y
      (SimpleGraph.Reachable.refl _) _ hys
  have hna' : ¬ (graph E).Reachable z a' := fun hc => hyn (hc.trans hya'.symm)
  have hsplit : ¬ (graph E).Reachable a a' := fun hc => hna' (hza.trans hc)
  have hss : siteOf a' = siteOf a := by rw [hasite, ha'site]
  have hne : a ≠ a' := fun h => hsplit (h ▸ SimpleGraph.Reachable.refl _)
  have hdb : atTop (E.t a) = false :=
    WalkSupport.maximiser_departure_bottom edgeOf siteOf atTop E (fun _ => rfl) hts z a hza hasite
  have hda : isArrOf up (E.t a) = false := by
    have h := hta a; rw [haarr] at h; simpa using h
  have hda' : isArrOf up (E.t a') = false := by
    have h := hta a'; rw [ha'arr] at h; simpa using h
  have haa2 : a' ≠ a := fun h => hne h.symm
  have h1 := swapT_invol E.t_invol rfl rfl (ConfigMerge.dep_ne_arr' E rfl)
    (ConfigMerge.dep_ne_other E rfl hsplit) haa2
    (ConfigMerge.dep_ne_dep' E rfl rfl haa2)
    (Ne.symm (ConfigMerge.dep_ne_arr' E rfl)) (ConfigMerge.dep_ne_other' E rfl hsplit)
  have h2 := swapT_ne E.t a (E.t a) a' (E.t a') E.t_ne
    (ConfigMerge.dep_ne_other E rfl hsplit) (ConfigMerge.dep_ne_other' E rfl hsplit)
  have h3 := partner_ne_swapT siteOf E.p E.t a (E.t a) a' (E.t a') hps hts (hts a) hss
    (show siteOf (E.t a') = siteOf a from (hts a').trans hss)
  exact ⟨a, a', hss, haarr, ha'arr, hsplit,
    CostMerge.free_pair_of_minimal (endDataOf (m := m) up ds) atTop E a a'
      (fun _ => rfl) hab hdb haarr ha'arr hda hda' hne h1 h2 h3
      (hmin a a' hss.symm haarr ha'arr h1 h2 h3)⟩

/-! ### The descent step, with no global covering

`run_step` carried `hcovAll`, the unrestricted covering, because `step_of_split'` used
`freePair_of_split`.  With `freePair_runlocal_gen` the run-local covering in `RunInv`
suffices, and the extra hypothesis goes. -/

/-- **The descent step, run-local.**  No global covering hypothesis. -/
theorem run_step_local (up : Fin n → ℕ) (ds : Bool → Bool) (Zf : Finset ℤ)
    (hZ : ∀ x : Endpt n m, isArrOf up x = true → siteOf x ∉ Zf)
    (E : Data (Endpt n m)) (hE : RunInv up ds Zf E) :
    (∃ E' : Data (Endpt n m), RunInv up ds Zf E' ∧ walkCount E' < walkCount E) ∨
      (∀ x y : Endpt n m, runIndex Zf x = runIndex Zf y → (graph E).Reachable x y) := by
  classical
  by_cases hsep : ∀ x y : Endpt n m,
      runIndex Zf x = runIndex Zf y → (graph E).Reachable x y
  · exact Or.inr hsep
  · left
    obtain ⟨x, hx⟩ := not_forall.mp hsep
    obtain ⟨y, hy⟩ := not_forall.mp hx
    have hnr : ¬ (graph E).Reachable x y := fun hc => hy (fun _ => hc)
    have hrun : runIndex Zf x = runIndex Zf y := by
      by_contra hc
      exact hy (fun h => absurd h hc)
    -- order the split so the first end has the larger leftmost edge
    obtain ⟨z, z', hzz', hle, hsame⟩ :
        ∃ z z' : Endpt n m, ¬ (graph E).Reachable z z' ∧
          WalkSupport.wLo edgeOf (graph E) z' ≤ WalkSupport.wLo edgeOf (graph E) z ∧
          CutComponents.gz Zf (edgeOf z') = CutComponents.gz Zf (edgeOf z) := by
      rcases le_total (WalkSupport.wLo edgeOf (graph E) y)
        (WalkSupport.wLo edgeOf (graph E) x) with h | h
      · refine ⟨x, y, hnr, h, ?_⟩
        show CutComponents.gz Zf (edgeOf y) = CutComponents.gz Zf (edgeOf x)
        exact (congrArg Fin.val hrun).symm
      · refine ⟨y, x, fun hc => hnr hc.symm, h, ?_⟩
        show CutComponents.gz Zf (edgeOf x) = CutComponents.gz Zf (edgeOf y)
        exact congrArg Fin.val hrun
    have hminE : ∀ (b b' : Endpt n m), siteOf b = siteOf b' →
        isArrOf up b = true → isArrOf up b' = true → ∀ h1 h2 h3,
        ¬ CostMerge.costOf (endDataOf (m := m) up ds)
            (swapData E b (E.t b) b' (E.t b') h1 h2 h3)
          < CostMerge.costOf (endDataOf (m := m) up ds) E := by
      intro b b' hbs hb hb' k1 k2 k3
      refine not_lt.mpr (hE.hmin _ hE.hp ?_ ?_)
      · exact swapT_site siteOf E.t b (E.t b) b' (E.t b') hE.hts (hE.hts b) hbs.symm
          (by rw [hE.hts b', hbs])
      · exact swapT_arr (isArrOf up) E.t b (E.t b) b' (E.t b') hE.hta rfl rfl hb hb'
    obtain ⟨a, a', hss, harr, harr', hsplit, hshared⟩ :=
      freePair_runlocal_gen up ds Zf E hE.hp hE.hts hE.hta hE.hturn hE.hcov hminE
        z z' hzz' hle hsame
    -- the merge
    have haa2 : a' ≠ a := ConfigMerge.ne_of_split E hsplit
    have hne : a ≠ a' := fun h => haa2 h.symm
    have h1 := swapT_invol E.t_invol rfl rfl (ConfigMerge.dep_ne_arr' E rfl)
      (ConfigMerge.dep_ne_other E rfl hsplit) haa2
      (ConfigMerge.dep_ne_dep' E rfl rfl haa2)
      (Ne.symm (ConfigMerge.dep_ne_arr' E rfl)) (ConfigMerge.dep_ne_other' E rfl hsplit)
    have h2 := swapT_ne E.t a (E.t a) a' (E.t a') E.t_ne
      (ConfigMerge.dep_ne_other E rfl hsplit) (ConfigMerge.dep_ne_other' E rfl hsplit)
    have hps : ∀ w : Endpt n m, siteOf (E.p w) ≠ siteOf w := by
      rw [hE.hp]
      exact WalkSupport.p_site_ne edgeOf siteOf atTop partner (fun _ => rfl)
        (fun w => partner_edgeOf w) (fun w => partner_top w)
    have h3 := partner_ne_swapT siteOf E.p E.t a (E.t a) a' (E.t a') hps hE.hts
      (hE.hts a) hss (show siteOf (E.t a') = siteOf a from (hE.hts a').trans hss)
    have hda : isArrOf up (E.t a) = false := by
      have h := hE.hta a; rw [harr] at h; simpa using h
    have hda' : isArrOf up (E.t a') = false := by
      have h := hE.hta a'; rw [harr'] at h; simpa using h
    refine ⟨swapData E a (E.t a) a' (E.t a') h1 h2 h3, ⟨hE.hp, ?_, ?_, ?_, hE.hcov, ?_⟩,
      ConfigMerge.descent_of_split E a a' hsplit h1 h2 h3⟩
    · exact swapT_site siteOf E.t a (E.t a) a' (E.t a') hE.hts (hE.hts a) hss
        (show siteOf (E.t a') = siteOf a from (hE.hts a').trans hss)
    · exact swapT_arr (isArrOf up) E.t a (E.t a) a' (E.t a') hE.hta rfl rfl harr harr'
    · exact hturn_step Zf (isArrOf up) hZ E _ a a' hE.hts hE.hturn harr hss rfl
    · intro F hF1 hF2 hF3
      have hsh : (endDataOf (m := m) up ds).side a = (endDataOf (m := m) up ds).side a' ∨
          (endDataOf (m := m) up ds).side (E.t a)
            = (endDataOf (m := m) up ds).side (E.t a') := hshared
      rw [CostMerge.cost_swapData (endDataOf (m := m) up ds) E a a' harr harr'
        hda hda' hne hsh h1 h2 h3]
      exact hE.hmin F hF1 hF2 hF3

/-! ### `c ≤ |Z|` and the shield law, unconditional

With `run_step_local` the global covering hypothesis is gone.  What remains are the
invariant `RunInv` -- whose covering clause is run-local and satisfiable in the presence
of cut sites -- and `hZ`, that cut sites carry no arrivals. -/

/-- **`c ≤ |Z|`, no global covering.** -/
theorem c_le_Z_final (up : Fin n → ℕ) (ds : Bool → Bool) (Zf : Finset ℤ)
    (hZ : ∀ x : Endpt n m, isArrOf up x = true → siteOf x ∉ Zf)
    (D : Data (Endpt n m)) (hD : RunInv up ds Zf D) :
    ∃ E : Data (Endpt n m), RunInv up ds Zf E ∧ walkCount E ≤ Zf.card + 1 := by
  obtain ⟨E, hE, hsep⟩ :=
    ConfigMerge.reaches_stuck
      (Stuck := fun E => ∀ x y : Endpt n m,
        runIndex Zf x = runIndex Zf y → (graph E).Reachable x y)
      (fun E hE => run_step_local up ds Zf hZ E hE) D hD
  exact ⟨E, hE, walkCount_le_runs_gen E Zf
    (local_of_hturn E Zf hE.hp hE.hts hE.hturn) hsep⟩

/-- **The shield law, no global covering.**  A cost-minimal configuration has exactly
`|Z| + 1` walks: `c = |Z|`. -/
theorem shield_law_final (up : Fin n → ℕ) (ds : Bool → Bool) (Zf : Finset ℤ)
    (hZ : ∀ x : Endpt n m, isArrOf up x = true → siteOf x ∉ Zf)
    (A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ Zf, A < z) (hhigh : ∀ z ∈ Zf, z ≤ B)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : Endpt n m, edgeOf x = t)
    (e0 : Endpt n m)
    (D : Data (Endpt n m)) (hD : RunInv up ds Zf D) :
    ∃ E : Data (Endpt n m), RunInv up ds Zf E ∧ walkCount E = Zf.card + 1 := by
  obtain ⟨E, hE, hle⟩ := c_le_Z_final up ds Zf hZ D hD
  refine ⟨E, hE, le_antisymm hle ?_⟩
  obtain ⟨F, hinj, havoid⟩ :=
    CutComponents.exists_injective_components_avoiding
      (local_of_hturn E Zf hE.hp hE.hts hE.hturn) A B hAB hlow hhigh hocc
      ((graph E).connectedComponentMk e0)
  exact walkCount_ge_of_avoiding E Zf.card _ F hinj havoid

/-! ### The run-local covering is satisfiable with cut sites

The global covering was not: a cut site needs two adjacent empty edges, and then for
`j` right of the gap the antecedents held while `j - 1` was empty.  The run-local form
excludes exactly that instance, because the two sides of a cut site have different `gz`.
Stated generally rather than on one configuration: if every cut site of `Zf` separates
`j - 1` from everything to its left that carries an end, the antecedent cannot fire. -/

/-- **The run-local covering holds whenever the gap is guarded by a cut site.**  If
edge `j - 1` carries no end, and some cut site lies in `(e, j]` for every edge `e < j`
carrying an end, then the antecedent of `hcov` is never satisfied at `j`. -/
theorem hcov_vacuous_at (Zf : Finset ℤ) (j : ℤ)
    (hguard : ∀ v : Endpt n m, edgeOf v < j →
      CutComponents.gz Zf (edgeOf v) ≠ CutComponents.gz Zf j) :
    (∃ u : Endpt n m, edgeOf u = j) →
      (∃ v : Endpt n m, edgeOf v < j ∧
        CutComponents.gz Zf (edgeOf v) = CutComponents.gz Zf j) →
      ∃ w : Endpt n m, edgeOf w = j - 1 ∧ atTop w = true := by
  rintro _ ⟨v, hlt, heq⟩
  exact absurd heq (hguard v hlt)

/-- A cut site strictly between two edges makes their run indices differ. -/
theorem gz_ne_of_between (Zf : Finset ℤ) (a b s : ℤ)
    (hs : s ∈ Zf) (hab : a < s) (hsb : s ≤ b) :
    CutComponents.gz Zf a ≠ CutComponents.gz Zf b := by
  classical
  have hsub : Zf.filter (fun z => z ≤ a) ⊂ Zf.filter (fun z => z ≤ b) := by
    constructor
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, by omega⟩
    · intro hcon
      have := hcon (Finset.mem_filter.mpr ⟨hs, hsb⟩)
      rw [Finset.mem_filter] at this
      omega
  exact Nat.ne_of_lt (Finset.card_lt_card hsub)

-- Certification (Rule 5).
#print axioms ConfigLoop.hcov_vacuous_at
#print axioms ConfigLoop.gz_ne_of_between
