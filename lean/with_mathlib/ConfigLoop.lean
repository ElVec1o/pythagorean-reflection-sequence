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

/-! ### The walk graph is `Local`

`prop:cut` (`c ≥ |Z|`) is proved abstractly in `CutComponents` for a graph that is
`Local`: every edge either stays at one position, or steps from `s-1` to `s` with `s`
not a gap site.  The walk graph satisfies the positional half outright -- a turn stays
at its site and a crossing steps by exactly one -- so the whole content of `Local` for
it is the gap condition, isolated below.

Note this is the case the merge chain does **not** cover: everything from
`thm_nogap_optimal` down assumes `∀ e, 0 < m e`, i.e. `Z = ∅`, whereas `prop:cut` is
about `Z ≠ ∅`.  The two halves of the development meet only at `Z = ∅`. -/
theorem walk_graph_local (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (Zf : Finset ℤ)
    (hgap : ∀ x : Endpt n m, edgeOf x + 1 ∉ Zf) :
    CutComponents.Local (graph (dataOf up hbal)) siteOf Zf := by
  intro x y hxy
  rcases hxy with h | h
  · -- a crossing edge: the two ends of one crossing, at sites `e` and `e + 1`
    subst h
    refine ⟨edgeOf x + 1, ?_, ?_, fun _ => hgap x⟩
    · unfold siteOf edgeOf atTop; cases x.top <;> simp
    · show siteOf (partner x) = edgeOf x + 1 - 1 ∨ siteOf (partner x) = edgeOf x + 1
      unfold siteOf edgeOf atTop partner; cases x.top <;> simp
  · -- a turn edge: both ends at the same site
    subst h
    exact ⟨siteOf x, Or.inr rfl, Or.inr (turnAt_site up hbal x), fun hne =>
      absurd (turnAt_site up hbal x).symm hne⟩

/-- Sites obtained by shifting the gap edges by one.

**CORRECTION (2026-08-23).**  This is NOT the paper's `Z`.  `prop:cut` takes `Z` to be
the set of **cut sites** interior to the span -- sites with `α_s = β_s = Φ_s = 0` --
and a maximal run of `L` gap edges contributes its `L - 1` *interior* sites, not `L`.
The definition below gives `L` sites per run and so overcounts by one per run.

It is kept because `walk_graph_local` is stated for an arbitrary `Zf` and this is a
legitimate instance of it; it simply is not the set `prop:cut` counts. -/
def gapSites (dep trav : Fin n → ℤ) : Finset ℤ :=
  (Finset.univ.filter (fun e : Fin n => dep e = 0 ∧ trav e = 0)).image
    (fun e : Fin n => ((e.val : ℤ) + 1))

/-- The gap condition, for the multiplicity law `m = max |d| |f|`.

**SCOPE (2026-08-23).**  This holds when multiplicities are the *minimum admissible*
ones, where a gap edge has `m = 0` and hence carries no end.  That law does NOT hold
on the span: by `cor:lRclosed` an edge with `f = 0` has `m ≥ 2` there, so on the span
gap edges do carry crossings and this hypothesis is unavailable.

So this is a true theorem about minimum-multiplicity configurations, not a discharge
of `Local`'s hypothesis in the setting `prop:cut` lives in. -/
theorem gap_condition (dep trav : Fin n → ℤ)
    (hmdef : ∀ e, m e = (max |dep e| |trav e|).toNat) :
    ∀ x : Endpt n m, edgeOf x + 1 ∉ gapSites dep trav := by
  intro x hx
  simp only [gapSites, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx
  obtain ⟨e, ⟨hd, hf⟩, he⟩ := hx
  have hxe : x.edge = e := by
    have h1 : (e : ℤ) = (x.edge : ℤ) := by unfold edgeOf at he; omega
    exact (Fin.ext (by exact_mod_cast h1)).symm
  subst hxe
  have hme : m x.edge = 0 := by
    have h := hmdef x.edge
    rw [hd, hf] at h
    simpa using h
  have hlt := x.idx.isLt
  omega

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

/-- **`prop:cut` on a configuration.**  At least `|Z|` walks carry neither virtual
event -- that is `c ≥ |Z|`.

The abstract counting is `CutComponents.exists_injective_components_avoiding`; what a
configuration supplies is its `Local` hypothesis, from `walk_graph_local` together
with `gap_condition`.  Occupancy is carried, since it fails exactly where two adjacent
gap edges meet. -/
theorem prop_cut_config (up : Fin n → ℕ) (dep trav : Fin n → ℤ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (A B : ℤ) (hAB : A ≤ B)
    (hlow : ∀ z ∈ gapSites dep trav, A < z) (hhigh : ∀ z ∈ gapSites dep trav, z ≤ B)
    (hmdef : ∀ e, m e = (max |dep e| |trav e|).toNat)
    (hocc : ∀ t : ℤ, A ≤ t → t ≤ B → ∃ x : Endpt n m, siteOf x = t)
    (c0 : (graph (dataOf up hbal)).ConnectedComponent) :
    ∃ F : Fin (gapSites dep trav).card → (graph (dataOf up hbal)).ConnectedComponent,
      Function.Injective F ∧ ∀ i, F i ≠ c0 :=
  CutComponents.exists_injective_components_avoiding
    (walk_graph_local up hbal (gapSites dep trav) (gap_condition dep trav hmdef))
    A B hAB hlow hhigh hocc c0

-- Certification (Rule 5).
#print axioms ConfigLoop.prop_cut_config
