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

-- Certification (Rule 5).
#print axioms ConfigLoop.otherComponents_eq_defect
#print axioms ConfigLoop.gapfree_no_isolated_cycles
