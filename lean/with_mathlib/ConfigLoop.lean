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

-- Certification (Rule 5).
#print axioms ConfigLoop.empty_hbal
#print axioms ConfigLoop.gapfree_not_vacuous
#print axioms ConfigLoop.balance_left
#print axioms ConfigLoop.balance_right
#print axioms ConfigLoop.balance_empty
