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

-- Certification (Rule 5).
#print axioms ConfigLoop.gapfree_merges_to_one
