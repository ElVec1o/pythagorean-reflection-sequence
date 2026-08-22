/-
Placing the two arrivals at a common site.

`exists_split_of_walkCount` gives two ends in different walks but says nothing about
where they sit; `config_descent` needs them at a *common site*.  The support
machinery closes most of that distance.

`shared_ends_at_cLo` already delivers an end at site `cLo i` lying in a different
cycle from `i`.  What is missing on the other side is an end *of* `i` at that same
site.  The component certainly has an end on the leftmost edge -- the minimum is
attained -- and that is proved here.  Whether that end is a *bottom* end, which is
what puts it at site `cLo` rather than `cLo + 1`, is the one structural input still
outstanding; it is what `bounce_of_all_one_side` is for.
-/
import Mathlib.Tactic
import ComponentSupport

namespace SitePlacement

open ComponentSupport Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The leftmost edge carries an end of the component.**  The support is a finite
non-empty set of integers, so its minimum is attained, and every element of the
support is some component end's edge. -/
theorem exists_end_at_cLo_edge (edgeOf : α → ℤ) (π : Perm α) (z : α) :
    ∃ x : α, π.SameCycle z x ∧ edgeOf x = cLo edgeOf π z := by
  classical
  have hmem : cLo edgeOf π z ∈ cycleEdges edgeOf π z :=
    Finset.min'_mem _ (cycleEdges_nonempty edgeOf π z)
  simp only [cycleEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  exact ⟨x, hx, hxe⟩

/-- A bottom end on the leftmost edge sits at the leftmost site. -/
theorem site_of_bottom_at_cLo (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (π : Perm α) (z x : α) (hxe : edgeOf x = cLo edgeOf π z)
    (hxb : atTop x = false) : siteOf x = cLo edgeOf π z := by
  have h := hsite x
  rw [hxb] at h
  simp at h
  omega

/-- **The placement.**  Given a bottom end `x` of the component on its leftmost
edge, and the top end `y` of the edge immediately to the left, the two lie at the
*same site* and in *different cycles*.  This is exactly the pair `config_descent`
consumes, with `hsplit` supplied by the second conjunct. -/
theorem shared_site_pair (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (π : Perm α) (z x y : α)
    (hx : π.SameCycle z x) (hxe : edgeOf x = cLo edgeOf π z) (hxb : atTop x = false)
    (hy : edgeOf y = cLo edgeOf π z - 1) (hyt : atTop y = true) :
    siteOf x = siteOf y ∧ ¬ π.SameCycle x y := by
  obtain ⟨hys, hns⟩ := shared_ends_at_cLo edgeOf siteOf atTop π hsite z y hy hyt
  refine ⟨?_, ?_⟩
  · rw [site_of_bottom_at_cLo edgeOf siteOf atTop hsite π z x hxe hxb, hys]
  · intro hc
    exact hns (hx.trans hc)

/-- **The outstanding input is discharged by strand-closure.**  The component has an
end on its leftmost edge, but that end might be a top end, sitting at `cLo + 1`
rather than `cLo`.  Its crossing partner shares the edge and is a bottom end, and
strand-closure puts the partner in the same cycle.  So a bottom end on the leftmost
edge always exists. -/
theorem exists_bottom_at_cLo (edgeOf : α → ℤ) (atTop : α → Bool)
    (partner : α → α) (π : Perm α)
    (hclosed : StrandClosed partner π)
    (hpe : ∀ x, edgeOf (partner x) = edgeOf x)
    (hpt : ∀ x, atTop (partner x) = !atTop x)
    (z : α) :
    ∃ x : α, π.SameCycle z x ∧ edgeOf x = cLo edgeOf π z ∧ atTop x = false := by
  obtain ⟨x, hx, hxe⟩ := exists_end_at_cLo_edge edgeOf π z
  by_cases hb : atTop x = false
  · exact ⟨x, hx, hxe, hb⟩
  · refine ⟨partner x, hx.trans (hclosed x), ?_, ?_⟩
    · rw [hpe]; exact hxe
    · rw [hpt]; simp at hb; simp [hb]

/-- **The placement, with no outstanding input.**  Given strand-closure and any end
`y` that is the top end of the edge immediately left of the component's support, the
pair at a common site in different cycles exists. -/
theorem shared_site_pair_exists (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (partner : α → α) (π : Perm α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hclosed : StrandClosed partner π)
    (hpe : ∀ x, edgeOf (partner x) = edgeOf x)
    (hpt : ∀ x, atTop (partner x) = !atTop x)
    (z y : α) (hy : edgeOf y = cLo edgeOf π z - 1) (hyt : atTop y = true) :
    ∃ x : α, siteOf x = siteOf y ∧ ¬ π.SameCycle x y := by
  obtain ⟨x, hx, hxe, hxb⟩ :=
    exists_bottom_at_cLo edgeOf atTop partner π hclosed hpe hpt z
  obtain ⟨h1, h2⟩ :=
    shared_site_pair edgeOf siteOf atTop hsite π z x y hx hxe hxb hy hyt
  exact ⟨x, h1, h2⟩

-- Certification (Rule 5).
#print axioms SitePlacement.exists_bottom_at_cLo
#print axioms SitePlacement.shared_site_pair_exists
