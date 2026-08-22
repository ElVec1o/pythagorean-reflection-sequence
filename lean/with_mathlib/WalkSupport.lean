/-
Component support over *reachability*, not over `sig`-cycles.

`SitePlacement` builds the support out of `π.SameCycle`, and delivers two ends in
different `sig`-cycles.  The descent needs two ends in different *walks*.  These are
not the same condition: `sig` has twice as many cycles as there are walks, so two
ends in different `sig`-cycles may well lie in one walk, and `¬ SameCycle` does not
give `¬ Reachable`.

Rebuilding the support over reachability fixes it, and the proofs are the same
shape.  One hypothesis even becomes free: strand-closure had to be *assumed* for
cycles, but an end is always adjacent to its crossing partner, so for reachability
it is a theorem.
-/
import Mathlib.Tactic
import WalkGraph

namespace WalkSupport

open WalkGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The edges a walk visits. -/
noncomputable def walkEdges (edgeOf : α → ℤ) (G : SimpleGraph α) (z : α) : Finset ℤ := by
  classical
  exact ((Finset.univ.filter (fun a => G.Reachable z a)).image edgeOf)

theorem walkEdges_nonempty (edgeOf : α → ℤ) (G : SimpleGraph α) (z : α) :
    (walkEdges edgeOf G z).Nonempty := by
  classical
  refine ⟨edgeOf z, ?_⟩
  simp only [walkEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨z, SimpleGraph.Reachable.refl _, rfl⟩

/-- The leftmost edge a walk visits. -/
noncomputable def wLo (edgeOf : α → ℤ) (G : SimpleGraph α) (z : α) : ℤ :=
  (walkEdges edgeOf G z).min' (walkEdges_nonempty edgeOf G z)

theorem wLo_le (edgeOf : α → ℤ) (G : SimpleGraph α) {z x : α} (h : G.Reachable z x) :
    wLo edgeOf G z ≤ edgeOf x := by
  classical
  refine Finset.min'_le _ _ ?_
  simp only [walkEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x, h, rfl⟩

/-- The minimum is attained: the walk has an end on its leftmost edge. -/
theorem exists_end_at_wLo (edgeOf : α → ℤ) (G : SimpleGraph α) (z : α) :
    ∃ x : α, G.Reachable z x ∧ edgeOf x = wLo edgeOf G z := by
  classical
  have hmem : wLo edgeOf G z ∈ walkEdges edgeOf G z :=
    Finset.min'_mem _ (walkEdges_nonempty edgeOf G z)
  simp only [walkEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  exact ⟨x, hx, hxe⟩

/-- **Strand-closure is free here.**  An end is adjacent to its crossing partner, so
the partner is always in the same walk -- no hypothesis needed. -/
theorem reachable_partner (D : Data α) (x : α) : (graph D).Reachable x (D.p x) :=
  (SimpleGraph.Adj.reachable (G := graph D) (Or.inl rfl))

/-- A bottom end on the leftmost edge always exists: if the end there is a top end,
its partner shares the edge, is a bottom end, and lies in the same walk. -/
theorem exists_bottom_at_wLo (edgeOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (z : α) :
    ∃ x : α, (graph D).Reachable z x ∧ edgeOf x = wLo edgeOf (graph D) z ∧
      atTop x = false := by
  obtain ⟨x, hx, hxe⟩ := exists_end_at_wLo edgeOf (graph D) z
  by_cases hb : atTop x = false
  · exact ⟨x, hx, hxe, hb⟩
  · refine ⟨D.p x, hx.trans (reachable_partner D x), ?_, ?_⟩
    · rw [hpe]; exact hxe
    · rw [hpt]; simp at hb; simp [hb]

/-- **The extraction, over walks.**  The top end of the edge immediately left of a
walk's support sits at the walk's leftmost site and lies in a *different walk* --
because its edge is below the support, which every edge of the walk is not. -/
theorem shared_ends_at_wLo (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (G : SimpleGraph α) (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (z y : α) (hy : edgeOf y = wLo edgeOf G z - 1) (hyt : atTop y = true) :
    siteOf y = wLo edgeOf G z ∧ ¬ G.Reachable z y := by
  constructor
  · have h := hsite y
    rw [hyt] at h
    simp only [if_true] at h
    omega
  · intro hc
    have := wLo_le edgeOf G hc
    omega

/-- **The placement, over walks.**  Two ends at a common site in *different walks*:
exactly `config_descent`'s pair, with `hsplit` the second conjunct. -/
theorem walk_shared_site_pair (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (z y : α) (hy : edgeOf y = wLo edgeOf (graph D) z - 1) (hyt : atTop y = true) :
    ∃ x : α, siteOf x = siteOf y ∧ ¬ (graph D).Reachable x y := by
  obtain ⟨x, hx, hxe, hxb⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z
  obtain ⟨hys, hns⟩ := shared_ends_at_wLo edgeOf siteOf atTop (graph D) hsite z y hy hyt
  refine ⟨x, ?_, ?_⟩
  · have h := hsite x
    rw [hxb] at h
    simp at h
    omega
  · intro hc
    exact hns (hx.trans hc)

-- Certification (Rule 5).
#print axioms WalkSupport.exists_end_at_wLo
#print axioms WalkSupport.reachable_partner
#print axioms WalkSupport.exists_bottom_at_wLo
#print axioms WalkSupport.shared_ends_at_wLo
#print axioms WalkSupport.walk_shared_site_pair
