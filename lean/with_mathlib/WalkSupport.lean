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
import ConfigMerge

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

/-! ### The two cases

For two walks there are two possibilities, and each yields a pair at a common site.

*Case A*, the supports start on the same edge: each walk has a bottom end there, and
both bottom ends sit at that edge's lower site.

*Case B*, one support starts strictly to the right: the edge immediately to its left
is below it, so the top end there lies in a different walk.  That case is
`walk_shared_site_pair` above.
-/

/-- **Case A.**  Two different walks whose supports start on the same edge each have
a bottom end there, and the two sit at the same site. -/
theorem pair_of_equal_wLo (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (z z' : α) (hsplit : ¬ (graph D).Reachable z z')
    (heq : wLo edgeOf (graph D) z = wLo edgeOf (graph D) z') :
    ∃ x y : α, siteOf x = siteOf y ∧ ¬ (graph D).Reachable x y := by
  obtain ⟨x, hxr, hxe, hxb⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z
  obtain ⟨y, hyr, hye, hyb⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z'
  refine ⟨x, y, ?_, ?_⟩
  · have h1 := hsite x
    have h2 := hsite y
    rw [hxb] at h1
    rw [hyb] at h2
    simp at h1 h2
    omega
  · intro hc
    exact hsplit ((hxr.trans hc).trans hyr.symm)

/-- **The dichotomy.**  Two ends in different walks yield a pair at a common site in
different walks.

The covering proviso `hcov` fires only where it can: it asks for a top end on the
edge immediately left of a walk's support *given that some end already lies strictly
to that support's left*.  That is exactly the situation Case B needs, and it is what
gap-freeness supplies -- every edge in range carries an end. -/
theorem pair_of_two_walks (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hcov : ∀ w : α, (∃ v : α, edgeOf v < wLo edgeOf (graph D) w) →
      ∃ y : α, edgeOf y = wLo edgeOf (graph D) w - 1 ∧ atTop y = true)
    (z z' : α) (hsplit : ¬ (graph D).Reachable z z') :
    ∃ x y : α, siteOf x = siteOf y ∧ ¬ (graph D).Reachable x y := by
  -- an end of each walk on its own leftmost edge, used to witness "something lies left"
  obtain ⟨u, _, hue, _⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z
  obtain ⟨u', _, hu'e, _⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z'
  rcases lt_trichotomy (wLo edgeOf (graph D) z) (wLo edgeOf (graph D) z') with h | h | h
  · -- `z`'s support starts to the left, so use `z'`
    obtain ⟨y, hye, hyt⟩ := hcov z' ⟨u, by omega⟩
    obtain ⟨x, hxs, hxn⟩ :=
      walk_shared_site_pair edgeOf siteOf atTop D hsite hpe hpt z' y hye hyt
    exact ⟨x, y, hxs, hxn⟩
  · exact pair_of_equal_wLo edgeOf siteOf atTop D hsite hpe hpt z z' hsplit h
  · -- `z'`'s support starts to the left, so use `z`
    obtain ⟨y, hye, hyt⟩ := hcov z ⟨u', by omega⟩
    obtain ⟨x, hxs, hxn⟩ :=
      walk_shared_site_pair edgeOf siteOf atTop D hsite hpe hpt z y hye hyt
    exact ⟨x, y, hxs, hxn⟩

/-- **More than one walk gives a mergeable pair.**  Composing the walk-count entry
point with the dichotomy: whenever the configuration has more than one walk, two ends
at a common site lie in different walks, which is precisely what the merge step
consumes. -/
theorem pair_of_many_walks (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hcov : ∀ w : α, (∃ v : α, edgeOf v < wLo edgeOf (graph D) w) →
      ∃ y : α, edgeOf y = wLo edgeOf (graph D) w - 1 ∧ atTop y = true)
    (hmany : 1 < walkCount D) :
    ∃ x y : α, siteOf x = siteOf y ∧ ¬ (graph D).Reachable x y := by
  obtain ⟨z, z', hsplit⟩ := ConfigMerge.exists_split_of_walkCount D hmany
  exact pair_of_two_walks edgeOf siteOf atTop D hsite hpe hpt hcov z z' hsplit

-- Certification (Rule 5).
#print axioms WalkSupport.pair_of_many_walks
