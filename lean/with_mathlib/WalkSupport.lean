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

omit [DecidableEq α] in
theorem walkEdges_nonempty (edgeOf : α → ℤ) (G : SimpleGraph α) (z : α) :
    (walkEdges edgeOf G z).Nonempty := by
  classical
  refine ⟨edgeOf z, ?_⟩
  simp only [walkEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨z, SimpleGraph.Reachable.refl _, rfl⟩

/-- The leftmost edge a walk visits. -/
noncomputable def wLo (edgeOf : α → ℤ) (G : SimpleGraph α) (z : α) : ℤ :=
  (walkEdges edgeOf G z).min' (walkEdges_nonempty edgeOf G z)

omit [DecidableEq α] in
theorem wLo_le (edgeOf : α → ℤ) (G : SimpleGraph α) {z x : α} (h : G.Reachable z x) :
    wLo edgeOf G z ≤ edgeOf x := by
  classical
  refine Finset.min'_le _ _ ?_
  simp only [walkEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x, h, rfl⟩

omit [DecidableEq α] in
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

omit [Fintype α] [DecidableEq α] in
/-- **Strand-closure is free here.**  An end is adjacent to its crossing partner, so
the partner is always in the same walk -- no hypothesis needed. -/
theorem reachable_partner (D : Data α) (x : α) : (graph D).Reachable x (D.p x) :=
  (SimpleGraph.Adj.reachable (G := graph D) (Or.inl rfl))

omit [DecidableEq α] in
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

/-- **The same, with locality asked only where it is used.**

`exists_bottom_at_wLo` asks that the crossing partner keep the edge and flip the end
*everywhere*.  The proof uses that at exactly one end: the one realising the walk's
leftmost edge.  This version asks for it only there.

The point is that the weaker hypothesis is satisfiable by an end type carrying ends
whose partner is not edge-local -- a virtual pair spanning many edges -- provided
those ends are never leftmost in their walk. -/
theorem exists_bottom_at_wLo_local (edgeOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (z : α)
    (hloc : ∀ x, (graph D).Reachable z x → edgeOf x = wLo edgeOf (graph D) z →
      edgeOf (D.p x) = edgeOf x ∧ atTop (D.p x) = !atTop x) :
    ∃ x : α, (graph D).Reachable z x ∧ edgeOf x = wLo edgeOf (graph D) z ∧
      atTop x = false := by
  obtain ⟨x, hx, hxe⟩ := exists_end_at_wLo edgeOf (graph D) z
  by_cases hb : atTop x = false
  · exact ⟨x, hx, hxe, hb⟩
  · obtain ⟨he, ht⟩ := hloc x hx hxe
    refine ⟨D.p x, hx.trans (reachable_partner D x), ?_, ?_⟩
    · rw [he]; exact hxe
    · rw [ht]; simp at hb; simp [hb]

/-- The original is the special case where locality holds everywhere. -/
theorem exists_bottom_at_wLo_of_global (edgeOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x) (z : α) :
    ∃ x : α, (graph D).Reachable z x ∧ edgeOf x = wLo edgeOf (graph D) z ∧
      atTop x = false :=
  exists_bottom_at_wLo_local edgeOf atTop D z (fun x _ _ => ⟨hpe x, hpt x⟩)

omit [DecidableEq α] in
/-- **The extraction, with `hsite` asked only at the end it is used on.**

Like `exists_bottom_at_wLo_local`: the global site-edge relation is asked of one end.
This matters because the site-edge relation is exactly the hypothesis that a virtual
pair -- ends whose site is not determined by their edge -- cannot satisfy. -/
theorem shared_ends_at_wLo_local (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (G : SimpleGraph α) (z y : α)
    (hsy : siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hy : edgeOf y = wLo edgeOf G z - 1) (hyt : atTop y = true) :
    siteOf y = wLo edgeOf G z ∧ ¬ G.Reachable z y := by
  constructor
  · rw [hyt] at hsy
    simp only [if_true] at hsy
    omega
  · intro hc
    have := wLo_le edgeOf G hc
    omega

omit [DecidableEq α] in
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

omit [DecidableEq α] in
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

/-- **`walk_shared_site_pair`, with `hsite` asked only where it is used.**

Two ends need it: the bottom end at the walk's leftmost edge, and `y` itself.  `hpe`
and `hpt` stay global -- they are satisfied by end types with non-local ends, since a
virtual pair still shares an edge and flips the end. -/
theorem walk_shared_site_pair_local (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (z y : α) (hy : edgeOf y = wLo edgeOf (graph D) z - 1) (hyt : atTop y = true)
    (hsy : siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hsX : ∀ x, (graph D).Reachable z x → edgeOf x = wLo edgeOf (graph D) z →
      atTop x = false → siteOf x = edgeOf x + (if atTop x then 1 else 0)) :
    ∃ x : α, siteOf x = siteOf y ∧ ¬ (graph D).Reachable x y := by
  obtain ⟨x, hx, hxe, hxb⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z
  obtain ⟨hys, hns⟩ :=
    shared_ends_at_wLo_local edgeOf siteOf atTop (graph D) z y hsy hy hyt
  refine ⟨x, ?_, ?_⟩
  · have h := hsX x hx hxe hxb
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

omit [DecidableEq α] in
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

/-- **`pair_of_equal_wLo`, localized.**  `hsB` is the site-edge relation at bottom
ends sitting at their own walk's leftmost edge -- the only place it is used. -/
theorem pair_of_equal_wLo_local (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hsB : ∀ w x, (graph D).Reachable w x → edgeOf x = wLo edgeOf (graph D) w →
      atTop x = false → siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (z z' : α) (hsplit : ¬ (graph D).Reachable z z')
    (heq : wLo edgeOf (graph D) z = wLo edgeOf (graph D) z') :
    ∃ x y : α, siteOf x = siteOf y ∧ ¬ (graph D).Reachable x y := by
  obtain ⟨x, hxr, hxe, hxb⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z
  obtain ⟨y, hyr, hye, hyb⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z'
  refine ⟨x, y, ?_, ?_⟩
  · have h1 := hsB z x hxr hxe hxb
    have h2 := hsB z' y hyr hye hyb
    rw [hxb] at h1
    rw [hyb] at h2
    simp at h1 h2
    omega
  · intro hc
    exact hsplit ((hxr.trans hc).trans hyr.symm)

omit [DecidableEq α] in
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

/-- **`pair_of_two_walks`, localized.**  `hsB` at bottom ends on their own walk's
leftmost edge; `hsT` at top ends immediately left of any walk's leftmost edge. -/
theorem pair_of_two_walks_local (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hsB : ∀ w x, (graph D).Reachable w x → edgeOf x = wLo edgeOf (graph D) w →
      atTop x = false → siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsT : ∀ w y, edgeOf y = wLo edgeOf (graph D) w - 1 → atTop y = true →
      siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hcov : ∀ w : α, (∃ v : α, edgeOf v < wLo edgeOf (graph D) w) →
      ∃ y : α, edgeOf y = wLo edgeOf (graph D) w - 1 ∧ atTop y = true)
    (z z' : α) (hsplit : ¬ (graph D).Reachable z z') :
    ∃ x y : α, siteOf x = siteOf y ∧ ¬ (graph D).Reachable x y := by
  obtain ⟨u, _, hue, _⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z
  obtain ⟨u', _, hu'e, _⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z'
  rcases lt_trichotomy (wLo edgeOf (graph D) z) (wLo edgeOf (graph D) z') with h | h | h
  · obtain ⟨y, hye, hyt⟩ := hcov z' ⟨u, by omega⟩
    obtain ⟨x, hxs, hxn⟩ :=
      walk_shared_site_pair_local edgeOf siteOf atTop D hpe hpt z' y hye hyt
        (hsT z' y hye hyt) (fun x hx he hb => hsB z' x hx he hb)
    exact ⟨x, y, hxs, hxn⟩
  · exact pair_of_equal_wLo_local edgeOf siteOf atTop D hpe hpt hsB z z' hsplit h
  · obtain ⟨y, hye, hyt⟩ := hcov z ⟨u', by omega⟩
    obtain ⟨x, hxs, hxn⟩ :=
      walk_shared_site_pair_local edgeOf siteOf atTop D hpe hpt z y hye hyt
        (hsT z y hye hyt) (fun x hx he hb => hsB z x hx he hb)
    exact ⟨x, y, hxs, hxn⟩

/-- **`pair_of_many_walks`, localized.** -/
theorem pair_of_many_walks_local (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hsB : ∀ w x, (graph D).Reachable w x → edgeOf x = wLo edgeOf (graph D) w →
      atTop x = false → siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsT : ∀ w y, edgeOf y = wLo edgeOf (graph D) w - 1 → atTop y = true →
      siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hcov : ∀ w : α, (∃ v : α, edgeOf v < wLo edgeOf (graph D) w) →
      ∃ y : α, edgeOf y = wLo edgeOf (graph D) w - 1 ∧ atTop y = true)
    (hmany : 1 < walkCount D) :
    ∃ x y : α, siteOf x = siteOf y ∧ ¬ (graph D).Reachable x y := by
  obtain ⟨z, z', hsplit⟩ := ConfigMerge.exists_split_of_walkCount D hmany
  exact pair_of_two_walks_local edgeOf siteOf atTop D hpe hpt hsB hsT hcov z z' hsplit

/-! ### From ends to arrivals

The descent re-pairs *arrivals*, but the placement produces ends of either role.  The
turn converts one into the other at no cost: it maps an end to one of the opposite
role at the same site, and it is an edge of the walk graph, so the arrival it
produces lies in the same walk. -/

omit [Fintype α] [DecidableEq α] in
/-- **Every end has an arrival beside it**: itself if it is one, otherwise its turn,
which sits at the same site and in the same walk. -/
theorem arrival_beside (siteOf : α → ℤ) (isArr : α → Bool) (D : Data α)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, isArr (D.t e) = !isArr e)
    (x : α) :
    ∃ a : α, siteOf a = siteOf x ∧ isArr a = true ∧ (graph D).Reachable x a := by
  by_cases h : isArr x = true
  · exact ⟨x, rfl, h, SimpleGraph.Reachable.refl _⟩
  · refine ⟨D.t x, hts x, ?_, SimpleGraph.Adj.reachable (G := graph D) (Or.inr rfl)⟩
    rw [hta]
    simp at h
    simp [h]

/-- **The merge step's input, as arrivals.**  More than one walk gives two
*arrivals* at a common site lying in different walks. -/
theorem arrivals_of_many_walks (edgeOf siteOf : α → ℤ) (atTop isArr : α → Bool)
    (D : Data α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, isArr (D.t e) = !isArr e)
    (hcov : ∀ w : α, (∃ v : α, edgeOf v < wLo edgeOf (graph D) w) →
      ∃ y : α, edgeOf y = wLo edgeOf (graph D) w - 1 ∧ atTop y = true)
    (hmany : 1 < walkCount D) :
    ∃ a a' : α, siteOf a = siteOf a' ∧ isArr a = true ∧ isArr a' = true ∧
      ¬ (graph D).Reachable a a' := by
  obtain ⟨x, y, hxy, hn⟩ :=
    pair_of_many_walks edgeOf siteOf atTop D hsite hpe hpt hcov hmany
  obtain ⟨a, hasite, haarr, hax⟩ := arrival_beside siteOf isArr D hts hta x
  obtain ⟨a', ha'site, ha'arr, ha'y⟩ := arrival_beside siteOf isArr D hts hta y
  refine ⟨a, a', by rw [hasite, ha'site, hxy], haarr, ha'arr, ?_⟩
  intro hc
  exact hn ((hax.trans hc).trans ha'y.symm)

/-- **`arrivals_of_many_walks`, localized.** -/
theorem arrivals_of_many_walks_local (edgeOf siteOf : α → ℤ) (atTop isArr : α → Bool)
    (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, isArr (D.t e) = !isArr e)
    (hsB : ∀ w x, (graph D).Reachable w x → edgeOf x = wLo edgeOf (graph D) w →
      atTop x = false → siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsT : ∀ w y, edgeOf y = wLo edgeOf (graph D) w - 1 → atTop y = true →
      siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hcov : ∀ w : α, (∃ v : α, edgeOf v < wLo edgeOf (graph D) w) →
      ∃ y : α, edgeOf y = wLo edgeOf (graph D) w - 1 ∧ atTop y = true)
    (hmany : 1 < walkCount D) :
    ∃ a a' : α, siteOf a = siteOf a' ∧ isArr a = true ∧ isArr a' = true ∧
      ¬ (graph D).Reachable a a' := by
  obtain ⟨x, y, hxy, hn⟩ :=
    pair_of_many_walks_local edgeOf siteOf atTop D hpe hpt hsB hsT hcov hmany
  obtain ⟨a, hasite, haarr, hax⟩ := arrival_beside siteOf isArr D hts hta x
  obtain ⟨a', ha'site, ha'arr, ha'y⟩ := arrival_beside siteOf isArr D hts hta y
  refine ⟨a, a', by rw [hasite, ha'site, hxy], haarr, ha'arr, ?_⟩
  intro hc
  exact hn ((hax.trans hc).trans ha'y.symm)

/-! ### Closing the loop

Every configuration merges down to a single walk.  The property carried through the
induction is that the crossing map is unchanged and the turn still respects sites and
alternates roles -- all three survive the re-pairing. -/

/-- The invariant the merge preserves. -/
def Merges {α : Type*} [Fintype α] [DecidableEq α]
    (siteOf : α → ℤ) (isArr : α → Bool) (p₀ : α → α) (D : Data α) : Prop :=
  D.p = p₀ ∧ (∀ e, siteOf (D.t e) = siteOf e) ∧ (∀ e, isArr (D.t e) = !isArr e)

omit [Fintype α] [DecidableEq α] in
/-- The crossing partner always changes site: it keeps the edge and flips the end. -/
theorem p_site_ne (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (p₀ : α → α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (p₀ x) = edgeOf x)
    (hpt : ∀ x, atTop (p₀ x) = !atTop x)
    (x : α) : siteOf (p₀ x) ≠ siteOf x := by
  rw [hsite, hsite, hpe, hpt]
  cases h : atTop x <;> simp

/-- **Every configuration merges to one walk.**  While more than one walk remains,
`arrivals_of_many_walks` produces two arrivals at a common site in different walks and
`descent_of_split` merges them, strictly lowering the count; `reaches_one` iterates. -/
theorem merges_to_one (edgeOf siteOf : α → ℤ) (atTop isArr : α → Bool) (p₀ : α → α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (p₀ x) = edgeOf x)
    (hpt : ∀ x, atTop (p₀ x) = !atTop x)
    (hcov0 : ∀ j : ℤ, (∃ u : α, edgeOf u = j) → (∃ v : α, edgeOf v < j) →
      ∃ y : α, edgeOf y = j - 1 ∧ atTop y = true)
    (D : Data α) (hD : Merges siteOf isArr p₀ D) :
    ∃ D', Merges siteOf isArr p₀ D' ∧ walkCount D' ≤ 1 := by
  classical
  refine ConfigMerge.reaches_one (P := Merges siteOf isArr p₀) ?_ D hD
  intro E hmany hE
  obtain ⟨hp, hts, hta⟩ := hE
  obtain ⟨a, a', hss, haa, ha'a2, hsplit⟩ :=
    arrivals_of_many_walks edgeOf siteOf atTop isArr E hsite
      (by rw [hp]; exact hpe) (by rw [hp]; exact hpt) hts hta
      (fun w hw => hcov0 _
        (by obtain ⟨x, _, hxe⟩ := exists_end_at_wLo edgeOf (graph E) w; exact ⟨x, hxe⟩) hw)
      hmany
  -- the six distinctness facts, all from `hsplit`
  have hda : E.t a ≠ a := ConfigMerge.dep_ne_arr' E rfl
  have hd'a : E.t a' ≠ a := ConfigMerge.dep_ne_other E rfl hsplit
  have haa' : a' ≠ a := ConfigMerge.ne_of_split E hsplit
  have hd'd : E.t a' ≠ E.t a := ConfigMerge.dep_ne_dep' E rfl rfl haa'
  have ha'd' : a' ≠ E.t a' := (ConfigMerge.dep_ne_arr' E rfl).symm
  have hda' : E.t a ≠ a' := ConfigMerge.dep_ne_other' E rfl hsplit
  -- the site facts
  have hsd : siteOf (E.t a) = siteOf a := hts a
  have hsa' : siteOf a' = siteOf a := hss.symm
  have hsd' : siteOf (E.t a') = siteOf a := by rw [hts a', hss]
  refine ⟨swapData E a (E.t a) a' (E.t a')
      (swapT_invol E.t_invol rfl rfl hda hd'a haa' hd'd ha'd' hda')
      (swapT_ne E.t a (E.t a) a' (E.t a') E.t_ne hd'a hda')
      (partner_ne_swapT siteOf E.p E.t a (E.t a) a' (E.t a')
        (by rw [hp]; exact p_site_ne edgeOf siteOf atTop p₀ hsite hpe hpt) hts
        hsd hsa' hsd'),
    ⟨hp, ?_, ?_⟩, ConfigMerge.descent_of_split E a a' hsplit _ _ _⟩
  · exact swapT_site siteOf E.t a (E.t a) a' (E.t a') hts hsd hsa' hsd'
  · exact swapT_arr isArr E.t a (E.t a) a' (E.t a') hta rfl rfl haa ha'a2

theorem merges_to_one_local (edgeOf siteOf : α → ℤ) (atTop isArr : α → Bool) (p₀ : α → α)
    (hpe : ∀ x, edgeOf (p₀ x) = edgeOf x)
    (hpt : ∀ x, atTop (p₀ x) = !atTop x)
    (hpsite : ∀ x, siteOf (p₀ x) ≠ siteOf x)
    (hsB : ∀ E : Data α, E.p = p₀ → ∀ w x, (graph E).Reachable w x →
      edgeOf x = wLo edgeOf (graph E) w → atTop x = false →
      siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsT : ∀ E : Data α, E.p = p₀ → ∀ w y, edgeOf y = wLo edgeOf (graph E) w - 1 →
      atTop y = true → siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hcov0 : ∀ j : ℤ, (∃ u : α, edgeOf u = j) → (∃ v : α, edgeOf v < j) →
      ∃ y : α, edgeOf y = j - 1 ∧ atTop y = true)
    (D : Data α) (hD : Merges siteOf isArr p₀ D) :
    ∃ D', Merges siteOf isArr p₀ D' ∧ walkCount D' ≤ 1 := by
  classical
  refine ConfigMerge.reaches_one (P := Merges siteOf isArr p₀) ?_ D hD
  intro E hmany hE
  obtain ⟨hp, hts, hta⟩ := hE
  obtain ⟨a, a', hss, haa, ha'a2, hsplit⟩ :=
    arrivals_of_many_walks_local edgeOf siteOf atTop isArr E
      (by rw [hp]; exact hpe) (by rw [hp]; exact hpt) hts hta
      (hsB E hp) (hsT E hp)
      (fun w hw => hcov0 _
        (by obtain ⟨x, _, hxe⟩ := exists_end_at_wLo edgeOf (graph E) w; exact ⟨x, hxe⟩) hw)
      hmany
  -- the six distinctness facts, all from `hsplit`
  have hda : E.t a ≠ a := ConfigMerge.dep_ne_arr' E rfl
  have hd'a : E.t a' ≠ a := ConfigMerge.dep_ne_other E rfl hsplit
  have haa' : a' ≠ a := ConfigMerge.ne_of_split E hsplit
  have hd'd : E.t a' ≠ E.t a := ConfigMerge.dep_ne_dep' E rfl rfl haa'
  have ha'd' : a' ≠ E.t a' := (ConfigMerge.dep_ne_arr' E rfl).symm
  have hda' : E.t a ≠ a' := ConfigMerge.dep_ne_other' E rfl hsplit
  -- the site facts
  have hsd : siteOf (E.t a) = siteOf a := hts a
  have hsa' : siteOf a' = siteOf a := hss.symm
  have hsd' : siteOf (E.t a') = siteOf a := by rw [hts a', hss]
  refine ⟨swapData E a (E.t a) a' (E.t a')
      (swapT_invol E.t_invol rfl rfl hda hd'a haa' hd'd ha'd' hda')
      (swapT_ne E.t a (E.t a) a' (E.t a') E.t_ne hd'a hda')
      (partner_ne_swapT siteOf E.p E.t a (E.t a) a' (E.t a')
        (by rw [hp]; exact hpsite) hts
        hsd hsa' hsd'),
    ⟨hp, ?_, ?_⟩, ConfigMerge.descent_of_split E a a' hsplit _ _ _⟩
  · exact swapT_site siteOf E.t a (E.t a) a' (E.t a') hts hsd hsa' hsd'
  · exact swapT_arr isArr E.t a (E.t a) a' (E.t a') hta rfl rfl haa ha'a2

/-! ### The canonical site

The numerics single out one site: `s*`, the largest leftmost edge over all walks.  At
it the maximising walk has *every* end on the bottom, and two bottom arrivals in
different walks are conjectured to sit there
(`code/zeta_probe/tools/nogap/maxwlo_probe.py`, 1114 of 1114).

The half about the maximising walk is proved here. -/

omit [DecidableEq α] in
/-- **Every end of a walk at its own leftmost site is a bottom end.**  A top end at
that site would lie on the edge one to the left, below the support. -/
theorem bottom_of_end_at_wLo (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (G : SimpleGraph α) (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (z x : α) (hzx : G.Reachable z x) (hs : siteOf x = wLo edgeOf G z) :
    atTop x = false := by
  by_contra hc
  have ht : atTop x = true := by simpa using hc
  have h := hsite x
  rw [ht] at h
  simp only [if_true] at h
  have := wLo_le edgeOf G hzx
  omega

/-- **`bottom_of_end_at_wLo`, with `hsite` asked only at the end concerned.** -/
theorem bottom_of_end_at_wLo_local (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (G : SimpleGraph α) (z x : α)
    (hsx : siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hzx : G.Reachable z x) (hs : siteOf x = wLo edgeOf G z) :
    atTop x = false := by
  by_contra hc
  have ht : atTop x = true := by simpa using hc
  rw [ht] at hsx
  simp only [if_true] at hsx
  have := wLo_le edgeOf G hzx
  omega

/-- **`maximiser_has_bottom_arrival`, with `hsite` asked only where it is used.**

Two ends need it: the bottom end realising the walk's leftmost edge, and the arrival
beside it.  Both sit at the walk's **leftmost site**, so this is the honest hypothesis.

It is weaker than the global one, but -- unlike `exists_bottom_at_wLo_local` -- it is
not automatically satisfiable by an end type with non-local ends: the arrival beside
is a *turn*-partner, and a turn can land on an end whose site is not determined by its
edge.  The residual obligation is recorded in `EltBridge`. -/
theorem maximiser_has_bottom_arrival_local (edgeOf siteOf : α → ℤ)
    (atTop isArr : α → Bool) (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, isArr (D.t e) = !isArr e)
    (z : α)
    (hsW : ∀ x, (graph D).Reachable z x → siteOf x = wLo edgeOf (graph D) z →
      siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsX : ∀ x, (graph D).Reachable z x → edgeOf x = wLo edgeOf (graph D) z →
      atTop x = false → siteOf x = edgeOf x + (if atTop x then 1 else 0)) :
    ∃ a : α, (graph D).Reachable z a ∧ siteOf a = wLo edgeOf (graph D) z ∧
      atTop a = false ∧ isArr a = true := by
  obtain ⟨x, hxr, hxe, hxb⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z
  have hxs : siteOf x = wLo edgeOf (graph D) z := by
    have h := hsX x hxr hxe hxb; rw [hxb] at h; simp at h; omega
  obtain ⟨a, hasite, haarr, hxa⟩ := arrival_beside siteOf isArr D hts hta x
  have hasW : siteOf a = wLo edgeOf (graph D) z := by rw [hasite, hxs]
  refine ⟨a, hxr.trans hxa, hasW, ?_, haarr⟩
  exact bottom_of_end_at_wLo_local edgeOf siteOf atTop (graph D) z a
    (hsW a (hxr.trans hxa) hasW) (hxr.trans hxa) hasW

/-- **The sharpest form: `hsite` is only needed where the end is *not already* a
bottom.**

`bottom_of_end_at_wLo_local` exists to prove `atTop a = false`.  If `a` is already a
bottom, nothing is needed.  So the hypothesis at the arrival is a *disjunction*, and
an end type whose non-local ends happen to be bottoms satisfies it for free.

This matters: the virtual arrival of a lamp configuration is a bottom arrival, so it
discharges the first disjunct and never needs the site-edge relation. -/
theorem maximiser_has_bottom_arrival_disj (edgeOf siteOf : α → ℤ)
    (atTop isArr : α → Bool) (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, isArr (D.t e) = !isArr e)
    (z : α)
    (hsX : ∀ x, (graph D).Reachable z x → edgeOf x = wLo edgeOf (graph D) z →
      atTop x = false → siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hsW : ∀ x, (graph D).Reachable z x → siteOf x = wLo edgeOf (graph D) z →
      atTop x = false ∨ siteOf x = edgeOf x + (if atTop x then 1 else 0)) :
    ∃ a : α, (graph D).Reachable z a ∧ siteOf a = wLo edgeOf (graph D) z ∧
      atTop a = false ∧ isArr a = true := by
  obtain ⟨x, hxr, hxe, hxb⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z
  have hxs : siteOf x = wLo edgeOf (graph D) z := by
    have h := hsX x hxr hxe hxb; rw [hxb] at h; simp at h; omega
  obtain ⟨a, hasite, haarr, hxa⟩ := arrival_beside siteOf isArr D hts hta x
  have hasW : siteOf a = wLo edgeOf (graph D) z := by rw [hasite, hxs]
  refine ⟨a, hxr.trans hxa, hasW, ?_, haarr⟩
  rcases hsW a (hxr.trans hxa) hasW with hb | hs
  · exact hb
  · exact bottom_of_end_at_wLo_local edgeOf siteOf atTop (graph D) z a hs
      (hxr.trans hxa) hasW

/-- `s*`: the largest leftmost edge over all walks. -/
noncomputable def maxWLo (edgeOf : α → ℤ) (G : SimpleGraph α) (z₀ : α) : ℤ :=
  Finset.univ.sup' ⟨z₀, Finset.mem_univ z₀⟩ (fun z => wLo edgeOf G z)

omit [DecidableEq α] in
/-- `s*` is attained, and dominates every walk's leftmost edge. -/
theorem maxWLo_spec (edgeOf : α → ℤ) (G : SimpleGraph α) (z₀ : α) :
    (∃ z : α, wLo edgeOf G z = maxWLo edgeOf G z₀) ∧
    ∀ w : α, wLo edgeOf G w ≤ maxWLo edgeOf G z₀ := by
  constructor
  · obtain ⟨z, _, hz⟩ := Finset.exists_mem_eq_sup' ⟨z₀, Finset.mem_univ z₀⟩
      (fun z => wLo edgeOf G z)
    exact ⟨z, hz.symm⟩
  · intro w
    exact Finset.le_sup' (f := fun z => wLo edgeOf G z) (Finset.mem_univ w)

omit [DecidableEq α] in
/-- **At `s*`, the maximising walk is all bottom ends.**  This is the half of the
canonical-site conjecture that does not need cost-minimality. -/
theorem maximising_walk_all_bottom (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (G : SimpleGraph α) (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (z₀ z : α) (hz : wLo edgeOf G z = maxWLo edgeOf G z₀) :
    ∀ x : α, G.Reachable z x → siteOf x = maxWLo edgeOf G z₀ → atTop x = false := by
  intro x hzx hs
  exact bottom_of_end_at_wLo edgeOf siteOf atTop G hsite z x hzx (by rw [hs, hz])

omit [DecidableEq α] in
/-- **The maximising walk has a bottom ARRIVAL at its leftmost site.**  This is
claim (i) of the canonical-site conjecture, and it needs **no** cost-minimality --
confirmed on all 76945 multi-walk systems, not only the 1114 minimal ones.

The walk has a bottom end there; if it is a departure, its turn-partner is in the
same walk (a turn is a graph edge), at the same site, with the opposite role, and is
a bottom end too. -/
theorem maximiser_has_bottom_arrival (edgeOf siteOf : α → ℤ) (atTop isArr : α → Bool)
    (D : Data α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, isArr (D.t e) = !isArr e)
    (z : α) :
    ∃ a : α, (graph D).Reachable z a ∧ siteOf a = wLo edgeOf (graph D) z ∧
      atTop a = false ∧ isArr a = true := by
  obtain ⟨x, hxr, hxe, hxb⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z
  have hxs : siteOf x = wLo edgeOf (graph D) z := by
    have h := hsite x; rw [hxb] at h; simp at h; omega
  obtain ⟨a, hasite, haarr, hxa⟩ := arrival_beside siteOf isArr D hts hta x
  refine ⟨a, hxr.trans hxa, by rw [hasite, hxs], ?_, haarr⟩
  exact bottom_of_end_at_wLo edgeOf siteOf atTop (graph D) hsite z a
    (hxr.trans hxa) (by rw [hasite, hxs])

omit [Fintype α] [DecidableEq α] in
/-- **A walk meeting a site has an arrival there.**  If an end of the walk sits at
site `s`, so does an arrival of the same walk: either that end, or its turn-partner,
which shares the site, lies in the same walk, and has the opposite role. -/
theorem walk_has_arrival_at_site (siteOf : α → ℤ) (isArr : α → Bool) (D : Data α)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (hta : ∀ e, isArr (D.t e) = !isArr e)
    (z x : α) (hzx : (graph D).Reachable z x) (s : ℤ) (hs : siteOf x = s) :
    ∃ a : α, (graph D).Reachable z a ∧ siteOf a = s ∧ isArr a = true := by
  obtain ⟨a, hasite, haarr, hxa⟩ := arrival_beside siteOf isArr D hts hta x
  exact ⟨a, hzx.trans hxa, by rw [hasite, hs], haarr⟩

omit [DecidableEq α] in
/-- **Another walk reaches the maximiser's leftmost site.**  The structural fact the
free-pair argument needs, and it splits on whether anything lies to the left.

If some end lies strictly left of `wLo z`, gap-freeness puts a top end on the edge
immediately left, and that end sits at site `wLo z` while lying below the support, so
it is in another walk.  Otherwise `z'`'s support starts at the same edge, and its own
bottom end there is at that site. -/
theorem other_end_at_wLo (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (z z' : α)
    (hcov : ∀ v : α, edgeOf v < wLo edgeOf (graph D) z →
      ∃ y : α, edgeOf y = wLo edgeOf (graph D) z - 1 ∧ atTop y = true)
    (hsplit : ¬ (graph D).Reachable z z')
    (hle : wLo edgeOf (graph D) z' ≤ wLo edgeOf (graph D) z) :
    ∃ y : α, siteOf y = wLo edgeOf (graph D) z ∧ ¬ (graph D).Reachable z y := by
  obtain ⟨u, hur, hue, hub⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z'
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- something lies strictly to the left: use the top end of the edge before
    obtain ⟨y, hye, hyt⟩ := hcov u (by omega)
    obtain ⟨hys, hyn⟩ :=
      shared_ends_at_wLo edgeOf siteOf atTop (graph D) hsite z y hye hyt
    exact ⟨y, hys, hyn⟩
  · -- the two supports start together: `z'`'s own bottom end is at that site
    refine ⟨u, ?_, fun hc => hsplit (hc.trans hur.symm)⟩
    have h := hsite u
    rw [hub] at h
    simp at h
    omega

omit [DecidableEq α] in

/-- **`other_end_at_wLo`, localized.**  `hsB` at bottom ends on their walk's leftmost
edge, and `hsT` at the top end immediately left of it. -/
theorem other_end_at_wLo_local (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (D : Data α)
    (hpe : ∀ x, edgeOf (D.p x) = edgeOf x)
    (hpt : ∀ x, atTop (D.p x) = !atTop x)
    (hsB : ∀ w x, (graph D).Reachable w x → edgeOf x = wLo edgeOf (graph D) w →
      atTop x = false → siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (z z' : α)
    (hsT : ∀ y, edgeOf y = wLo edgeOf (graph D) z - 1 → atTop y = true →
      siteOf y = edgeOf y + (if atTop y then 1 else 0))
    (hcov : ∀ v : α, edgeOf v < wLo edgeOf (graph D) z →
      ∃ y : α, edgeOf y = wLo edgeOf (graph D) z - 1 ∧ atTop y = true)
    (hsplit : ¬ (graph D).Reachable z z')
    (hle : wLo edgeOf (graph D) z' ≤ wLo edgeOf (graph D) z) :
    ∃ y : α, siteOf y = wLo edgeOf (graph D) z ∧ ¬ (graph D).Reachable z y := by
  obtain ⟨u, hur, hue, hub⟩ := exists_bottom_at_wLo edgeOf atTop D hpe hpt z'
  rcases lt_or_eq_of_le hle with hlt | heq
  · obtain ⟨y, hye, hyt⟩ := hcov u (by omega)
    obtain ⟨hys, hyn⟩ :=
      shared_ends_at_wLo_local edgeOf siteOf atTop (graph D) z y (hsT y hye hyt) hye hyt
    exact ⟨y, hys, hyn⟩
  · refine ⟨u, ?_, fun hc => hsplit (hc.trans hur.symm)⟩
    have h := hsB z' u hur hue hub
    rw [hub] at h
    simp at h
    omega

/-- **In the maximising walk, a departure at the leftmost site is a bottom end too.**

This is what kills the one configuration `cross_dearer` would otherwise allow: the
turn-partner of an end of `z` at `wLo z` lies in the *same* walk (a turn is a graph
edge) and at the *same* site, and that walk has no end below edge `wLo z`.  So the
arrival and its departure are both bottoms -- they align, which is exactly the
hypothesis the strict exchange needs. -/
theorem maximiser_departure_bottom (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (D : Data α) (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (z a : α) (hza : (graph D).Reachable z a)
    (hs : siteOf a = wLo edgeOf (graph D) z) :
    atTop (D.t a) = false := by
  refine bottom_of_end_at_wLo edgeOf siteOf atTop (graph D) hsite z (D.t a) ?_ ?_
  · exact hza.trans (SimpleGraph.Adj.reachable (G := graph D) (Or.inr rfl))
  · rw [hts a]; exact hs

/-- **`maximising_walk_all_bottom`, localized.** -/
theorem maximising_walk_all_bottom_local (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (G : SimpleGraph α) (z₀ z : α) (hz : wLo edgeOf G z = maxWLo edgeOf G z₀)
    (hsB : ∀ x, G.Reachable z x → siteOf x = maxWLo edgeOf G z₀ →
      siteOf x = edgeOf x + (if atTop x then 1 else 0)) :
    ∀ x : α, G.Reachable z x → siteOf x = maxWLo edgeOf G z₀ → atTop x = false := by
  intro x hzx hs
  exact bottom_of_end_at_wLo_local edgeOf siteOf atTop G z x (hsB x hzx hs) hzx
    (by rw [hs, hz])

/-- **`maximiser_departure_bottom`, localized**: the relation is needed at the turn
of `a`, and nowhere else. -/
theorem maximiser_departure_bottom_local (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (D : Data α)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (z a : α) (hza : (graph D).Reachable z a)
    (hs : siteOf a = wLo edgeOf (graph D) z)
    (hsta : siteOf (D.t a) = edgeOf (D.t a) + (if atTop (D.t a) then 1 else 0)) :
    atTop (D.t a) = false := by
  refine bottom_of_end_at_wLo_local edgeOf siteOf atTop (graph D) z (D.t a) hsta ?_ ?_
  · exact hza.trans (SimpleGraph.Adj.reachable (G := graph D) (Or.inr rfl))
  · rw [hts a]; exact hs

/-- **`maximiser_departure_bottom`, disjunctive form.**  Its conclusion is that the
turn is a bottom, so an end that is already a bottom needs nothing. -/
theorem maximiser_departure_bottom_disj (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (D : Data α)
    (hts : ∀ e, siteOf (D.t e) = siteOf e)
    (z a : α) (hza : (graph D).Reachable z a)
    (hs : siteOf a = wLo edgeOf (graph D) z)
    (hsta : atTop (D.t a) = false ∨
      siteOf (D.t a) = edgeOf (D.t a) + (if atTop (D.t a) then 1 else 0)) :
    atTop (D.t a) = false := by
  rcases hsta with h | h
  · exact h
  · exact maximiser_departure_bottom_local edgeOf siteOf atTop D hts z a hza hs h

/-! ### The maximiser, restricted to a set

`maxWLo` takes the sup over all ends, so its maximiser lies in the rightmost run.  The
run induction needs the sup over the ends of one run instead.  A non-empty finite set
still attains its sup, so the argument carries over unchanged. -/

/-- `s*` restricted to a set of ends. -/
noncomputable def maxWLoOn (edgeOf : α → ℤ) (G : SimpleGraph α)
    (S : Finset α) (hS : S.Nonempty) : ℤ :=
  S.sup' hS (fun z => wLo edgeOf G z)

omit [DecidableEq α] in
/-- It is attained inside the set, and dominates the set. -/
theorem maxWLoOn_spec (edgeOf : α → ℤ) (G : SimpleGraph α)
    (S : Finset α) (hS : S.Nonempty) :
    (∃ z ∈ S, wLo edgeOf G z = maxWLoOn edgeOf G S hS) ∧
    ∀ w ∈ S, wLo edgeOf G w ≤ maxWLoOn edgeOf G S hS := by
  constructor
  · obtain ⟨z, hz, hval⟩ := Finset.exists_mem_eq_sup' hS (fun z => wLo edgeOf G z)
    exact ⟨z, hz, hval.symm⟩
  · intro w hw
    exact Finset.le_sup' (f := fun z => wLo edgeOf G z) hw

-- Certification (Rule 5).
#print axioms WalkSupport.maxWLoOn_spec
#print axioms WalkSupport.exists_bottom_at_wLo_local
#print axioms WalkSupport.exists_bottom_at_wLo_of_global
#print axioms WalkSupport.shared_ends_at_wLo_local
#print axioms WalkSupport.bottom_of_end_at_wLo_local
#print axioms WalkSupport.maximiser_has_bottom_arrival_local
#print axioms WalkSupport.maximiser_has_bottom_arrival_disj
#print axioms WalkSupport.walk_shared_site_pair_local
#print axioms WalkSupport.pair_of_equal_wLo_local
#print axioms WalkSupport.other_end_at_wLo_local
#print axioms WalkSupport.pair_of_two_walks_local
#print axioms WalkSupport.pair_of_many_walks_local
#print axioms WalkSupport.arrivals_of_many_walks_local
#print axioms WalkSupport.merges_to_one_local
#print axioms WalkSupport.maximising_walk_all_bottom_local
#print axioms WalkSupport.maximiser_departure_bottom_local
#print axioms WalkSupport.maximiser_departure_bottom_disj
