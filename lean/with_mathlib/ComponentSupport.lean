/-
Component supports: the edges a component occupies, and its endpoints.

A component is a cycle of the transition permutation.  Its support is the set of
edges carried by the crossings in that cycle.  `cLo` and `cHi` are its endpoints,
the second offset by one so the support is the half-open interval convention
`SharedSite` uses.

`self_mem_support` is the fact `GapFreeAssembly.compOf` needs: an end's own edge
lies in its component's support.  Combined with `EdgeData.mult_pos`, which says a
gap-free span edge carries a crossing, that is the covering hypothesis.

`cLo_lt_cHi` is the non-degeneracy `SharedSite` also requires.
-/
import Mathlib.Tactic
import OrbitCount

namespace ComponentSupport

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The edges occupied by the component of `z`. -/
noncomputable def cycleEdges (edgeOf : α → ℤ) (π : Perm α) (z : α) : Finset ℤ :=
  ((Finset.univ.filter (fun a => π.SameCycle z a)).image edgeOf)

/-- A component's support contains its own end's edge, so it is non-empty. -/
theorem cycleEdges_nonempty (edgeOf : α → ℤ) (π : Perm α) (z : α) :
    (cycleEdges edgeOf π z).Nonempty := by
  classical
  refine ⟨edgeOf z, ?_⟩
  simp only [cycleEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨z, SameCycle.refl π z, rfl⟩

/-- The left endpoint of a component's support. -/
noncomputable def cLo (edgeOf : α → ℤ) (π : Perm α) (z : α) : ℤ :=
  (cycleEdges edgeOf π z).min' (cycleEdges_nonempty edgeOf π z)

/-- The right endpoint, half-open. -/
noncomputable def cHi (edgeOf : α → ℤ) (π : Perm α) (z : α) : ℤ :=
  (cycleEdges edgeOf π z).max' (cycleEdges_nonempty edgeOf π z) + 1

/-- **The covering fact.**  An end's own edge lies in its component's support. -/
theorem self_mem_support (edgeOf : α → ℤ) (π : Perm α) (z : α) :
    cLo edgeOf π z ≤ edgeOf z ∧ edgeOf z < cHi edgeOf π z := by
  classical
  have hmem : edgeOf z ∈ cycleEdges edgeOf π z := by
    simp only [cycleEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨z, SameCycle.refl π z, rfl⟩
  constructor
  · exact Finset.min'_le _ _ hmem
  · have := Finset.le_max' _ _ hmem
    unfold cHi
    omega

/-- Non-degeneracy: a component's support is a non-empty interval. -/
theorem cLo_lt_cHi (edgeOf : α → ℤ) (π : Perm α) (z : α) :
    cLo edgeOf π z < cHi edgeOf π z := by
  obtain ⟨h1, h2⟩ := self_mem_support edgeOf π z
  omega

/-- The support is constant along a cycle, so `cLo` and `cHi` descend to
components. -/
theorem cycleEdges_congr (edgeOf : α → ℤ) (π : Perm α) {z w : α}
    (h : π.SameCycle z w) : cycleEdges edgeOf π z = cycleEdges edgeOf π w := by
  classical
  unfold cycleEdges
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hz => h.symm.trans hz, fun hw => h.trans hw⟩

theorem cLo_congr (edgeOf : α → ℤ) (π : Perm α) {z w : α} (h : π.SameCycle z w) :
    cLo edgeOf π z = cLo edgeOf π w := by
  unfold cLo; congr 1; exact cycleEdges_congr edgeOf π h

theorem cHi_congr (edgeOf : α → ℤ) (π : Perm α) {z w : α} (h : π.SameCycle z w) :
    cHi edgeOf π z = cHi edgeOf π w := by
  unfold cHi; congr 2; exact cycleEdges_congr edgeOf π h

/-- **The covering hypothesis, constructed.**  If every edge of the span carries a
crossing, then every edge lies in the support of some component.  This is what
`GapFreeAssembly` had to assume as `compOf` together with `hsupp`; here it is
produced from the crossings themselves.

The hypothesis `hcross` is `EdgeData.mult_pos` transported to the end type: a
gap-free span edge has positive multiplicity, so some end sits on it. -/
theorem covering_of_crossings (edgeOf : α → ℤ) (π : Perm α) (L H : ℤ)
    (hcross : ∀ j : ℤ, L ≤ j → j < H → ∃ z : α, edgeOf z = j) :
    ∀ j : ℤ, L ≤ j → j < H →
      ∃ z : α, cLo edgeOf π z ≤ j ∧ j < cHi edgeOf π z := by
  intro j h1 h2
  obtain ⟨z, hz⟩ := hcross j h1 h2
  obtain ⟨hlo, hhi⟩ := self_mem_support edgeOf π z
  exact ⟨z, by rw [← hz]; exact hlo, by rw [← hz]; exact hhi⟩

/-- Every component's support lies inside the span, given that every crossing does.
This is `SharedSite`'s `hspan`. -/
theorem cHi_le_of_edges_le (edgeOf : α → ℤ) (π : Perm α) (H : ℤ)
    (hle : ∀ a : α, edgeOf a < H) (z : α) : cHi edgeOf π z ≤ H := by
  classical
  have hbound : ∀ y ∈ cycleEdges edgeOf π z, y ≤ H - 1 := by
    intro y hy
    simp only [cycleEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hy
    obtain ⟨a, _, ha⟩ := hy
    have := hle a
    omega
  have hb := Finset.max'_le (cycleEdges edgeOf π z) (cycleEdges_nonempty edgeOf π z)
    (H - 1) hbound
  unfold cHi
  omega

/-- And every support starts at or after the span's left end.  This is `hL`. -/
theorem le_cLo_of_le_edges (edgeOf : α → ℤ) (π : Perm α) (L : ℤ)
    (hle : ∀ a : α, L ≤ edgeOf a) (z : α) : L ≤ cLo edgeOf π z := by
  classical
  unfold cLo
  rw [Finset.le_min'_iff]
  intro y hy
  simp only [cycleEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hy
  obtain ⟨a, _, ha⟩ := hy
  rw [← ha]
  exact hle a

/-! ### From supports to ends

The shared-site dichotomy is about component supports, intervals of edges.  The
merge needs it about ends: two ends at one site, in different components, one of
them opening a bounce.  These lemmas cross between the two descriptions.

An end sits at the site of its edge, offset by one when it is the edge's top end.
So at a component's leftmost site, no end of it can be a top end, since that would
put its edge one step further left than the support allows. -/

/-- **At its leftmost site a component has only bottom ends.**  A top end there
would lie on the edge below the support's left endpoint. -/
theorem not_atTop_at_cLo (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (π : Perm α) (z e : α) (hmem : π.SameCycle z e)
    (hs : siteOf e = cLo edgeOf π z) :
    atTop e = false := by
  classical
  by_contra hcon
  have htop : atTop e = true := by simpa using hcon
  -- the end's edge sits one to the left of the support's left endpoint
  have hedge : edgeOf e = cLo edgeOf π z - 1 := by
    have h := hsite e
    rw [htop] at h
    simp only [if_true] at h
    omega
  -- but the edge lies in the support, so it is at least the left endpoint
  have hin : edgeOf e ∈ cycleEdges edgeOf π z := by
    simp only [cycleEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, hmem, rfl⟩
  have hge : cLo edgeOf π z ≤ edgeOf e := Finset.min'_le _ _ hin
  omega

/-- Consequently every end of a component at its leftmost site lies on the edge
that starts the support. -/
theorem edge_eq_cLo_at_cLo (edgeOf siteOf : α → ℤ) (atTop : α → Bool)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (π : Perm α) (z e : α) (hmem : π.SameCycle z e)
    (hs : siteOf e = cLo edgeOf π z) :
    edgeOf e = cLo edgeOf π z := by
  have hbot := not_atTop_at_cLo edgeOf siteOf atTop hsite π z e hmem hs
  have h := hsite e
  rw [hbot] at h
  simp at h
  omega

/-! ### Transition systems, and the bounce at a leftmost site -/

/-- A transition system pairs each arrival with a departure at the same site.  This
is the one structural property of a realisation that the merge argument uses and
that nothing above has needed until now. -/
def IsTransitionSystem {β : Type*} (siteOf : β → ℤ) (isArr : β → Bool) (π : Perm β) : Prop :=
  ∀ a : β, isArr a = true → isArr (π a) = false ∧ siteOf (π a) = siteOf a

/-- **A component whose ends at a site all lie on one side bounces there.**  The
partner of an arrival is a departure at the same site, so it lies on that side too,
and the pair has equal sides. -/
theorem bounce_of_all_one_side {β : Type*} (siteOf : β → ℤ) (isArr side : β → Bool)
    (π : Perm β)
    (hts : IsTransitionSystem siteOf isArr π)
    (z a : β) (hmem : π.SameCycle z a) (harr : isArr a = true)
    (hall : ∀ e : β, π.SameCycle z e → siteOf e = siteOf a → side e = true) :
    side a = side (π a) := by
  have hpartner : π.SameCycle z (π a) := hmem.trans ⟨1, by simp⟩
  obtain ⟨_, hsite⟩ := hts a harr
  rw [hall a hmem rfl, hall (π a) hpartner hsite]

/-- At its leftmost site, every end of a component lies on the right side.  This
supplies the hypothesis of `bounce_of_all_one_side` there. -/
theorem all_right_at_cLo (edgeOf siteOf : α → ℤ) (atTop : α → Bool) (π : Perm α)
    (hsite : ∀ x, siteOf x = edgeOf x + (if atTop x then 1 else 0))
    (z : α) :
    ∀ e : α, π.SameCycle z e → siteOf e = cLo edgeOf π z → (!atTop e) = true := by
  intro e hmem hs
  rw [not_atTop_at_cLo edgeOf siteOf atTop hsite π z e hmem hs]
  rfl

-- Certification (Rule 5).
#print axioms ComponentSupport.cycleEdges_nonempty
#print axioms ComponentSupport.self_mem_support
#print axioms ComponentSupport.cLo_lt_cHi
#print axioms ComponentSupport.cycleEdges_congr
#print axioms ComponentSupport.cLo_congr
#print axioms ComponentSupport.cHi_congr
#print axioms ComponentSupport.covering_of_crossings
#print axioms ComponentSupport.cHi_le_of_edges_le
#print axioms ComponentSupport.le_cLo_of_le_edges
#print axioms ComponentSupport.not_atTop_at_cLo
#print axioms ComponentSupport.edge_eq_cLo_at_cLo
#print axioms ComponentSupport.bounce_of_all_one_side
#print axioms ComponentSupport.all_right_at_cLo

end ComponentSupport
