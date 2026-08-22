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

end ComponentSupport
