/-
The assembly point: gap-freeness to a shared site, and from there to `hpair`.

`EdgeData.mult_pos` says every span edge of a gap-free element carries at least one
crossing.  Each crossing lies in some component, whose support therefore contains
that edge.  That is exactly the covering hypothesis of
`SharedSite.shared_site_exists`, and this file records the composition.

What this file does **not** do, and what stands between `thm:nogap` and a
`VERIFIED` label, is construct the map `compOf` from a group element.  Doing so
means defining, in Lean, the lamp configuration, the deposit and travel indicator
it induces on each edge, the strand ends and their sites, and the assignment of
each crossing to a component.  That is a model of the group, not a further step of
the proof: every mathematical input above is already verified.  The blocker is
recorded here rather than left implicit (Rule 5).
-/
import Mathlib.Tactic
import EdgeData
import SharedSite
import ComponentSupport
import EndType

namespace GapFreeAssembly

/-- **Gap-freeness gives the shared site.**  `compOf` assigns to each span edge a
component containing it; `EdgeData.mult_pos` is what guarantees such an assignment
exists, since a gap-free span edge carries a crossing and every crossing lies in a
component.  The conclusion is the dichotomy the merge consumes: either two
components start at the left end of the span, or one starts strictly inside and
shares that site with another. -/
theorem shared_site_of_gapfree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι → ℤ) (L H : ℤ)
    (compOf : ℤ → ι)
    (hsupp : ∀ j : ℤ, L ≤ j → j < H → lo (compOf j) ≤ j ∧ j < hi (compOf j))
    (hspan : ∀ k : ι, hi k ≤ H) (hL : ∀ k : ι, L ≤ lo k)
    (hnedeg : ∀ k : ι, lo k < hi k)
    (a b : ι) (hab : a ≠ b) :
    (∃ i j : ι, i ≠ j ∧ lo i = L ∧ lo j = L) ∨
    (∃ i j : ι, i ≠ j ∧ L < lo i ∧ lo j ≤ lo i - 1 ∧ lo i - 1 < hi j) :=
  SharedSite.shared_site_exists lo hi L H
    (fun j h1 h2 => ⟨compOf j, hsupp j h1 h2⟩) hspan hL a b hab hnedeg

/-- The multiplicity side of the same hypothesis, stated where it is used: a
gap-free edge carries a crossing, so the assignment `compOf` has something to
assign. -/
theorem edge_carries_crossing {d f : ℤ} (hf : EdgeData.IsTravel f)
    (hpar : (d - f) % 2 = 0) (hgap : ¬ EdgeData.IsGap d f) :
    1 ≤ max |d| |f| :=
  EdgeData.mult_pos hf hpar hgap

/-- **The shared site, with every hypothesis constructed.**

`SharedSite.shared_site_exists` needs four things: that every span edge is covered
by some component's support, that supports lie inside the span on both sides, and
that no support is degenerate.  All four now come from `ComponentSupport`, built
from the crossings themselves, so nothing is assumed about how components sit on
the line.

Components are indexed by ends here; `ComponentSupport.cLo_congr` and `cHi_congr`
say the endpoints are constant along a cycle, so this is the same indexing as by
components.

`hcross` is the only remaining input, and it is `EdgeData.mult_pos` transported to
the end type: a gap-free span edge has positive multiplicity, so an end sits on
it. -/
theorem shared_site_constructed {α : Type*} [DecidableEq α] [Fintype α]
    (edgeOf : α → ℤ) (π : Equiv.Perm α) (L H : ℤ)
    (hcross : ∀ j : ℤ, L ≤ j → j < H → ∃ z : α, edgeOf z = j)
    (hlo : ∀ a : α, L ≤ edgeOf a) (hhi : ∀ a : α, edgeOf a < H)
    (a b : α) (hab : a ≠ b) :
    (∃ i j : α, i ≠ j ∧
        ComponentSupport.cLo edgeOf π i = L ∧ ComponentSupport.cLo edgeOf π j = L) ∨
    (∃ i j : α, i ≠ j ∧ L < ComponentSupport.cLo edgeOf π i ∧
        ComponentSupport.cLo edgeOf π j ≤ ComponentSupport.cLo edgeOf π i - 1 ∧
        ComponentSupport.cLo edgeOf π i - 1 < ComponentSupport.cHi edgeOf π j) :=
  SharedSite.shared_site_exists
    (ComponentSupport.cLo edgeOf π) (ComponentSupport.cHi edgeOf π) L H
    (ComponentSupport.covering_of_crossings edgeOf π L H hcross)
    (ComponentSupport.cHi_le_of_edges_le edgeOf π H hhi)
    (ComponentSupport.le_cLo_of_le_edges edgeOf π L hlo)
    a b hab
    (ComponentSupport.cLo_lt_cHi edgeOf π)

/-- **The chain, composed.**  A gap-free configuration yields a shared site, with
nothing assumed.

The edge data is `dep` and `trav` on `Fin n`, subject to the travel range and the
parity, and gap-free.  The multiplicities are the minimum admissible ones.  From
gap-freeness, `EdgeData.mult_pos` makes every multiplicity positive, so
`EndType.exists_end_of_mult_pos` puts an end on every edge, which is the covering
input; the span bounds come from the edge index range.  `shared_site_constructed`
then supplies the dichotomy the merge consumes.

Every hypothesis here is about the configuration itself.  None is about
realisations, components, or costs. -/
theorem shared_site_of_gapfree_config
    (n : ℕ) (dep trav : Fin n → ℤ) (m : Fin n → ℕ)
    (hf : ∀ e, EdgeData.IsTravel (trav e))
    (hpar : ∀ e, (dep e - trav e) % 2 = 0)
    (hgapfree : ∀ e, ¬ EdgeData.IsGap (dep e) (trav e))
    (hm : ∀ e, m e = (max |dep e| |trav e|).toNat)
    (π : Equiv.Perm (EndType.Endpt n m))
    (a b : EndType.Endpt n m) (hab : a ≠ b) :
    (∃ i j : EndType.Endpt n m, i ≠ j ∧
        ComponentSupport.cLo EndType.edgeOf π i = 0 ∧
        ComponentSupport.cLo EndType.edgeOf π j = 0) ∨
    (∃ i j : EndType.Endpt n m, i ≠ j ∧
        0 < ComponentSupport.cLo EndType.edgeOf π i ∧
        ComponentSupport.cLo EndType.edgeOf π j ≤
          ComponentSupport.cLo EndType.edgeOf π i - 1 ∧
        ComponentSupport.cLo EndType.edgeOf π i - 1 <
          ComponentSupport.cHi EndType.edgeOf π j) := by
  refine shared_site_constructed EndType.edgeOf π 0 (n : ℤ) ?_
    (fun x => EndType.edgeOf_nonneg x) (fun x => EndType.edgeOf_lt x) a b hab
  intro j h1 h2
  -- the edge index of `j`
  have hlt : j.toNat < n := by omega
  refine ⟨?_, ?_⟩
  · exact (EndType.exists_end_of_mult_pos (m := m) ⟨j.toNat, hlt⟩
      (by rw [hm]; exact EndType.mult_natPos (hf _) (hpar _) (hgapfree _))).choose
  · have hspec := (EndType.exists_end_of_mult_pos (m := m) ⟨j.toNat, hlt⟩
      (by rw [hm]; exact EndType.mult_natPos (hf _) (hpar _) (hgapfree _))).choose_spec
    rw [hspec]
    simp only []
    omega

/-- **The shared site inside a class.**  `SharedSite.shared_site_exists` is already
general in the interval, so applying it to a class rather than the whole span is
immediate; what needs saying is why both branches of its dichotomy give a site at
which the merge is free.

*Second branch:* one component starts strictly inside the class and the edge to its
left is covered by another, so they meet at a site interior to the class, and
interior sites of a class are not cut, the cut sites being exactly the class
boundaries.

*First branch:* two components both start at the class's left end.  That site is a
class boundary, hence cut, but the merge is still free there: at the leftmost site
of a class every end lies on the edge to its right, so both components have only
right-side ends, and they therefore share an arrival side.  The blocking
configuration is cost-zero bounces on *opposite* sides, which a shared side
excludes.

So the dichotomy delivers a mergeable site either way. -/
theorem shared_site_in_class {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι → ℤ) (L' H' : ℤ)
    (compOf : ℤ → ι)
    (hsupp : ∀ j : ℤ, L' ≤ j → j < H' → lo (compOf j) ≤ j ∧ j < hi (compOf j))
    (hspan : ∀ k : ι, hi k ≤ H') (hL : ∀ k : ι, L' ≤ lo k)
    (hnedeg : ∀ k : ι, lo k < hi k)
    (a b : ι) (hab : a ≠ b) :
    (∃ i j : ι, i ≠ j ∧ lo i = L' ∧ lo j = L') ∨
    (∃ i j : ι, i ≠ j ∧ L' < lo i ∧ lo j ≤ lo i - 1 ∧ lo i - 1 < hi j) :=
  shared_site_of_gapfree lo hi L' H' compOf hsupp hspan hL hnedeg a b hab

/-! ### Non-vacuity

Two components on the span `[0,2)`, the first covering edge `0` and the second
edge `1`.  The dichotomy fires on its second branch: the second component starts
at `1`, strictly inside, and edge `0` immediately to its left is covered by the
first. -/

def loW : Fin 2 → ℤ := fun i => if i = 0 then 0 else 1
def hiW : Fin 2 → ℤ := fun i => if i = 0 then 1 else 2
def compOfW : ℤ → Fin 2 := fun j => if j ≤ 0 then 0 else 1

theorem assembly_not_vacuous :
    (∃ i j : Fin 2, i ≠ j ∧ loW i = 0 ∧ loW j = 0) ∨
    (∃ i j : Fin 2, i ≠ j ∧ 0 < loW i ∧ loW j ≤ loW i - 1 ∧ loW i - 1 < hiW j) := by
  refine shared_site_of_gapfree loW hiW 0 2 compOfW ?_ ?_ ?_ ?_ 0 1 (by decide)
  · intro j h1 h2
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp [loW, hiW, compOfW]
  · intro k; fin_cases k <;> simp [hiW]
  · intro k; fin_cases k <;> simp [loW]
  · intro k; fin_cases k <;> simp [loW, hiW]

-- Certification (Rule 5).
#print axioms GapFreeAssembly.shared_site_of_gapfree
#print axioms GapFreeAssembly.edge_carries_crossing
#print axioms GapFreeAssembly.shared_site_constructed
#print axioms GapFreeAssembly.shared_site_of_gapfree_config
#print axioms GapFreeAssembly.shared_site_in_class
#print axioms GapFreeAssembly.assembly_not_vacuous

end GapFreeAssembly
