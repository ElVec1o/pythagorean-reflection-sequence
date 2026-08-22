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
#print axioms GapFreeAssembly.assembly_not_vacuous

end GapFreeAssembly
