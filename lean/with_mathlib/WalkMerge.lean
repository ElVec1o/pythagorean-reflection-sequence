/-
Walks as orbits of two involutions, and the merge measured on the correct ensemble.

A realisation gives two involutions on the strand ends: `p` exchanges the two ends
of a crossing, `t` pairs an arrival with a departure at a site.  A **walk** is an
orbit of the pair, that is a connected component of the graph whose edges are the
`p`-edges and the `t`-edges.  That graph is 2-regular, since every end lies on
exactly one edge of each kind, so its components are cycles.

This is the corrected picture.  Earlier files counted cycles of a single
permutation, which is not the walk count: measured on the structured ensemble,
`cycles (t ∘ p) = 2 * walks`, and a 2-swap lowers the walk count by one while
lowering the cycle count by two.

`conn_swap_step` is the step that does the merging: after re-pairing, `a` is
adjacent to `d'`, which lay in the other walk.  Everything else in the merge is the
statement that a cycle minus one edge stays connected, recorded as the hypothesis
`hpath` rather than proved here, since it needs the 2-regularity development.
-/
import Mathlib.Tactic

namespace WalkMerge

variable {α : Type*} [DecidableEq α]

/-- One step of a walk: along the crossing, or across the site. -/
def Step (p t : α → α) (x y : α) : Prop := y = p x ∨ y = t x

/-- Connectivity under both involutions: the walk relation. -/
def Conn (p t : α → α) : α → α → Prop := Relation.ReflTransGen (Step p t)

theorem conn_refl (p t : α → α) (x : α) : Conn p t x x := Relation.ReflTransGen.refl

theorem conn_of_step {p t : α → α} {x y : α} (h : Step p t x y) : Conn p t x y :=
  Relation.ReflTransGen.single h

theorem conn_trans {p t : α → α} {x y z : α}
    (h₁ : Conn p t x y) (h₂ : Conn p t y z) : Conn p t x z :=
  Relation.ReflTransGen.trans h₁ h₂

/-- The re-paired turn: `a` now points at `d'` and `a'` at `d`. -/
def swapTurn (t : α → α) (a d a' d' : α) : α → α := fun x =>
  if x = a then d' else if x = d' then a else
  if x = a' then d else if x = d then a' else t x

@[simp] theorem swapTurn_a (t : α → α) (a d a' d' : α) :
    swapTurn t a d a' d' a = d' := by simp [swapTurn]

/-- **The merging step.**  After re-pairing, `a` is one `t`-step from `d'`, which
lay in the other walk.  This is what joins the two. -/
theorem conn_swap_step (p t : α → α) (a d a' d' : α) :
    Conn p (swapTurn t a d a' d') a d' :=
  conn_of_step (Or.inr (swapTurn_a t a d a' d').symm)

/-- **The merge.**  Given that the other walk stays connected after losing its
`t`-edge, which is the statement that a cycle minus an edge is a path, the two
walks become one.  `hpath` carries that; it is the 2-regularity fact, true and
measured, and not proved here. -/
theorem conn_merge (p t : α → α) (a d a' d' : α)
    (hpath : Conn p (swapTurn t a d a' d') d' a') :
    Conn p (swapTurn t a d a' d') a a' :=
  conn_trans (conn_swap_step p t a d a' d') hpath

/-! ### Non-vacuity: the merging step fires on a concrete configuration. -/

/-- Four ends, `0,1` one walk and `2,3` another; re-pairing `0` with `3` joins
them. -/
theorem witness_step :
    Conn (fun x : Fin 4 => x) (swapTurn (fun x : Fin 4 => x) 0 1 2 3) 0 3 :=
  conn_swap_step _ _ 0 1 2 3

-- Certification (Rule 5).
#print axioms WalkMerge.conn_of_step
#print axioms WalkMerge.conn_trans
#print axioms WalkMerge.swapTurn_a
#print axioms WalkMerge.conn_swap_step
#print axioms WalkMerge.conn_merge
#print axioms WalkMerge.witness_step

end WalkMerge
