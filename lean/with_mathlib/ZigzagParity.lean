/-
  ZigzagParity.lean
  =================
  The counting core behind BLOCK 339 and the refutation logged with it: WHY the
  single-chain zigzag turn described in `EltBridge.lean`'s own docstring (the section
  "A path of links is joined", "up 0 - dn 0 - up 1 - dn 1 ...") cannot work at even
  multiplicities, and why the spine+zigzag ("Through2") that replaced it must split
  each edge into TWO chains rather than one.

  Both facts were established computationally first (a Rust sweep: the single chain
  fails 4302 of 4665 configurations, passing exactly when every run has length one;
  the spine+zigzag passes 149796/149796).  What follows is the arithmetic reason,
  kernel-checked, so the refutation no longer rests on a sweep alone.

  The setting, in the notation of `EndType.Endpt`: one edge carries `2 * w` parallel
  strands, each with a bottom end and a top end.  A "bounce" at the top pairs two top
  ends of that edge; a bounce at the bottom pairs two bottom ends.  Write `a` for the
  number of top bounces and `b` for the number of bottom bounces.  Then `a <= w` and
  `b <= w` (there are only `2 * w` ends on each side), the strands left unpaired on the
  top are `2 * w - 2 * a` and on the bottom `2 * w - 2 * b`, and those loose ends are
  exactly what can PASS to a neighbouring edge.

  One graph-theoretic input is used, as a hypothesis rather than re-proved here: a
  connected graph on `2 * w` vertices has at least `2 * w - 1` edges, so an edge whose
  own bounces already connect its strands has `a + b + 1 >= 2 * w`.

  No `sorry`.
-/

import Mathlib.Tactic

namespace ZigzagParity

/-- **A bounce-connected edge has all its loose ends on one side.**  If the edge's own
bounces already join its `2 * w` strands into one chain, then `a + b + 1 >= 2 * w`, and
since neither `a` nor `b` can exceed `w` this forces one of the two sides to be
perfectly matched -- leaving it with no loose end at all.  This is the whole obstruction:
such an edge has a free end on at most ONE of its two sides. -/
theorem loose_ends_one_sided (w a b : ℕ) (ha : a ≤ w) (hb : b ≤ w)
    (hconn : 2 * w ≤ a + b + 1) :
    2 * w - 2 * a = 0 ∨ 2 * w - 2 * b = 0 := by
  omega

/-- **The pass count at a site is even when both widths are.**  A pass consumes one end
from each side; the ends it does not consume are paired among themselves, so each side's
leftover is even.  With both widths even that forces the number of passes even. -/
theorem pass_count_even (mL mR p : ℕ) (hL : mL % 2 = 0) (hR : mR % 2 = 0)
    (hpL : p ≤ mL) (hpR : p ≤ mR)
    (hbL : (mL - p) % 2 = 0) (hbR : (mR - p) % 2 = 0) :
    p % 2 = 0 := by
  omega

/-- **So linking two edges costs at least two passes.**  There is no way to join
neighbouring edges with a single strand crossing: one pass would leave both sides odd. -/
theorem link_needs_two (mL mR p : ℕ) (hL : mL % 2 = 0) (hR : mR % 2 = 0)
    (hpL : p ≤ mL) (hpR : p ≤ mR)
    (hbL : (mL - p) % 2 = 0) (hbR : (mR - p) % 2 = 0) (hlink : 0 < p) :
    2 ≤ p := by
  omega

/-- **The single-chain zigzag is impossible for an edge interior to a run.**  Such an
edge must link to BOTH neighbours, so by `link_needs_two` it needs at least two loose
ends on each side; but `loose_ends_one_sided` says a bounce-connected edge has loose ends
on at most one side.  The two requirements are contradictory, at every even width.

This is the arithmetic content of the counterexample `m = [2, 2]`, `Z = {}` found by the
Rust sweep: one run, two edges, and the single-chain construction yields two components
instead of one. -/
theorem single_chain_fails (w a b : ℕ) (ha : a ≤ w) (hb : b ≤ w)
    (hconn : 2 * w ≤ a + b + 1)
    (hleft : 2 ≤ 2 * w - 2 * a) (hright : 2 ≤ 2 * w - 2 * b) :
    False := by
  omega

/-- **And the repair is forced, not chosen.**  Dropping to `a = b = w - 1` bounces leaves
exactly two loose ends on each side -- the minimum `link_needs_two` demands -- at the cost
of splitting the edge into two chains instead of one.  That is precisely the spine+zigzag
("Through2") construction: strand `0` runs straight through as a spine and strands
`1 .. 2 * w - 1` zigzag, so every edge can reach both of its neighbours. -/
theorem two_chains_leave_two_each_side (w : ℕ) (hw : 1 ≤ w) :
    2 * w - 2 * (w - 1) = 2 := by
  omega

/-- **The count is tight.**  With `a + b` bounces an edge's strands fall into at least
`2 * w - (a + b)` chains, so leaving two loose ends on each side (`a = b = w - 1`) forces
at least two chains -- an edge interior to a run can never be internally connected. -/
theorem two_loose_each_side_forces_split (w a b : ℕ) (ha : a ≤ w) (hb : b ≤ w)
    (hleft : 2 ≤ 2 * w - 2 * a) (hright : 2 ≤ 2 * w - 2 * b) (hw : 1 ≤ w) :
    a + b + 2 ≤ 2 * w := by
  omega

end ZigzagParity

#print axioms ZigzagParity.loose_ends_one_sided
#print axioms ZigzagParity.pass_count_even
#print axioms ZigzagParity.link_needs_two
#print axioms ZigzagParity.single_chain_fails
#print axioms ZigzagParity.two_chains_leave_two_each_side
#print axioms ZigzagParity.two_loose_each_side_forces_split
