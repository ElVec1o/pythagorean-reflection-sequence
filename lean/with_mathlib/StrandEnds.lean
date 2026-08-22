/-
Strand ends, and the consistency of the two ways of assigning a sign.

A crossing of edge `j` has two ends, one at site `j` and one at site `j+1`.  It is
an up-crossing or a down-crossing.  From that primitive data everything else
follows:

* the **side** at a site: an end at site `s` coming from edge `s-1` is on the left,
  one coming from edge `s` is on the right, so `side = !atTop`;
* the **role**: an up-crossing arrives at its top end and departs from its bottom
  one, a down-crossing the reverse, so `isArr = (isUp == atTop)`;
* the **sign**, forced by `NoGapMerge.split_forced_pos/neg`: an up-crossing carries
  the opposite of its edge's deposit sign, a down-crossing carries it.

`sgn_agrees` checks that the sign computed this way, from the crossing direction,
is the sign `EndData.sgn` computes from the side and the role.  The two layers were
written independently, so their agreement is a real check rather than a
restatement: it fixes the side convention (`false` is left) and confirms the role
assignment.
-/
import Mathlib.Tactic
import EndData

namespace StrandEnds

/-- An end of a crossing: which edge, whether the crossing goes up, and which of
its two ends this is. -/
structure End where
  isUp : Bool
  atTop : Bool
  deriving DecidableEq, Fintype

/-- Left is `false`.  An end at a site coming from the edge below it sits on the
left, and that is the end at the top of that edge. -/
def side (e : End) : Bool := !e.atTop

/-- An up-crossing arrives at its top end; a down-crossing arrives at its bottom
end. -/
def isArr (e : End) : Bool := e.isUp == e.atTop

/-- The forced sign: opposite to the deposit sign for an up-crossing, equal to it
for a down-crossing. -/
def sgn (ds : Bool) (e : End) : Bool := if e.isUp then !ds else ds

/-- The `EndData` view of the same ends, with the deposit sign supplied per side. -/
def toData (ds : Bool → Bool) : EndData.Data End where
  side := side
  isArr := isArr
  depSign := ds

/-- **Cross-layer consistency.**  The sign obtained from the crossing direction
agrees with the sign `EndData.sgn` derives from side and role, for every end and
every deposit sign.  Sixteen cases, decided. -/
theorem sgn_agrees : ∀ (ds : Bool → Bool) (e : End),
    EndData.sgn (toData ds) e = sgn (ds (side e)) e := by decide

/-- An up-crossing's two ends are one arrival and one departure. -/
theorem up_roles : ∀ e : End, e.isUp = true →
    (isArr e = e.atTop) := by decide

/-- The two ends of a crossing sit on opposite sides. -/
theorem sides_differ : ∀ e f : End, e.isUp = f.isUp → e.atTop ≠ f.atTop →
    side e ≠ side f := by decide

/-! ### Non-vacuity: all four end kinds occur, with the expected roles. -/

theorem up_top_is_arrival : isArr ⟨true, true⟩ = true := by decide
theorem up_bottom_is_departure : isArr ⟨true, false⟩ = false := by decide
theorem down_top_is_departure : isArr ⟨false, true⟩ = false := by decide
theorem down_bottom_is_arrival : isArr ⟨false, false⟩ = true := by decide

/-- A left arrival carries the opposite of its deposit sign, which is the content
of the forced split. -/
theorem left_arrival_sign : ∀ ds : Bool, sgn ds ⟨true, true⟩ = !ds := by decide

-- Certification (Rule 5).
#print axioms StrandEnds.sgn_agrees
#print axioms StrandEnds.up_roles
#print axioms StrandEnds.sides_differ
#print axioms StrandEnds.up_top_is_arrival
#print axioms StrandEnds.down_bottom_is_arrival
#print axioms StrandEnds.left_arrival_sign

end StrandEnds
