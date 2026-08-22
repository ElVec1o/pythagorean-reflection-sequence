/-
Assembling the walk-graph data from a lamp configuration.

The crossing map is `EndType.partner`.  The turn is chosen site by site: where the
arrivals and departures balance, `TurnBuild.exists_involution_of_card_eq` supplies
an involution swapping them; elsewhere the identity, which never arises for a
configuration whose travel indicator does not jump.  Gluing gives the global turn.

The three conditions the data asks of the pair are then the three already proved:
each map is an involution, each is fixed-point free where it acts, and they never
agree because one moves between the two sites of an edge while the other stays.
-/
import Mathlib.Tactic
import EndType
import TurnBuild

namespace DataBuild

open EndType TurnBuild

variable {n : ℕ} {m : Fin n → ℕ}

/-- The turn at one site: an involution swapping arrivals with departures when they
balance, and the identity otherwise. -/
noncomputable def turnAt (up : Fin n → ℕ) (s : ℤ) : Endpt n m → Endpt n m :=
  if h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card then
    (exists_involution_of_card_eq (arrAt (m := m) up s) (depAt (m := m) up s)
      (arrAt_disjoint_depAt up s) h).choose
  else id

/-- Where the site balances, the chosen map is an involution. -/
theorem turnAt_invol (up : Fin n → ℕ) (s : ℤ) :
    ∀ x : Endpt n m, turnAt up s (turnAt up s x) = x := by
  intro x
  unfold turnAt
  by_cases h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card
  · rw [dif_pos h]
    exact (exists_involution_of_card_eq (arrAt (m := m) up s) (depAt (m := m) up s)
      (arrAt_disjoint_depAt up s) h).choose_spec.1 x
  · rw [dif_neg h]; rfl

/-- It sends arrivals to departures. -/
theorem turnAt_arr (up : Fin n → ℕ) (s : ℤ)
    (h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    ∀ x ∈ arrAt (m := m) up s, turnAt up s x ∈ depAt (m := m) up s := by
  intro x hx
  unfold turnAt
  rw [dif_pos h]
  exact (exists_involution_of_card_eq (arrAt (m := m) up s) (depAt (m := m) up s)
    (arrAt_disjoint_depAt up s) h).choose_spec.2.1 x hx

/-- And fixes nothing that it moves. -/
theorem turnAt_ne (up : Fin n → ℕ) (s : ℤ)
    (h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    ∀ x ∈ arrAt (m := m) up s, turnAt up s x ≠ x := by
  intro x hx
  unfold turnAt
  rw [dif_pos h]
  exact (exists_involution_of_card_eq (arrAt (m := m) up s) (depAt (m := m) up s)
    (arrAt_disjoint_depAt up s) h).choose_spec.2.2.2.2.1 x hx

/-- The global turn. -/
noncomputable def turn (up : Fin n → ℕ) : Endpt n m → Endpt n m :=
  glue siteOf (turnAt up)

-- Certification (Rule 5).
#print axioms DataBuild.turnAt_invol
#print axioms DataBuild.turnAt_arr
#print axioms DataBuild.turnAt_ne

end DataBuild
