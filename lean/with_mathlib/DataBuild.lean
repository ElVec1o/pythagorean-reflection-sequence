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
import WalkGraph

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

/-- The turn fixes nothing among the departures either. -/
theorem turnAt_ne_dep (up : Fin n → ℕ) (s : ℤ)
    (h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    ∀ x ∈ depAt (m := m) up s, turnAt up s x ≠ x := by
  intro x hx
  unfold turnAt
  rw [dif_pos h]
  exact (exists_involution_of_card_eq (arrAt (m := m) up s) (depAt (m := m) up s)
    (arrAt_disjoint_depAt up s) h).choose_spec.2.2.2.2.2 x hx

/-- **Every end lies at its own site**, as an arrival or a departure.  This is what
makes the site-local statements apply to it, since `siteOf` is a function and the
role predicate is total. -/
theorem mem_own_site (up : Fin n → ℕ) (x : Endpt n m) :
    x ∈ arrAt (m := m) up (siteOf x) ∨ x ∈ depAt (m := m) up (siteOf x) := by
  classical
  by_cases h : isArrOf up x = true
  · exact Or.inl ((mem_arrAt up (siteOf x) x).mpr ⟨rfl, h⟩)
  · refine Or.inr ((mem_depAt up (siteOf x) x).mpr ⟨rfl, ?_⟩)
    simpa using h

/-- **The glued turn is fixed-point free.**  At each end the glue is the turn at
that end's own site, and the end is an arrival or a departure there, so one of the
two site-local statements applies. -/
theorem turn_ne (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    ∀ x : Endpt n m, turn up x ≠ x := by
  intro x
  unfold turn glue
  rcases mem_own_site up x with h | h
  · exact turnAt_ne up (siteOf x) (hbal _) x h
  · exact turnAt_ne_dep up (siteOf x) (hbal _) x h

/-- The turn sends departures to arrivals as well. -/
theorem turnAt_dep (up : Fin n → ℕ) (s : ℤ)
    (h : (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    ∀ x ∈ depAt (m := m) up s, turnAt up s x ∈ arrAt (m := m) up s := by
  intro x hx
  unfold turnAt
  rw [dif_pos h]
  exact (exists_involution_of_card_eq (arrAt (m := m) up s) (depAt (m := m) up s)
    (arrAt_disjoint_depAt up s) h).choose_spec.2.2.1 x hx

/-- **The turn preserves sites.**  It pairs arrivals with departures at one site, so
an end's image lies at that same site.  This is what the glue's involutivity
needs. -/
theorem turnAt_site (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (x : Endpt n m) : siteOf (turnAt up (siteOf x) x) = siteOf x := by
  classical
  rcases mem_own_site up x with h | h
  · exact ((mem_depAt up (siteOf x) _).mp (turnAt_arr up (siteOf x) (hbal _) x h)).1
  · exact ((mem_arrAt up (siteOf x) _).mp (turnAt_dep up (siteOf x) (hbal _) x h)).1

/-- The glued turn is an involution. -/
theorem turn_invol (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    ∀ x : Endpt n m, turn up (turn up x) = x :=
  glue_invol siteOf (turnAt up) (fun s x => turnAt_invol up s x) (turnAt_site up hbal)

/-- **The walk-graph data of a lamp configuration.**  Every field is one of the
constructions above and every proof one of the lemmas; the single hypothesis is
that arrivals and departures balance at every site, which the travel indicator
being locally constant provides. -/
noncomputable def dataOf (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card) :
    WalkGraph.Data (Endpt n m) where
  p := partner
  t := turn up
  p_invol := partner_invol
  t_invol := turn_invol up hbal
  p_ne := partner_ne
  t_ne := turn_ne up hbal
  pt_ne := partner_ne_turn siteOf partner (turn up)
    (fun x => partner_site_ne x) (fun x => turnAt_site up hbal x)

/-- **The turn flips the role.**  An arrival's turn is a departure and a departure's
turn is an arrival.  Both directions were already available at a fixed site
(`turnAt_arr`, `turnAt_dep`); this glues them into a statement about `turn`. -/
theorem turn_arr_flip (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (x : Endpt n m) :
    EndType.isArrOf up (turn up x) = !EndType.isArrOf up x := by
  unfold turn glue
  by_cases h : EndType.isArrOf up x = true
  · have hx : x ∈ arrAt (m := m) up (EndType.siteOf x) :=
      (EndType.mem_arrAt up _ x).mpr ⟨rfl, h⟩
    have := (EndType.mem_depAt up (EndType.siteOf x) _).mp
      (turnAt_arr up (EndType.siteOf x) (hbal _) x hx)
    rw [this.2, h]
    rfl
  · simp only [Bool.not_eq_true] at h
    have hx : x ∈ depAt (m := m) up (EndType.siteOf x) :=
      (EndType.mem_depAt up _ x).mpr ⟨rfl, h⟩
    have := (EndType.mem_arrAt up (EndType.siteOf x) _).mp
      (turnAt_dep up (EndType.siteOf x) (hbal _) x hx)
    rw [this.2, h]
    rfl

-- Certification (Rule 5).

#print axioms DataBuild.turnAt_invol
#print axioms DataBuild.turnAt_arr
#print axioms DataBuild.turnAt_ne
#print axioms DataBuild.turnAt_ne_dep
#print axioms DataBuild.mem_own_site
#print axioms DataBuild.turn_ne
#print axioms DataBuild.turnAt_site
#print axioms DataBuild.turn_invol
#print axioms DataBuild.dataOf

end DataBuild
#print axioms DataBuild.turn_arr_flip
