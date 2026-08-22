/-
Building the turn from the balance.

At a site the arrivals and the departures are disjoint and, by the balance already
proved, equinumerous.  Any bijection between them extends to an involution of the
whole end type: pair each arrival with its image, each departure with its preimage,
and fix everything else.

This is the local half of the turn.  The global turn is the union over sites, which
is well defined because each end lies at exactly one site.
-/
import Mathlib.Tactic

namespace TurnBuild

variable {α : Type*} [DecidableEq α]

/-- **The local turn.**  Equinumerous disjoint sets admit an involution swapping
them and fixing everything else. -/
theorem exists_involution_of_card_eq (A D : Finset α)
    (hdisj : Disjoint A D) (hcard : A.card = D.card) :
    ∃ t : α → α,
      (∀ x, t (t x) = x) ∧
      (∀ x ∈ A, t x ∈ D) ∧ (∀ x ∈ D, t x ∈ A) ∧
      (∀ x, x ∉ A → x ∉ D → t x = x) ∧
      (∀ x ∈ A, t x ≠ x) ∧ (∀ x ∈ D, t x ≠ x) := by
  classical
  obtain ⟨e⟩ : Nonempty (A ≃ D) := ⟨Finset.equivOfCardEq hcard⟩
  refine ⟨fun x =>
    if hA : x ∈ A then (e ⟨x, hA⟩ : α)
    else if hD : x ∈ D then (e.symm ⟨x, hD⟩ : α)
    else x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hA : x ∈ A
    · have hmem : (e ⟨x, hA⟩ : α) ∈ D := (e ⟨x, hA⟩).2
      have hnA : (e ⟨x, hA⟩ : α) ∉ A := fun h => (Finset.disjoint_left.mp hdisj h) hmem
      simp only [dif_pos hA, dif_neg hnA, dif_pos hmem]
      have : (⟨(e ⟨x, hA⟩ : α), hmem⟩ : {y // y ∈ D}) = e ⟨x, hA⟩ := rfl
      rw [this, Equiv.symm_apply_apply]
    · by_cases hD : x ∈ D
      · have hmem : (e.symm ⟨x, hD⟩ : α) ∈ A := (e.symm ⟨x, hD⟩).2
        simp only [dif_neg hA, dif_pos hD, dif_pos hmem]
        have : (⟨(e.symm ⟨x, hD⟩ : α), hmem⟩ : {y // y ∈ A}) = e.symm ⟨x, hD⟩ := rfl
        rw [this, Equiv.apply_symm_apply]
      · simp [hA, hD]
  · intro x hx; simp only [dif_pos hx]; exact (e ⟨x, hx⟩).2
  · intro x hx
    have hnA : x ∉ A := fun h => (Finset.disjoint_left.mp hdisj h) hx
    simp only [dif_neg hnA, dif_pos hx]; exact (e.symm ⟨x, hx⟩).2
  · intro x hA hD; simp [hA, hD]
  · intro x hx hcon
    have hmem : (e ⟨x, hx⟩ : α) ∈ D := (e ⟨x, hx⟩).2
    simp only [dif_pos hx] at hcon
    exact (Finset.disjoint_left.mp hdisj hx) (hcon ▸ hmem)
  · intro x hx hcon
    have hnA : x ∉ A := fun h => (Finset.disjoint_left.mp hdisj h) hx
    have hmem : (e.symm ⟨x, hx⟩ : α) ∈ A := (e.symm ⟨x, hx⟩).2
    simp only [dif_neg hnA, dif_pos hx] at hcon
    exact hnA (hcon ▸ hmem)

-- Certification (Rule 5).
#print axioms TurnBuild.exists_involution_of_card_eq

end TurnBuild
