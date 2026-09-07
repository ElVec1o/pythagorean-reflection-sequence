/-
  BoundedDrift.lean
  =================
  The bounded-drift statement, proved: consecutive configurations along a generator step
  differ by a RANK-ONE update of the deposit vector plus a cursor shift of at most one.

  This is the "walker moves one step and only a few lamps toggle" picture, made precise
  and checked.  In this model the drift is not merely bounded, it is exactly one
  coordinate:

    * `s1` and `s2` do not move the deposit vector or the cursor AT ALL
      (`s1_d_eq`, `s2_d_eq`, `s1_kstar_eq`, `s2_kstar_eq` -- all `rfl`);
    * `s3` moves the cursor by exactly one and changes `d` at exactly ONE edge, the
      crossed one (`s3_d_off`, `s3_kstar_dist`), the change there being `-+ eps`, of
      absolute value one (`s3_d_at`).

  So along a walk of length `L` the deposit vector accumulates at most `L` single-coordinate
  updates, and the support of the difference between the endpoints has size at most `L`:
  `drift_support_card` below.  Storage of a trajectory is therefore the initial vector plus
  one (edge, delta) pair per step, not a fresh vector per step.

  What this does NOT say, and the distinction matters before it is transported anywhere:
  these are statements about the group's OWN configurations -- the deposit vector `d` of a
  `PathData` -- not about a basis extracted from an arbitrary matrix.  Nothing here asserts
  that a generic trained weight matrix admits such a decomposition; see the note at the end
  of the accompanying README block.

  No `sorry`.
-/

import EltBridge

namespace BoundedDrift

open EltBridge EltBridge.Elt

variable (g : EltBridge.Elt)

/-! ### `s1` and `s2` do not drift at all -/

theorem s1_d_eq : (s1 g).d = g.d := rfl
theorem s2_d_eq : (s2 g).d = g.d := rfl
theorem s1_kstar_eq : (s1 g).kstar = g.kstar := rfl
theorem s2_kstar_eq : (s2 g).kstar = g.kstar := rfl

/-! ### `s3` drifts by one coordinate and one cursor step -/

/-- The edge `s3` crosses: `kstar` when `delta`, `kstar - 1` otherwise. -/
def crossed : ℤ := if g.delta then g.kstar else g.kstar - 1

/-- **The cursor moves by exactly one.** -/
theorem s3_kstar_dist : ((s3 g).kstar - g.kstar) ^ 2 = 1 := by
  by_cases h : g.delta = true
  · rw [show (s3 g).kstar = g.kstar + 1 from by rw [s3, dif_pos h]]; ring
  · rw [show (s3 g).kstar = g.kstar - 1 from by rw [s3, dif_neg h]]; ring

/-- **Off the crossed edge the deposit vector is untouched.**  This is the rank-one
statement: `d' - d` is supported on the single coordinate `crossed g`. -/
theorem s3_d_off (j : ℤ) (hj : j ≠ crossed g) : (s3 g).d j = g.d j := by
  by_cases h : g.delta = true
  · have hd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
      rw [s3, dif_pos h]
    have : j ≠ g.kstar := by simpa [crossed, h] using hj
    rw [hd, Function.update_of_ne this]
  · have hd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
      rw [s3, dif_neg h]
    have : j ≠ g.kstar - 1 := by simpa [crossed, h] using hj
    rw [hd, Function.update_of_ne this]

/-- **And at the crossed edge it moves by exactly one**, since `eps = +-1`. -/
theorem s3_d_at : ((s3 g).d (crossed g) - g.d (crossed g)) ^ 2 = 1 := by
  have he := g.heps
  by_cases h : g.delta = true
  · have hd : (s3 g).d = Function.update g.d g.kstar (g.d g.kstar - g.eps) := by
      rw [s3, dif_pos h]
    have hc : crossed g = g.kstar := by simp [crossed, h]
    rw [hc, hd, Function.update_self]
    rcases he with he | he <;> rw [he] <;> ring
  · have hd : (s3 g).d = Function.update g.d (g.kstar - 1) (g.d (g.kstar - 1) + g.eps) := by
      rw [s3, dif_neg h]
    have hc : crossed g = g.kstar - 1 := by simp [crossed, h]
    rw [hc, hd, Function.update_self]
    rcases he with he | he <;> rw [he] <;> ring

/-! ### Consequence: the drift support of a whole walk -/

/-- **Every generator step changes the deposit vector at no more than one coordinate.**
Stated as: the set of edges where the deposit differs is contained in a singleton. -/
theorem gen_drift_subsingleton (a b : EltBridge.Elt) (h : Gen a b) :
    ∃ p : ℤ, ∀ j : ℤ, j ≠ p → b.d j = a.d j := by
  rcases h with h | h | h
  · exact ⟨0, fun j _ => by rw [congrFun h.2.2.2 j]; rfl⟩
  · exact ⟨0, fun j _ => by rw [congrFun h.2.2.2 j]; rfl⟩
  · exact ⟨crossed a, fun j hj => by rw [congrFun h.2.2.2 j]; exact s3_d_off a j hj⟩

/-- **A walk of length `L` drifts on at most `L` coordinates.**  Induction on `Reaches`:
each step contributes at most one edge to the support of the difference, so the endpoints
of an `L`-step walk differ on a set of size at most `L`.  Storing a trajectory therefore
costs the initial vector plus one `(edge, sign)` pair per step. -/
theorem drift_support_card {n : ℕ} {g : EltBridge.Elt} (h : Reaches n g) :
    ∃ S : Finset ℤ, S.card ≤ n ∧ ∀ j : ℤ, j ∉ S → g.d j = EltBridge.Elt.one.d j := by
  induction h with
  | refl hsame =>
    exact ⟨∅, by simp, fun j _ => by rw [congrFun hsame.2.2.2 j]⟩
  | @step m a b hreach hgen ih =>
    obtain ⟨S, hcard, hS⟩ := ih
    obtain ⟨p, hp⟩ := gen_drift_subsingleton a b hgen
    refine ⟨insert p S, ?_, fun j hj => ?_⟩
    · exact le_trans (Finset.card_insert_le _ _) (by omega)
    · have hjp : j ≠ p := fun hc => hj (by simp [hc])
      have hjS : j ∉ S := fun hc => hj (Finset.mem_insert_of_mem hc)
      rw [hp j hjp, hS j hjS]

end BoundedDrift

#print axioms BoundedDrift.s3_kstar_dist
#print axioms BoundedDrift.s3_d_off
#print axioms BoundedDrift.s3_d_at
#print axioms BoundedDrift.gen_drift_subsingleton
#print axioms BoundedDrift.drift_support_card
