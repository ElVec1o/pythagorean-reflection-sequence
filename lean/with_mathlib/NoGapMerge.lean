/-
The arithmetic core of M6 (no gap edge implies no isolated cycles).

Three ingredients are formalised here.

* `split_forced_pos` / `split_forced_neg`: at minimum crossing multiplicity the
  sign split of an edge is forced, so every up-crossing of an edge carries one
  sign and every down-crossing the other.  This is what makes the pair cost
  depend only on the side pattern.
* `passfree_worse`: a pass-free pairing costs `|d_L| + |d_R|` against a minimum of
  `max |d_L| |d_R|`, so it is not optimal when both deposits are non-zero.  With a
  vanishing travel indicator a zero deposit means a gap edge, so under the no-gap
  hypothesis every min-cost pairing has a pass (the forced-pass lemma).
* `swap_free_iff`: a 2-swap is free exactly when the two pairs share an arrival
  side or a departure side.  Sides are `Bool`; the pair cost is `2` for a bounce
  and `1` for a pass, which is the specialisation justified by the first item.
-/
import Mathlib.Tactic

namespace NoGapMerge

/-- Pair cost once the sign split is forced: `2` for a bounce, `1` for a pass. -/
def pcost (x y : Bool) : ℤ := if x = y then 2 else 1

/-- Cost change of the 2-swap `(a → d), (a' → d') ↦ (a → d'), (a' → d)`. -/
def swapDelta (a d a' d' : Bool) : ℤ :=
  (pcost a d' + pcost a' d) - (pcost a d + pcost a' d')

/-- A 2-swap is free exactly when the arrivals share a side or the departures do.
    Sixteen side patterns, decided exhaustively. -/
theorem swap_free_iff : ∀ a d a' d' : Bool,
    swapDelta a d a' d' = 0 ↔ (a = a' ∨ d = d') := by decide

/-- The only cost-lowering swaps: opposite bounces.  These cannot occur in a
    cost-minimal realisation, which is what rules out the blocking configuration. -/
theorem swap_neg_iff : ∀ a d a' d' : Bool,
    swapDelta a d a' d' < 0 ↔ (a ≠ a' ∧ d ≠ d' ∧ a = d) := by decide

/-- A component with a bounce at a shared site always merges at no cost:
    if one pair is a bounce, the swap is never strictly positive. -/
theorem bounce_never_blocks : ∀ a a' d' : Bool,
    swapDelta a a a' d' ≤ 0 := by decide

/-- At minimum multiplicity the sign split is forced to `p^u = 0`: every
    up-crossing carries the sign opposite to the deposit.  The sign of `d` is not
    needed; the cap `pd ≤ dn` alone forces it. -/
theorem split_forced_pos {f d pu pd u dn : ℤ}
    (hu : 2 * u = d + f) (hdn : 2 * dn = d - f)
    (hpd : 2 * pd = 2 * pu + d - f) (h1 : 0 ≤ pu) (h3 : pd ≤ dn) :
    pu = 0 := by omega

/-- The mirror case: `p^u = u`, again without needing the sign of `d`. -/
theorem split_forced_neg {f d pu pd u dn : ℤ}
    (hu : 2 * u = -d + f) (hdn : 2 * dn = -d - f)
    (hpd : 2 * pd = 2 * pu + d - f) (h2 : 0 ≤ pd) (h4 : pu ≤ u) :
    pu = u := by omega

/-- A pass-free pairing costs the sum of the two deposit magnitudes, against a
    minimum of their maximum; with both non-zero it is strictly worse. -/
theorem passfree_worse {A B : ℤ} (hA : 0 < A) (hB : 0 < B) : max A B < A + B := by
  rcases le_total A B with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-- Contrapositive form: if a pass-free pairing is optimal then one deposit
    vanishes.  With a vanishing travel indicator that edge is a gap edge. -/
theorem passfree_optimal_imp_zero {A B : ℤ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A + B ≤ max A B) : A = 0 ∨ B = 0 := by
  by_contra hc
  push Not at hc
  exact absurd h (not_le.mpr (passfree_worse (lt_of_le_of_ne hA (Ne.symm hc.1))
    (lt_of_le_of_ne hB (Ne.symm hc.2))))

/-- **At a cost minimum, a bounce forces a shared side.**  This is the step that
turns the shared-site argument into the pair the merge needs: if one component has
a bounce at a shared site, then against *any* pair of another component the two
either share an arrival side or share a departure side, so the swap is free.

`bounce_never_blocks` gives `Delta ≤ 0`; cost-minimality gives `Delta ≥ 0`, since a
strictly negative `Delta` would exhibit a cheaper realisation; so `Delta = 0` and
`swap_free_iff` reads off the shared side. -/
theorem shared_side_of_bounce (a a' d' : Bool)
    (hmin : 0 ≤ swapDelta a a a' d') :
    a = a' ∨ a = d' := by
  have hle : swapDelta a a a' d' ≤ 0 := bounce_never_blocks a a' d'
  have hzero : swapDelta a a a' d' = 0 := le_antisymm hle hmin
  exact (swap_free_iff a a a' d').mp hzero

/-- The contrapositive: if neither side is shared, the bounce swap is strictly
cheaper, so the realisation was not cost-minimal. -/
theorem not_min_of_bounce_unshared : ∀ a a' d' : Bool,
    a ≠ a' → a ≠ d' → swapDelta a a a' d' < 0 := by decide

-- Certification (Rule 5): every declaration above, axioms listed in the build log.
#print axioms NoGapMerge.swap_free_iff
#print axioms NoGapMerge.swap_neg_iff
#print axioms NoGapMerge.bounce_never_blocks
#print axioms NoGapMerge.split_forced_pos
#print axioms NoGapMerge.split_forced_neg
#print axioms NoGapMerge.passfree_worse
#print axioms NoGapMerge.passfree_optimal_imp_zero
#print axioms NoGapMerge.shared_side_of_bounce
#print axioms NoGapMerge.not_min_of_bounce_unshared

end NoGapMerge
