/-
  TravelParity.lean
  =================
  Where the crossing count `mu` is odd, and what that forces.

  `SiteCost.PathData.mu_par` (Realisation.lean) says `mu j = travel k* j (mod 2)`, and
  `travel` only ever takes the values `-1, 0, 1`.  So `mu j` is ODD exactly where the
  travel indicator does not vanish -- that is, exactly on the half-open interval between
  `0` and `k*`.

  The consequence is the structural one.  At a site `s` the ends present are those of
  edge `s - 1` and those of edge `s`, so a pairing of all of them (a "turn") can exist
  only if `mu (s-1) + mu s` is even.  `site_parity_defect` below pins the failures down:
  the sum is odd at exactly two sites, `0` and `k*` (and at none at all when `k* = 0`).

  That is why the group-element model cannot live on `EndType.Endpt` alone, and why
  `EltBridge.VEndpt n mm := Endpt n mm (+) Bool` carries exactly TWO extra points: they
  are the two ends of a single virtual strand spanning the travel interval, repairing
  the parity at those two sites and nowhere else.  Interior travel sites are already
  even (odd + odd), which is why two points suffice rather than one per edge.

  No `sorry`.
-/

import Realisation

namespace TravelParity

open SiteCost

variable (P : SiteCost.PathData)

/-- **`mu` is odd exactly on the travel interval.**  Immediate from `mu_par` together
with the fact that `travel` takes only the values `-1, 0, 1`: the congruence
`mu j = travel k* j (mod 2)` leaves `mu j` even precisely when the indicator vanishes. -/
theorem mu_odd_iff_mem (j : ℤ) :
    P.mu j % 2 = 1 ↔ ((0 ≤ j ∧ j < P.kstar) ∨ (P.kstar ≤ j ∧ j < 0)) := by
  have hp := P.mu_par j
  have hc := SiteCost.travel_cases P.kstar j
  unfold SiteCost.travel at hp hc
  split_ifs at hp hc <;> omega

/-- **And even off it.** -/
theorem mu_even_iff_not_mem (j : ℤ) :
    P.mu j % 2 = 0 ↔ ¬((0 ≤ j ∧ j < P.kstar) ∨ (P.kstar ≤ j ∧ j < 0)) := by
  have h := mu_odd_iff_mem P j
  omega

/-- **The parity defect sits at exactly two sites.**  A turn at site `s` pairs up the
ends of edge `s - 1` with those of edge `s`, so it needs `mu (s-1) + mu s` even.  That
sum is odd exactly at `s = 0` and `s = k*` -- the two endpoints of the travel interval --
and never when `k* = 0`.  Two sites, hence the two virtual points of `VEndpt`. -/
theorem site_parity_defect (s : ℤ) :
    (P.mu (s - 1) + P.mu s) % 2 = 1 ↔ (P.kstar ≠ 0 ∧ (s = 0 ∨ s = P.kstar)) := by
  have h1 := mu_odd_iff_mem P (s - 1)
  have h2 := mu_odd_iff_mem P s
  omega

/-- **Interior travel sites are balanced.**  Strictly inside the travel interval both
adjacent edges carry odd `mu`, so their sum is even and no repair is needed there.  This
is what makes ONE virtual strand enough: it contributes ends only at its two endpoints. -/
theorem interior_travel_site_even (s : ℤ)
    (h : ((0 ≤ s - 1 ∧ s - 1 < P.kstar) ∨ (P.kstar ≤ s - 1 ∧ s - 1 < 0))
      ∧ ((0 ≤ s ∧ s < P.kstar) ∨ (P.kstar ≤ s ∧ s < 0))) :
    (P.mu (s - 1) + P.mu s) % 2 = 0 := by
  have h1 := mu_odd_iff_mem P (s - 1)
  have h2 := mu_odd_iff_mem P s
  omega

/-- **Off the travel interval every site is balanced too.**  Both edges carry even `mu`,
so the sum is even.  Combined with `interior_travel_site_even`, the only failures are the
two boundary sites `site_parity_defect` names. -/
theorem off_travel_site_even (s : ℤ)
    (h1 : ¬((0 ≤ s - 1 ∧ s - 1 < P.kstar) ∨ (P.kstar ≤ s - 1 ∧ s - 1 < 0)))
    (h2 : ¬((0 ≤ s ∧ s < P.kstar) ∨ (P.kstar ≤ s ∧ s < 0))) :
    (P.mu (s - 1) + P.mu s) % 2 = 0 := by
  have e1 := mu_odd_iff_mem P (s - 1)
  have e2 := mu_odd_iff_mem P s
  omega

/-- **When the cursor is at the origin there is no defect anywhere.**  `travel` vanishes
identically, so every `mu` is even and a turn exists on `Endpt` alone. -/
theorem no_defect_of_kstar_zero (hk : P.kstar = 0) (s : ℤ) :
    (P.mu (s - 1) + P.mu s) % 2 = 0 := by
  have h := site_parity_defect P s
  omega

end TravelParity

#print axioms TravelParity.mu_odd_iff_mem
#print axioms TravelParity.mu_even_iff_not_mem
#print axioms TravelParity.site_parity_defect
#print axioms TravelParity.interior_travel_site_even
#print axioms TravelParity.off_travel_site_even
#print axioms TravelParity.no_defect_of_kstar_zero
