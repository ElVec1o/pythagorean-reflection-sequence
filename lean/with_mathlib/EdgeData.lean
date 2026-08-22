/-
Edge data, and the two arithmetic steps that gap-freeness buys.

Each edge of the span carries a deposit `d` and a travel indicator `f ∈ {-1,0,1}`,
subject to the parity `d ≡ f (mod 2)`.  A *gap edge* is one with `d = 0` and
`f = 0`.

Two steps of `thm:nogap` live here.  `dep_ne_zero_of_not_gap` is step 2: away from
gap edges the deposit never vanishes, because a vanishing deposit forces `f` even,
hence `f = 0` in the allowed range, hence a gap.  `mult_eq_abs_dep` is step 3's
first half: the minimum crossing multiplicity `max |d| |f|` is then `|d|`, which is
what makes the sign split forced in `NoGapMerge.split_forced_pos/neg`.
-/
import Mathlib.Tactic

namespace EdgeData

/-- The travel indicator takes only three values. -/
def IsTravel (f : ℤ) : Prop := f = -1 ∨ f = 0 ∨ f = 1

/-- A gap edge: no deposit and no travel. -/
def IsGap (d f : ℤ) : Prop := d = 0 ∧ f = 0

/-- **Step 2.** Off a gap edge the deposit is non-zero.  A vanishing deposit makes
`f` even by parity, and the only even travel indicator is `0`, which would be a
gap. -/
theorem dep_ne_zero_of_not_gap {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hgap : ¬ IsGap d f) : d ≠ 0 := by
  intro hd
  apply hgap
  refine ⟨hd, ?_⟩
  rcases hf with h | h | h <;> subst h <;> omega

/-- **Step 3, first half.** With a non-zero deposit the minimum multiplicity is the
absolute deposit: `|d| ≥ |f|` in both parities. -/
theorem one_le_abs {d : ℤ} (hd : d ≠ 0) : 1 ≤ |d| := by
  rcases abs_cases d with ⟨he, _⟩ | ⟨he, _⟩ <;> omega

theorem abs_dep_ge_abs_trav {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hd : d ≠ 0) : |f| ≤ |d| := by
  have h1 : 1 ≤ |d| := one_le_abs hd
  rcases hf with h | h | h <;> subst h
  · simpa using h1
  · simpa using abs_nonneg d
  · simpa using h1

theorem mult_eq_abs_dep {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hd : d ≠ 0) : max |d| |f| = |d| :=
  max_eq_left (abs_dep_ge_abs_trav hf hpar hd)

/-- The two together: a non-gap edge has non-zero deposit and multiplicity `|d|`. -/
theorem nongap_mult {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hgap : ¬ IsGap d f) : d ≠ 0 ∧ max |d| |f| = |d| :=
  let hd := dep_ne_zero_of_not_gap hf hpar hgap
  ⟨hd, mult_eq_abs_dep hf hpar hd⟩

/-- And the multiplicity is at least one, which is the covering hypothesis
`SharedSite.shared_site_exists` needs: every span edge carries a crossing. -/
theorem mult_pos {d f : ℤ} (hf : IsTravel f) (hpar : (d - f) % 2 = 0)
    (hgap : ¬ IsGap d f) : 1 ≤ max |d| |f| := by
  obtain ⟨hd, hm⟩ := nongap_mult hf hpar hgap
  rw [hm]
  exact one_le_abs hd

/-! ### Non-vacuity -/

/-- A bulk edge: even deposit, no travel.  Not a gap, deposit non-zero,
multiplicity `2`. -/
theorem witness_bulk : (2 : ℤ) ≠ 0 ∧ max |(2:ℤ)| |(0:ℤ)| = 2 :=
  nongap_mult (Or.inr (Or.inl rfl)) (by decide) (by simp [IsGap])

/-- A travel edge: odd deposit, travel `1`.  Multiplicity `1`. -/
theorem witness_travel : (1 : ℤ) ≠ 0 ∧ max |(1:ℤ)| |(1:ℤ)| = 1 :=
  nongap_mult (Or.inr (Or.inr rfl)) (by decide) (by simp [IsGap])

/-- The gap edge really is excluded rather than the hypothesis being unsatisfiable:
`d = f = 0` satisfies the travel and parity conditions but *is* a gap. -/
theorem witness_gap_excluded : IsTravel 0 ∧ ((0:ℤ) - 0) % 2 = 0 ∧ IsGap 0 0 :=
  ⟨Or.inr (Or.inl rfl), by decide, ⟨rfl, rfl⟩⟩

/-- And a gap edge has multiplicity `0`, which is why reachability has to force it
to `2`: the covering hypothesis fails there. -/
theorem witness_gap_mult_zero : max |(0:ℤ)| |(0:ℤ)| = 0 := by decide

/-! ### The arrival/departure balance

The turn pairs arrivals with departures at a site, so it exists only where those
counts agree.  Writing `u` and `dn` for the up- and down-crossings of an edge, with
`2u = m + f` and `2dn = m - f`, the arrivals at a site are the up-crossings of the
edge below and the down-crossings of the edge above, and the departures are the
other two.  Balance is therefore

    u (s-1) + dn s  =  dn (s-1) + u s

which, since `u - dn = f` on every edge, is exactly `f (s-1) = f s`.  So the
condition is not an extra assumption: it is the travel indicator being locally
constant, which holds away from the two marker sites and is restored at them by the
virtual ends. -/

/-- **Balance from local constancy of the travel indicator.** -/
theorem balance_of_travel_eq {mLo mHi fLo fHi uLo uHi dnLo dnHi : ℤ}
    (huLo : 2 * uLo = mLo + fLo) (hdnLo : 2 * dnLo = mLo - fLo)
    (huHi : 2 * uHi = mHi + fHi) (hdnHi : 2 * dnHi = mHi - fHi)
    (hf : fLo = fHi) :
    uLo + dnHi = dnLo + uHi := by omega

/-- Conversely, balance forces the travel indicator to agree: the two are the same
condition, so a site where the indicator jumps cannot balance without a virtual
end. -/
theorem travel_eq_of_balance {mLo mHi fLo fHi uLo uHi dnLo dnHi : ℤ}
    (huLo : 2 * uLo = mLo + fLo) (hdnLo : 2 * dnLo = mLo - fLo)
    (huHi : 2 * uHi = mHi + fHi) (hdnHi : 2 * dnHi = mHi - fHi)
    (hbal : uLo + dnHi = dnLo + uHi) :
    fLo = fHi := by omega

/-- The travel indicator is locally constant away from `0` and `k`: it changes only
where a virtual end sits.  Stated on the three-valued range. -/
theorem travel_const_away {f : ℤ → ℤ} {s k : ℤ}
    (hs : ∀ j, f j = (if 0 ≤ j ∧ j < k then 1 else if k ≤ j ∧ j < 0 then -1 else 0))
    (h1 : s ≠ 0) (h2 : s ≠ k) : f (s - 1) = f s := by
  rw [hs (s - 1), hs s]
  split_ifs <;> omega

/-! ### The balance in up-count form

Counting at a site splits by which of the two adjacent edges an end comes from.  An
arrival at site `s` is either a top end of edge `s-1`, which makes it an
up-crossing, or a bottom end of edge `s`, which makes it a down-crossing.  So

    arrivals   = up (s-1) + (m s - up s)
    departures = (m (s-1) - up (s-1)) + up s

and the balance between them is the arithmetic below.  With `2 up = m + f` on each
edge it is again just `f (s-1) = f s`, so the count form and the earlier form say
the same thing. -/

theorem card_balance_of_travel_eq {mLo mHi upLo upHi fLo fHi : ℤ}
    (hLo : 2 * upLo = mLo + fLo) (hHi : 2 * upHi = mHi + fHi) (hf : fLo = fHi) :
    upLo + (mHi - upHi) = (mLo - upLo) + upHi := by omega

/-- And conversely, so the count balance is equivalent to the indicator not
jumping, exactly as the crossing-count form was. -/
theorem travel_eq_of_card_balance {mLo mHi upLo upHi fLo fHi : ℤ}
    (hLo : 2 * upLo = mLo + fLo) (hHi : 2 * upHi = mHi + fHi)
    (hbal : upLo + (mHi - upHi) = (mLo - upLo) + upHi) :
    fLo = fHi := by omega

/-! ### The balance in natural-number form

The counts return natural numbers with truncated subtraction, while the balance was
proved over the integers.  With the up-count bounded by the crossing count on each
edge the two minima collapse and the subtraction is exact, so the integer identity
transfers. -/

/-- The balance as the counts state it, from the up-count relation in natural
numbers.  `2 upLo + mHi = 2 upHi + mLo` is what `2 up = m + f` and `fLo = fHi`
give once the indicator is eliminated. -/
theorem nat_balance {mLo mHi upLo upHi : ℕ}
    (hLo : upLo ≤ mLo) (hHi : upHi ≤ mHi)
    (h : 2 * upLo + mHi = 2 * upHi + mLo) :
    min upLo mLo + (mHi - min upHi mHi) = (mLo - min upLo mLo) + min upHi mHi := by
  rw [min_eq_left hLo, min_eq_left hHi]
  omega

/-- Eliminating the indicator: equal indicators on the two edges is exactly the
relation the natural-number balance needs. -/
theorem nat_balance_hyp_of_travel {mLo mHi upLo upHi : ℕ} {fLo fHi : ℤ}
    (hLo : 2 * (upLo : ℤ) = (mLo : ℤ) + fLo)
    (hHi : 2 * (upHi : ℤ) = (mHi : ℤ) + fHi)
    (hf : fLo = fHi) :
    2 * upLo + mHi = 2 * upHi + mLo := by
  have : 2 * (upLo : ℤ) + (mHi : ℤ) = 2 * (upHi : ℤ) + (mLo : ℤ) := by omega
  exact_mod_cast this

-- Certification (Rule 5).
#print axioms EdgeData.dep_ne_zero_of_not_gap
#print axioms EdgeData.one_le_abs
#print axioms EdgeData.abs_dep_ge_abs_trav
#print axioms EdgeData.mult_eq_abs_dep
#print axioms EdgeData.nongap_mult
#print axioms EdgeData.mult_pos
#print axioms EdgeData.witness_bulk
#print axioms EdgeData.witness_travel
#print axioms EdgeData.witness_gap_excluded
#print axioms EdgeData.witness_gap_mult_zero
#print axioms EdgeData.balance_of_travel_eq
#print axioms EdgeData.travel_eq_of_balance
#print axioms EdgeData.travel_const_away
#print axioms EdgeData.card_balance_of_travel_eq
#print axioms EdgeData.travel_eq_of_card_balance
#print axioms EdgeData.nat_balance
#print axioms EdgeData.nat_balance_hyp_of_travel

end EdgeData
