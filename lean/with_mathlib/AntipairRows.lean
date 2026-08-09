/-
  AntipairRows.lean
  =================
  Paper 4, Corollary `cor:antipair` and Remark `rem:krows-shape`.

  The corollary asserts min over (n,j) of max{k(n,j), k(n+h,j)} = h-1 for h >= 2.  Its proof
  had two halves.  The attainment half is an explicit computation on the rows j = 0 and j = 1,
  where the closed formulas of `lem:krows` hold; that half is correct and is proved here.  The
  lower-bound half claimed that "the valley has width at most two and each step adds 2", which
  is false off those two rows, and the corollary now records its lower bound as verified rather
  than proved.  This file proves the attainment and refutes the false premise.

  Row formulas (`lem:krows`):
      k(n,0) = 2n for n >= 0,     k(n,0) = -2n-2 for n <= -1;
      k(n,1) = 2n+1 for n >= 0,   k(-1,1) = 0,   k(n,1) = -2n-3 for n <= -2.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace AntipairRows

/-- `le_or_lt` is not available under that name in this Mathlib; this is the same statement
    for the integers, which is all we need. -/
private theorem le_or_lt (a b : ℤ) : a ≤ b ∨ b < a := by omega

/-! ### 1. Attainment on row 0, for odd `h` -/

/-- With `h` odd and `n = -(h+1)/2`, both `k(n,0) = -2n-2` and `k(n+h,0) = 2(n+h)` equal
    `h-1`, so the maximum of the pair is exactly `h-1`. -/
theorem row0_attains {h n : ℤ} (hn : 2 * n = -(h + 1)) :
    (-2 * n - 2 = h - 1) ∧ (2 * (n + h) = h - 1) ∧
    max (-2 * n - 2) (2 * (n + h)) = h - 1 := by
  have h1 : -2 * n - 2 = h - 1 := by linarith
  have h2 : 2 * (n + h) = h - 1 := by linarith
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2, max_self]

/-- The index used is in the range the formulas require: `n <= -1` and `n + h >= 0`. -/
theorem row0_range {h n : ℤ} (hh : 2 ≤ h) (hn : 2 * n = -(h + 1)) :
    n ≤ -1 ∧ 0 ≤ n + h := by
  constructor <;> linarith

/-! ### 2. Attainment on row 1, for even `h` -/

/-- With `h` even and `n = -h/2 - 1`, both `k(n,1) = -2n-3` and `k(n+h,1) = 2(n+h)+1` equal
    `h-1`. -/
theorem row1_attains {h n : ℤ} (hn : 2 * n = -h - 2) :
    (-2 * n - 3 = h - 1) ∧ (2 * (n + h) + 1 = h - 1) ∧
    max (-2 * n - 3) (2 * (n + h) + 1) = h - 1 := by
  have h1 : -2 * n - 3 = h - 1 := by linarith
  have h2 : 2 * (n + h) + 1 = h - 1 := by linarith
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2, max_self]

theorem row1_range {h n : ℤ} (hh : 2 ≤ h) (hn : 2 * n = -h - 2) :
    n ≤ -2 ∧ 0 ≤ n + h := by
  constructor <;> linarith

/-! ### 3. Parity selects exactly one of the two rows

    For every `h >= 2` exactly one of the two constructions above is available, so the value
    `h-1` is attained for every `h`. -/

theorem parity_selects (h : ℤ) :
    (∃ n : ℤ, 2 * n = -(h + 1)) ∨ (∃ n : ℤ, 2 * n = -h - 2) := by
  rcases Int.even_or_odd h with ⟨k, hk⟩ | ⟨k, hk⟩
  · right; exact ⟨-k - 1, by omega⟩
  · left; exact ⟨-k - 1, by omega⟩

/-- **Attainment, for every `h >= 2`.**  (The identities themselves need no lower bound on
    `h`; `2 <= h` is what puts the witness in the range where the row formulas apply, which is
    `row0_range` and `row1_range`.) -/
theorem attains (h : ℤ) :
    ∃ n : ℤ, max (-2 * n - 2) (2 * (n + h)) = h - 1
           ∨ max (-2 * n - 3) (2 * (n + h) + 1) = h - 1 := by
  rcases parity_selects h with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact ⟨n, Or.inl (row0_attains hn).2.2⟩
  · exact ⟨n, Or.inr (row1_attains hn).2.2⟩

/-! ### 4. The lower bound, from the closed form of `lem:krows`

    `k` is given by the closed form
        j >= 1:  2n+2j-1 (n >= 0),  2j-2 (-j <= n <= -1),  -2n-3 (n <= -j-1)
        j <= 0:  2n (n >= -j),      -2j-1 (0 <= n <= -j-1), -2n-2j-2 (n <= -1)
    which is verified in the paper at every site with |n|,|j| <= 60.  Taking it as given, the
    lower bound `max{k(n,j), k(n+h,j)} >= h-1` is an elementary case analysis, done here.  This
    is what replaces the withdrawn valley argument refuted in section 5. -/

/-- The closed form on the rows `j <= 0`, written with `M = -j >= 0`. -/
noncomputable def kNonpos (M n : ℤ) : ℤ :=
  if M ≤ n then 2 * n else if 0 ≤ n then 2 * M - 1 else -2 * n + 2 * M - 2

/-- The closed form on the rows `j >= 1`. -/
noncomputable def kPos (j n : ℤ) : ℤ :=
  if 0 ≤ n then 2 * n + 2 * j - 1 else if -j ≤ n then 2 * j - 2 else -2 * n - 3

/-- **Lower bound on the rows `j <= 0`.** -/
theorem lower_bound_nonpos {M n h : ℤ} (hM : 0 ≤ M) (hh : 2 ≤ h) :
    h - 1 ≤ max (kNonpos M n) (kNonpos M (n + h)) := by
  unfold kNonpos
  rcases le_or_lt M n with hn | hn
  · -- n >= M, so both points are on the increasing branch
    have h1 : M ≤ n + h := by linarith
    rw [if_pos hn, if_pos h1]
    have : h - 1 ≤ 2 * (n + h) := by
      have : 0 ≤ n := le_trans hM hn
      linarith
    exact le_trans this (le_max_right _ _)
  · rcases le_or_lt 0 n with hn0 | hn0
    · -- 0 <= n < M
      rcases le_or_lt M (n + h) with hh1 | hh1
      · rw [if_pos hh1]
        have : h - 1 ≤ 2 * (n + h) := by linarith
        exact le_trans this (le_max_right _ _)
      · rw [if_neg (not_le.mpr hn), if_pos hn0, if_neg (not_le.mpr hh1),
            if_pos (by linarith : (0:ℤ) ≤ n + h)]
        have : h - 1 ≤ 2 * M - 1 := by linarith
        exact le_trans this (le_max_left _ _)
    · -- n < 0
      rw [if_neg (not_le.mpr hn), if_neg (not_le.mpr hn0)]
      rcases le_or_lt M (n + h) with hh1 | hh1
      · rw [if_pos hh1]
        -- the two values sum to 2M + 2h - 2
        have hsum : (-2 * n + 2 * M - 2) + 2 * (n + h) = 2 * M + 2 * h - 2 := by ring
        rcases le_or_lt (-2 * n + 2 * M - 2) (2 * (n + h)) with hc | hc
        · have : h - 1 ≤ 2 * (n + h) := by linarith
          exact le_trans this (le_max_right _ _)
        · have : h - 1 ≤ -2 * n + 2 * M - 2 := by linarith
          exact le_trans this (le_max_left _ _)
      · have : h - 1 ≤ -2 * n + 2 * M - 2 := by
          rcases le_or_lt 0 (n + h) with hp | hp
          · linarith
          · linarith
        exact le_trans this (le_max_left _ _)

/-- **Lower bound on the rows `j >= 1`.** -/
theorem lower_bound_pos {j n h : ℤ} (hj : 1 ≤ j) (hh : 2 ≤ h) :
    h - 1 ≤ max (kPos j n) (kPos j (n + h)) := by
  unfold kPos
  rcases le_or_lt 0 n with hn | hn
  · have h1 : (0:ℤ) ≤ n + h := by linarith
    rw [if_pos hn, if_pos h1]
    have : h - 1 ≤ 2 * (n + h) + 2 * j - 1 := by linarith
    exact le_trans this (le_max_right _ _)
  · rw [if_neg (not_le.mpr hn)]
    rcases le_or_lt (-j) n with hv | hv
    · -- n in the valley
      rw [if_pos hv]
      rcases le_or_lt 0 (n + h) with hp | hp
      · rw [if_pos hp]
        have : h - 1 ≤ 2 * (n + h) + 2 * j - 1 := by linarith
        exact le_trans this (le_max_right _ _)
      · rw [if_neg (not_le.mpr hp)]
        have hle : h - 1 ≤ 2 * j - 2 := by
          rcases le_or_lt (-j) (n + h) with hq | hq
          · linarith
          · linarith
        rcases le_or_lt (-j) (n + h) with hq | hq
        · rw [if_pos hq]; exact le_trans hle (le_max_left _ _)
        · rw [if_neg (not_le.mpr hq)]; exact le_trans hle (le_max_left _ _)
    · -- n < -j : left of the valley
      rw [if_neg (not_le.mpr hv)]
      have hnle : n ≤ -j - 1 := by linarith
      rcases le_or_lt 0 (n + h) with hp | hp
      · rw [if_pos hp]
        have hsum : (-2 * n - 3) + (2 * (n + h) + 2 * j - 1) = 2 * h + 2 * j - 4 := by ring
        rcases le_or_lt (-2 * n - 3) (2 * (n + h) + 2 * j - 1) with hc | hc
        · have : h - 1 ≤ 2 * (n + h) + 2 * j - 1 := by linarith
          exact le_trans this (le_max_right _ _)
        · have : h - 1 ≤ -2 * n - 3 := by linarith
          exact le_trans this (le_max_left _ _)
      · have hkey : h - 1 ≤ -2 * n - 3 := by linarith
        rcases le_or_lt (-j) (n + h) with hq | hq
        · rw [if_neg (not_le.mpr hp), if_pos hq]; exact le_trans hkey (le_max_left _ _)
        · rw [if_neg (not_le.mpr hp), if_neg (not_le.mpr hq)]
          exact le_trans hkey (le_max_left _ _)

/-- **The bound, both branches.**  With the closed form granted, no pair of sites at horizontal
    separation `h >= 2` has both values below `h-1`. -/
theorem antipair_lower_bound {j n h : ℤ} (hh : 2 ≤ h) :
    (j ≤ 0 → h - 1 ≤ max (kNonpos (-j) n) (kNonpos (-j) (n + h))) ∧
    (1 ≤ j → h - 1 ≤ max (kPos j n) (kPos j (n + h))) :=
  ⟨fun hj => lower_bound_nonpos (by linarith) hh, fun hj => lower_bound_pos hj hh⟩

/-! ### 5. The false premise, refuted

    The withdrawn proof asserted that on every row the function increases by 2 with each unit
    step away from its minimum, and that the valley has width at most two.  Row `j = 3` of the
    computed table, for `n = -4, ..., 4`, is `5, 4, 4, 4, 5, 7, 9, 11, 13`.  Its minimum 4 is
    attained three times, and the first step out of the valley is `+1`. -/

def row3 : List ℤ := [5, 4, 4, 4, 5, 7, 9, 11, 13]

/-- The valley has width three, not "at most two". -/
theorem row3_valley_width_three :
    (row3.count 4 = 3) ∧ (row3.count 4 ≠ 2) := by
  refine ⟨by decide, by decide⟩

/-- The first step out of the valley adds 1, not 2, so the premise "each step adds 2" fails
    already inside the range in which the paper's own computation was carried out. -/
theorem row3_step_is_one :
    row3 = [5, 4, 4, 4, 5, 7, 9, 11, 13] ∧ ((5 : ℤ) - 4 = 1) ∧ ((5 : ℤ) - 4 ≠ 2) := by
  refine ⟨rfl, by decide, by decide⟩

/-- Consequently the inequality the withdrawn proof drew, that the larger of the two values is
    at least `k_j + h - 1`, fails: on row 3 with `h = 2` and `n = -3` the two values are both
    `4`, so the maximum is `4`, while the claimed bound is `k_3 + h - 1 = 4 + 1 = 5`. -/
theorem row3_counterexample :
    max (4 : ℤ) 4 = 4 ∧ ¬ (4 + 2 - 1 ≤ max (4 : ℤ) 4) := by
  refine ⟨by decide, by decide⟩

end AntipairRows
