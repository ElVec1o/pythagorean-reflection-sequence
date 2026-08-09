/-
  HexDistance.lean
  ================
  Paper 4, Lemma `lem:krows`: the closed form for the lamp distance, PROVED.

  `X` is the honeycomb dual to the triangular lattice of sites.  A vertex of `X` is a triangle
  of mutually hex-adjacent sites; there are two families,

      up   (n,j,ff) = {(n,j), (n+1,j), (n,j+1)}
      down (n,j,tt) = {(n,j), (n+1,j), (n+1,j-1)}

  and `up (n,j)` is adjacent to `down (n,j)`, `down (n-1,j+1)` and `down (n,j+1)`.  The base
  vertex is `e = up(-1,0)`, the triangle of the three base sites.

  The closed form is proved by the standard local criterion for a distance function on a graph:
  if `dhat(e) = 0`, if `dhat` changes by at most one across every edge, and if every vertex
  other than `e` has a neighbour where `dhat` is one smaller, then `dhat` is the distance from
  `e`.  The first gives nothing, the second gives `d >= dhat` along any geodesic, and the third
  gives `d <= dhat` by induction.  Each of the three is a finite piece of linear arithmetic
  here, because `dhat` is a maximum of three affine functions.

      dhat0 (n,j) = max ( -2n-2+2j^-,  2|j|,  2n+2+2j^+ )
      dhat  (n,j,up) = dhat0 (n,j),
      dhat  (n,j,down) = dhat0 (n,j) - 1  if j >= 1,  dhat0 (n,j) + 1  if j <= 0.

  The lamp distance of the paper is `k(n,j) = min` of `dhat` over the six corners of the
  hexagon at `(n,j)`, and that minimum is computed at the end.

  Everything below is `omega` after unfolding the maxima: no geometry is formalised, only the
  arithmetic that the local criterion reduces the geometry to.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace HexDistance

/-- `le_or_lt` is absent under that name in this Mathlib; the integer case is all we need. -/
private theorem le_or_lt (a b : ℤ) : a ≤ b ∨ b < a := by omega

/-! ### 1. The claimed distance -/

/-- The claimed distance at an up-vertex.  As a maximum of three affine functions it reads
    `max(-2n-2+2j^-, 2|j|, 2n+2+2j^+)`; it is written piecewise here because that is the form
    `omega` can discharge, the two being equal region by region. -/
def dhat0 (n j : ℤ) : ℤ :=
  if 0 ≤ j then
    (if n ≤ -j - 2 then -2 * n - 2 else if n ≤ -1 then 2 * j else 2 * n + 2 * j + 2)
  else
    (if n ≤ -1 then -2 * n - 2 * j - 2 else if n ≤ -j - 1 then -2 * j else 2 * n + 2)

/-- The claimed distance at a vertex; `t = false` is an up-triangle, `t = true` a down one. -/
def dhat (n j : ℤ) (t : Bool) : ℤ :=
  if t then (if 1 ≤ j then dhat0 n j - 1 else dhat0 n j + 1) else dhat0 n j

/-- `dhat` at an up-vertex and at a down-vertex, with the Bool already reduced.  Without these
    `simp only [dhat]` leaves `if True` and `if false = true` in the goal, `split_ifs` then
    manufactures impossible branches, and `omega` cannot close them.  That was the obstruction. -/
@[simp] theorem dhat_false (n j : ℤ) : dhat n j false = dhat0 n j := rfl

@[simp] theorem dhat_true (n j : ℤ) :
    dhat n j true = if 1 ≤ j then dhat0 n j - 1 else dhat0 n j + 1 := rfl

/-! ### 1b. The affine pieces as an explicit case disjunction

    `omega` cannot see through `dhat0` at a shifted site, so the pieces must be handed to it
    with their region hypotheses attached. -/

theorem dhat0_cases_nonneg {n j : ℤ} (hj : 0 ≤ j) :
    (n ≤ -j - 2 ∧ dhat0 n j = -2 * n - 2) ∨
    (-j - 1 ≤ n ∧ n ≤ -1 ∧ dhat0 n j = 2 * j) ∨
    (0 ≤ n ∧ dhat0 n j = 2 * n + 2 * j + 2) := by
  rcases le_or_lt n (-j - 2) with h | h
  · exact Or.inl ⟨h, by simp only [dhat0]; rw [if_pos hj, if_pos h]⟩
  · rcases le_or_lt n (-1) with h2 | h2
    · exact Or.inr (Or.inl ⟨by omega, h2, by
        simp only [dhat0]; rw [if_pos hj, if_neg (by omega : ¬ n ≤ -j - 2), if_pos h2]⟩)
    · exact Or.inr (Or.inr ⟨by omega, by
        simp only [dhat0]
        rw [if_pos hj, if_neg (by omega : ¬ n ≤ -j - 2), if_neg (by omega : ¬ n ≤ -1)]⟩)

theorem dhat0_cases_neg {n j : ℤ} (hj : j ≤ -1) :
    (n ≤ -1 ∧ dhat0 n j = -2 * n - 2 * j - 2) ∨
    (0 ≤ n ∧ n ≤ -j - 1 ∧ dhat0 n j = -2 * j) ∨
    (-j ≤ n ∧ dhat0 n j = 2 * n + 2) := by
  have hjn : ¬ (0 ≤ j) := by omega
  rcases le_or_lt n (-1) with h | h
  · exact Or.inl ⟨h, by simp only [dhat0]; rw [if_neg hjn, if_pos h]⟩
  · rcases le_or_lt n (-j - 1) with h2 | h2
    · exact Or.inr (Or.inl ⟨by omega, h2, by
        simp only [dhat0]; rw [if_neg hjn, if_neg (by omega : ¬ n ≤ -1), if_pos h2]⟩)
    · exact Or.inr (Or.inr ⟨by omega, by
        simp only [dhat0]
        rw [if_neg hjn, if_neg (by omega : ¬ n ≤ -1), if_neg (by omega : ¬ n ≤ -j - 1)]⟩)

/-! ### 2. (a) the base vertex -/

theorem dhat_base : dhat (-1) 0 false = 0 := by
  unfold dhat dhat0; norm_num

/-! ### 3. (c) `dhat` is 1-Lipschitz across every edge

    The three edges out of an up-vertex.  Each is closed by `omega` once the maxima and the
    branch on the sign of `j` are unfolded. -/

theorem lip_same (n j : ℤ) :
    -1 ≤ dhat n j false - dhat n j true ∧ dhat n j false - dhat n j true ≤ 1 := by
  simp only [dhat, dhat0]; split_ifs <;> omega

/-- **Left-neighbour Lipschitz.** -/
theorem lip_left (n j : ℤ) :
    -1 ≤ dhat n j false - dhat (n - 1) (j + 1) true ∧
    dhat n j false - dhat (n - 1) (j + 1) true ≤ 1 := by
  simp only [dhat_false, dhat_true]
  rcases le_or_lt 0 j with hj | hj
  · rcases dhat0_cases_nonneg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩  <;>
  rcases dhat0_cases_nonneg (n := n - 1) (j := j + 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩  <;>
      rw [e1, e2] <;> split_ifs <;> omega
  · rcases le_or_lt 0 (j + 1) with hj1 | hj1
    · rcases dhat0_cases_neg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩  <;>
      rcases dhat0_cases_nonneg (n := n - 1) (j := j + 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩  <;>
        rw [e1, e2] <;> split_ifs <;> omega
    · rcases dhat0_cases_neg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩  <;>
      rcases dhat0_cases_neg (n := n - 1) (j := j + 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩  <;>
        rw [e1, e2] <;> split_ifs <;> omega

/-- **Upper-neighbour Lipschitz.** -/
theorem lip_up (n j : ℤ) :
    -1 ≤ dhat n j false - dhat n (j + 1) true ∧
    dhat n j false - dhat n (j + 1) true ≤ 1 := by
  simp only [dhat_false, dhat_true]
  rcases le_or_lt 0 j with hj | hj
  · rcases dhat0_cases_nonneg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩  <;>
  rcases dhat0_cases_nonneg (n := n) (j := j + 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩  <;>
      rw [e1, e2] <;> split_ifs <;> omega
  · rcases le_or_lt 0 (j + 1) with hj1 | hj1
    · rcases dhat0_cases_neg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩  <;>
      rcases dhat0_cases_nonneg (n := n) (j := j + 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩  <;>
        rw [e1, e2] <;> split_ifs <;> omega
    · rcases dhat0_cases_neg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩  <;>
      rcases dhat0_cases_neg (n := n) (j := j + 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩  <;>
        rw [e1, e2] <;> split_ifs <;> omega

/-! ### 4. (b) every vertex other than the base has a descending neighbour

    For a down-vertex the three neighbours are the up-vertices `(n,j)`, `(n+1,j-1)`, `(n,j-1)`;
    for an up-vertex they are the down-vertices `(n,j)`, `(n-1,j+1)`, `(n,j+1)`. -/

/-- **Descent from a down-vertex.**  For `j <= 0` the same-site up-vertex already descends;
    only `j >= 1` needs the shifted sites, and there all three indices are nonnegative. -/
theorem descent_down (n j : ℤ) :
    dhat n j false = dhat n j true - 1 ∨
    dhat (n + 1) (j - 1) false = dhat n j true - 1 ∨
    dhat n (j - 1) false = dhat n j true - 1 := by
  simp only [dhat_false, dhat_true]
  rcases le_or_lt 1 j with hj | hj
  · right
    rcases dhat0_cases_nonneg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩ <;>
    rcases dhat0_cases_nonneg (n := n + 1) (j := j - 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩ <;>
    rcases dhat0_cases_nonneg (n := n) (j := j - 1) (by omega) with ⟨q3a,e3⟩|⟨q3a,q3b,e3⟩|⟨q3a,e3⟩ <;>
      rw [e1, e2, e3] <;> split_ifs <;> omega
  · left
    rw [if_neg (by omega : ¬ (1:ℤ) ≤ j)]
    omega

/-- **Descent from an up-vertex other than the base.**  For `j >= 1` the same-site down-vertex
    already descends; only `j <= 0` needs the shifted sites, and the base `(-1,0)` is the single
    exception there. -/
theorem descent_up {n j : ℤ} (hne : ¬ (n = -1 ∧ j = 0)) :
    dhat n j true = dhat n j false - 1 ∨
    dhat (n - 1) (j + 1) true = dhat n j false - 1 ∨
    dhat n (j + 1) true = dhat n j false - 1 := by
  simp only [dhat_false, dhat_true]
  rcases le_or_lt 1 j with hj | hj
  · left; rw [if_pos hj]
  · right
    have hn1 : j = 0 → n ≠ -1 := fun h hn => hne ⟨hn, h⟩
    rcases le_or_lt 0 j with hj0 | hj0
    · -- j = 0
      rcases dhat0_cases_nonneg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩ <;>
      rcases dhat0_cases_nonneg (n := n - 1) (j := j + 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩ <;>
      rcases dhat0_cases_nonneg (n := n) (j := j + 1) (by omega) with ⟨q3a,e3⟩|⟨q3a,q3b,e3⟩|⟨q3a,e3⟩ <;>
        rw [e1, e2, e3] <;> split_ifs <;> omega
    · rcases le_or_lt 0 (j + 1) with hj1 | hj1
      · -- j = -1
        rcases dhat0_cases_neg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩ <;>
        rcases dhat0_cases_nonneg (n := n - 1) (j := j + 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩ <;>
        rcases dhat0_cases_nonneg (n := n) (j := j + 1) (by omega) with ⟨q3a,e3⟩|⟨q3a,q3b,e3⟩|⟨q3a,e3⟩ <;>
          rw [e1, e2, e3] <;> split_ifs <;> omega
      · -- j <= -2
        rcases dhat0_cases_neg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩ <;>
        rcases dhat0_cases_neg (n := n - 1) (j := j + 1) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩ <;>
        rcases dhat0_cases_neg (n := n) (j := j + 1) (by omega) with ⟨q3a,e3⟩|⟨q3a,q3b,e3⟩|⟨q3a,e3⟩ <;>
          rw [e1, e2, e3] <;> split_ifs <;> omega

/-! ### 5. The lamp distance

    `k(n,j)` is the minimum of `dhat` over the six corners of the hexagon at `(n,j)`, namely
    the up-vertices `(n,j)`, `(n-1,j)`, `(n,j-1)` and the down-vertices `(n,j)`, `(n-1,j)`,
    `(n-1,j+1)`. -/

def kmin (n j : ℤ) : ℤ :=
  min (min (min (dhat n j false) (dhat (n - 1) j false)) (min (dhat n (j - 1) false) (dhat n j true)))
      (min (dhat (n - 1) j true) (dhat (n - 1) (j + 1) true))

/-- The closed form of `lem:krows`, in the two branches the paper displays. -/
def kClosed (n j : ℤ) : ℤ :=
  if 1 ≤ j then
    (if 0 ≤ n then 2 * n + 2 * j - 1 else if -j ≤ n then 2 * j - 2 else -2 * n - 3)
  else
    (if -j ≤ n then 2 * n else if 0 ≤ n then -2 * j - 1 else -2 * n - 2 * j - 2)

set_option maxHeartbeats 1000000 in
/-- **Lemma `lem:krows`.**  The minimum over the six corners is the displayed closed form. -/
theorem kmin_eq_kClosed (n j : ℤ) : kmin n j = kClosed n j := by
  simp only [kmin, kClosed, dhat_false, dhat_true]
  rcases le_or_lt 1 j with hj | hj
  · -- j >= 1
    rcases dhat0_cases_nonneg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩ <;>
    rcases dhat0_cases_nonneg (n := n - 1) (j := j) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩ <;>
    rcases dhat0_cases_nonneg (n := n) (j := j - 1) (by omega) with ⟨q3a,e3⟩|⟨q3a,q3b,e3⟩|⟨q3a,e3⟩ <;>
    rcases dhat0_cases_nonneg (n := n - 1) (j := j + 1) (by omega) with ⟨q4a,e4⟩|⟨q4a,q4b,e4⟩|⟨q4a,e4⟩ <;>
      rw [e1, e2, e3, e4] <;> split_ifs <;> omega
  · rcases le_or_lt 0 j with hj0 | hj0
    · -- j = 0
      rcases dhat0_cases_nonneg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩ <;>
      rcases dhat0_cases_nonneg (n := n - 1) (j := j) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩ <;>
      rcases dhat0_cases_neg (n := n) (j := j - 1) (by omega) with ⟨q3a,e3⟩|⟨q3a,q3b,e3⟩|⟨q3a,e3⟩ <;>
      rcases dhat0_cases_nonneg (n := n - 1) (j := j + 1) (by omega) with ⟨q4a,e4⟩|⟨q4a,q4b,e4⟩|⟨q4a,e4⟩ <;>
        rw [e1, e2, e3, e4] <;> split_ifs <;> omega
    · rcases le_or_lt 0 (j + 1) with hj1 | hj1
      · -- j = -1
        rcases dhat0_cases_neg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩ <;>
        rcases dhat0_cases_neg (n := n - 1) (j := j) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩ <;>
        rcases dhat0_cases_neg (n := n) (j := j - 1) (by omega) with ⟨q3a,e3⟩|⟨q3a,q3b,e3⟩|⟨q3a,e3⟩ <;>
        rcases dhat0_cases_nonneg (n := n - 1) (j := j + 1) (by omega) with ⟨q4a,e4⟩|⟨q4a,q4b,e4⟩|⟨q4a,e4⟩ <;>
          rw [e1, e2, e3, e4] <;> split_ifs <;> omega
      · -- j <= -2
        rcases dhat0_cases_neg (n := n) (j := j) (by omega) with ⟨q1a,e1⟩|⟨q1a,q1b,e1⟩|⟨q1a,e1⟩ <;>
        rcases dhat0_cases_neg (n := n - 1) (j := j) (by omega) with ⟨q2a,e2⟩|⟨q2a,q2b,e2⟩|⟨q2a,e2⟩ <;>
        rcases dhat0_cases_neg (n := n) (j := j - 1) (by omega) with ⟨q3a,e3⟩|⟨q3a,q3b,e3⟩|⟨q3a,e3⟩ <;>
        rcases dhat0_cases_neg (n := n - 1) (j := j + 1) (by omega) with ⟨q4a,e4⟩|⟨q4a,q4b,e4⟩|⟨q4a,e4⟩ <;>
          rw [e1, e2, e3, e4] <;> split_ifs <;> omega

/-! ### 6. Status

    All of the local criterion is proved here: the base value, the three Lipschitz bounds, and
    the two descent statements.  Together they give `dhat = d_X(e, .)`, and `kmin_eq_kClosed`
    evaluates the minimum over the six corners of a hexagon, which is the paper's lemma.

    The obstruction that blocked this for several attempts was not the case analysis but the
    Bool: `simp only [dhat]` leaves `if True` and `if false = true` in the goal, `split_ifs`
    then manufactures branches with hypotheses `omega` cannot refute, and on the larger goals
    the branch count exploded.  Reducing the Bool first, via `dhat_false` and `dhat_true`, and
    handing `omega` the affine pieces with their region hypotheses via `dhat0_cases_*`, makes
    every one of them close in seconds. -/

/-- **Lemma `lem:krows`.** -/
theorem lem_krows : ∀ n j : ℤ, kmin n j = kClosed n j := kmin_eq_kClosed

#print axioms dhat_base
#print axioms lip_same
#print axioms lip_left
#print axioms lip_up
#print axioms descent_down
#print axioms descent_up
#print axioms lem_krows

end HexDistance
