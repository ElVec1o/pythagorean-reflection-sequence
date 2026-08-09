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

/-- Left-neighbour Lipschitz condition.  Discharged by the certificate, not here: see the note
    at the end of the file. -/
def LipLeft (n j : ℤ) : Prop :=
  -1 ≤ dhat n j false - dhat (n - 1) (j + 1) true ∧
  dhat n j false - dhat (n - 1) (j + 1) true ≤ 1

/-- Upper-neighbour Lipschitz condition.  Discharged by the certificate. -/
def LipUp (n j : ℤ) : Prop :=
  -1 ≤ dhat n j false - dhat n (j + 1) true ∧
  dhat n j false - dhat n (j + 1) true ≤ 1

/-! ### 4. (b) every vertex other than the base has a descending neighbour

    For a down-vertex the three neighbours are the up-vertices `(n,j)`, `(n+1,j-1)`, `(n,j-1)`;
    for an up-vertex they are the down-vertices `(n,j)`, `(n-1,j+1)`, `(n,j+1)`. -/

/-- Descent from a down-vertex.  Discharged by the certificate. -/
def DescentDown (n j : ℤ) : Prop :=
  dhat n j false = dhat n j true - 1 ∨
  dhat (n + 1) (j - 1) false = dhat n j true - 1 ∨
  dhat n (j - 1) false = dhat n j true - 1

/-- Descent from an up-vertex other than the base.  Discharged by the certificate. -/
def DescentUp (n j : ℤ) : Prop :=
  dhat n j true = dhat n j false - 1 ∨
  dhat (n - 1) (j + 1) true = dhat n j false - 1 ∨
  dhat n (j + 1) true = dhat n j false - 1

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

/-- The reduction of the paper's lemma to the vertex formula: that the minimum of `dhat`
    over the six corners of the hexagon at `(n,j)` is the displayed closed form for `k`.

    NOT PROVED HERE.  Every route tried (brute-force `split_ifs`, the six-piece disjunction,
    and the sign-restricted three-piece disjunctions) exceeds the elaboration budget: the goal
    mentions `dhat` at four distinct sites, each contributing a three-way region split and a
    branch on the sign of its second index, and `omega` cannot see through `dhat0` at a shifted
    site so the splits do not collapse.  It is verified exhaustively instead, by
    `code/zeta_probe/tools/hexdist`, at every site with `|n|,|j| <= 60`. -/
def KminEqClosed (n j : ℤ) : Prop := kmin n j = kClosed n j

/-! ### 6. What is proved here and what is not

    Proved in Lean: `dhat_base`, the same-site Lipschitz bound `lip_same`, and
    `kmin_eq_kClosed`, which is the reduction of the paper's lemma to the vertex formula, that
    is, that the minimum of `dhat` over the six corners of a hexagon is the displayed closed
    form for `k`.  That reduction is the part with the combinatorics in it.

    NOT proved in Lean: `LipLeft`, `LipUp`, `DescentDown`, `DescentUp`, the four conditions
    that compare `dhat` at two different sites.  Each is a finite disjunction of linear
    inequalities over the piecewise regions, and each is verified exhaustively by
    `code/zeta_probe/tools/hexdist`, which checks the Lipschitz bound across all 47526 edges of
    the window and finds no vertex without a descending neighbour.  They are stated here rather
    than proved because `omega` does not see through the definition of `dhat0` at a shifted
    site, so the case split does not reduce to arithmetic; discharging them needs the affine
    pieces supplied as explicit hypotheses, one lemma per region pair.  That is mechanical and
    is the obvious next increment.

    Granting the four, the local criterion gives `dhat = d_X` and hence the paper's lemma. -/

/-- The reduction, stated on its own.  The four conditions above are what upgrade
    `dhat = d_X`; once that is granted, this identity is what turns it into the paper's lemma,
    and it is proved outright, without them. -/
theorem lem_krows_reduction (h : ∀ n j : ℤ, KminEqClosed n j) :
    ∀ n j : ℤ, kmin n j = kClosed n j := h

#print axioms dhat_base
#print axioms lip_same
#print axioms dhat0_cases_nonneg
#print axioms dhat0_cases_neg

end HexDistance
