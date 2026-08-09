/-
  HexGraph.lean
  =============
  Paper 4, Lemma `lem:krows`: the geometry that `HexDistance.lean` left outside Lean.

  `HexDistance.lean` proves the arithmetic that the local criterion reduces the geometry to --
  the base value, three Lipschitz bounds, two descent statements and the evaluation of the
  corner minimum -- but it constructs no graph, so its `lem_krows` is a statement about a
  minimum of the function `dhat`, not about a graph distance.  This file closes that gap.

    1. `X` is the honeycomb, a `SimpleGraph` on `Z x Z x Bool`.  A vertex is a triangle of
       mutually hex-adjacent sites,

           up   (n,j) = {(n,j), (n+1,j), (n,j+1)}       (Bool `false`)
           down (n,j) = {(n,j), (n+1,j), (n+1,j-1)}     (Bool `true`)

       and two triangles are adjacent when they share two sites.  That the hand-written
       adjacency `adjUD` is exactly the share-two-sites relation is proved, not assumed:
       `adj_iff_sharesEdge`.

    2. The local criterion `[base + 1-Lipschitz + descent] implies f = d_G(e, .)` is proved for
       an arbitrary graph in `GraphLocalDistance.lean`.

    3. `dist_up`, `dist_down`: the graph distance in `X` from `e = up(-1,0)` is `dhat`.  This is
       the implication that the paper's proof asserts and that was outside Lean.

    4. `lem_krows_face`: the distance from `e` to the vertex set of the face of the site `(n,j)`
       -- the paper's `k(n,j) = d_X(e, f_{n,j})` -- is the closed form of `lem:krows`.  That the
       face of `(n,j)` consists of exactly the six triangles having `(n,j)` as a corner is
       proved, not assumed: `memTri_iff`, `kdist_eq_sInf`.

  With `HexDistance.lean` this makes `lem:krows` a statement about `SimpleGraph.dist` that is
  machine-checked end to end.
-/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith
import HexDistance
import GraphLocalDistance

namespace HexGraph

open SimpleGraph

/-! ### 1. The honeycomb `X` -/

/-- A vertex of `X`: `(n, j, false)` is the up-triangle at `(n,j)`, `(n, j, true)` the down
    one. -/
abbrev Vert := ℤ × ℤ × Bool

/-- `up (n,j) = {(n,j), (n+1,j), (n,j+1)}`. -/
def up (n j : ℤ) : Vert := (n, j, false)

/-- `down (n,j) = {(n,j), (n+1,j), (n+1,j-1)}`. -/
def down (n j : ℤ) : Vert := (n, j, true)

/-- The base vertex `e`, the triangle `{(0,0), (-1,0), (-1,1)}` of the three base sites. -/
def base : Vert := up (-1) 0

/-- `up (n,j)` is adjacent to `down (m,k)` for exactly these three `(m,k)`. -/
def adjUD (n j m k : ℤ) : Prop :=
  (m = n ∧ k = j) ∨ (m = n - 1 ∧ k = j + 1) ∨ (m = n ∧ k = j + 1)

/-- The adjacency relation of `X`.  Up-triangles meet only down-triangles and conversely. -/
def XAdj : Vert → Vert → Prop
  | (n, j, false), (m, k, true) => adjUD n j m k
  | (n, j, true), (m, k, false) => adjUD m k n j
  | _, _ => False

/-- **The honeycomb.** -/
def X : SimpleGraph Vert where
  Adj := XAdj
  symm := by
    rintro ⟨n, j, t⟩ ⟨m, k, u⟩
    cases t <;> cases u <;> exact id
  loopless := ⟨by
    rintro ⟨n, j, t⟩ h
    cases t <;> exact h⟩

/-! #### The four adjacency equations -/

theorem adj_ud (n j m k : ℤ) : X.Adj (up n j) (down m k) ↔ adjUD n j m k := Iff.rfl

theorem adj_du (n j m k : ℤ) : X.Adj (down n j) (up m k) ↔ adjUD m k n j := Iff.rfl

theorem not_adj_uu (n j m k : ℤ) : ¬ X.Adj (up n j) (up m k) := id

theorem not_adj_dd (n j m k : ℤ) : ¬ X.Adj (down n j) (down m k) := id

/-- **The three edges out of an up-vertex.** -/
theorem adj_up_same (n j : ℤ) : X.Adj (up n j) (down n j) := Or.inl ⟨rfl, rfl⟩

theorem adj_up_left (n j : ℤ) : X.Adj (up n j) (down (n - 1) (j + 1)) :=
  Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem adj_up_upper (n j : ℤ) : X.Adj (up n j) (down n (j + 1)) :=
  Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- **The three edges out of a down-vertex**, the same edges read backwards. -/
theorem adj_down_same (n j : ℤ) : X.Adj (down n j) (up n j) := Or.inl ⟨rfl, rfl⟩

theorem adj_down_right (n j : ℤ) : X.Adj (down n j) (up (n + 1) (j - 1)) :=
  Or.inr (Or.inl ⟨by ring, by ring⟩)

theorem adj_down_lower (n j : ℤ) : X.Adj (down n j) (up n (j - 1)) :=
  Or.inr (Or.inr ⟨rfl, by ring⟩)

/-- **Every edge is one of the six.** -/
theorem adj_cases {v w : Vert} (h : X.Adj v w) :
    (∃ n j : ℤ, v = up n j ∧
      (w = down n j ∨ w = down (n - 1) (j + 1) ∨ w = down n (j + 1))) ∨
    (∃ n j : ℤ, w = up n j ∧
      (v = down n j ∨ v = down (n - 1) (j + 1) ∨ v = down n (j + 1))) := by
  obtain ⟨n, j, t⟩ := v
  obtain ⟨m, k, u⟩ := w
  cases t <;> cases u
  · exact absurd h (not_adj_uu n j m k)
  · refine Or.inl ⟨n, j, rfl, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by subst h1; subst h2; rfl)
    · exact Or.inr (Or.inl (by subst h1; subst h2; rfl))
    · exact Or.inr (Or.inr (by subst h1; subst h2; rfl))
  · refine Or.inr ⟨m, k, rfl, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by subst h1; subst h2; rfl)
    · exact Or.inr (Or.inl (by subst h1; subst h2; rfl))
    · exact Or.inr (Or.inr (by subst h1; subst h2; rfl))
  · exact absurd h (not_adj_dd n j m k)

/-! ### 2. The triangles

    A vertex of `X` is a set of three sites.  `memTri v p q` says that the site `(p,q)` is one
    of them.  The definition is written through `cond` so that both cases reduce by `rfl`. -/

/-- The three sites of `up (n,j)`. -/
def memTriU (n j p q : ℤ) : Prop :=
  (p = n ∧ q = j) ∨ (p = n + 1 ∧ q = j) ∨ (p = n ∧ q = j + 1)

/-- The three sites of `down (n,j)`. -/
def memTriD (n j p q : ℤ) : Prop :=
  (p = n ∧ q = j) ∨ (p = n + 1 ∧ q = j) ∨ (p = n + 1 ∧ q = j - 1)

/-- `memTri v p q`: the site `(p,q)` is a corner of the triangle `v`. -/
def memTri (v : Vert) (p q : ℤ) : Prop :=
  cond v.2.2 (memTriD v.1 v.2.1 p q) (memTriU v.1 v.2.1 p q)

theorem memTri_up (n j p q : ℤ) : memTri (up n j) p q ↔ memTriU n j p q := Iff.rfl

theorem memTri_down (n j p q : ℤ) : memTri (down n j) p q ↔ memTriD n j p q := Iff.rfl

/-- **The face of a site has exactly six vertices.**  The paper lists the six corners of the
    hexagon at `(n,j)`; here they are computed from the definition of a triangle. -/
theorem memTri_iff (v : Vert) (n j : ℤ) :
    memTri v n j ↔
      (v = up n j ∨ v = up (n - 1) j ∨ v = up n (j - 1) ∨
       v = down n j ∨ v = down (n - 1) j ∨ v = down (n - 1) (j + 1)) := by
  obtain ⟨m, k, t⟩ := v
  cases t <;>
    simp only [memTri, memTriU, memTriD, up, down, cond_false, cond_true, Prod.mk.injEq,
      reduceCtorEq, and_false, and_true, or_false, false_or] <;>
    omega

/-! ### 3. The honeycomb is the share-an-edge graph on triangles

    The adjacency of section 1 was written down by hand.  Here it is shown to be forced: two
    distinct triangles are adjacent exactly when they have two sites in common, that is, when
    they share an edge of the triangular lattice. -/

/-- Two triangles share an edge when they have two distinct sites in common. -/
def sharesEdge (v w : Vert) : Prop :=
  ∃ p q p' q' : ℤ, (p ≠ p' ∨ q ≠ q') ∧
    memTri v p q ∧ memTri v p' q' ∧ memTri w p q ∧ memTri w p' q'

theorem sharesEdge_symm {v w : Vert} (h : sharesEdge v w) : sharesEdge w v := by
  obtain ⟨p, q, p', q', hne, h1, h2, h3, h4⟩ := h
  exact ⟨p, q, p', q', hne, h3, h4, h1, h2⟩

theorem up_ne_down (n j m k : ℤ) : up n j ≠ down m k := by
  simp [up, down]

/-- `up (n,j)` and `down (n,j)` share the sites `(n,j)` and `(n+1,j)`. -/
theorem sharesEdge_same (n j : ℤ) : sharesEdge (up n j) (down n j) := by
  refine ⟨n, j, n + 1, j, Or.inl (by omega), ?_, ?_, ?_, ?_⟩
  · rw [memTri_up]; exact Or.inl ⟨rfl, rfl⟩
  · rw [memTri_up]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [memTri_down]; exact Or.inl ⟨rfl, rfl⟩
  · rw [memTri_down]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- `up (n,j)` and `down (n-1,j+1)` share the sites `(n,j)` and `(n,j+1)`. -/
theorem sharesEdge_left (n j : ℤ) : sharesEdge (up n j) (down (n - 1) (j + 1)) := by
  refine ⟨n, j, n, j + 1, Or.inr (by omega), ?_, ?_, ?_, ?_⟩
  · rw [memTri_up]; exact Or.inl ⟨rfl, rfl⟩
  · rw [memTri_up]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [memTri_down]; exact Or.inr (Or.inr ⟨by ring, by ring⟩)
  · rw [memTri_down]; exact Or.inr (Or.inl ⟨by ring, rfl⟩)

/-- `up (n,j)` and `down (n,j+1)` share the sites `(n,j+1)` and `(n+1,j)`. -/
theorem sharesEdge_upper (n j : ℤ) : sharesEdge (up n j) (down n (j + 1)) := by
  refine ⟨n, j + 1, n + 1, j, Or.inl (by omega), ?_, ?_, ?_, ?_⟩
  · rw [memTri_up]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [memTri_up]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [memTri_down]; exact Or.inl ⟨rfl, rfl⟩
  · rw [memTri_down]; exact Or.inr (Or.inr ⟨rfl, by ring⟩)

set_option maxHeartbeats 2000000 in
/-- **The honeycomb, intrinsically.**  Two triangles are adjacent in `X` exactly when they are
    distinct and share an edge of the site lattice.  This is what makes `X` the dual of the
    triangular lattice rather than a hand-written adjacency table. -/
theorem adj_iff_sharesEdge (v w : Vert) : X.Adj v w ↔ (v ≠ w ∧ sharesEdge v w) := by
  constructor
  · intro h
    rcases adj_cases h with ⟨n, j, rfl, hw⟩ | ⟨n, j, rfl, hv⟩
    · rcases hw with rfl | rfl | rfl
      · exact ⟨up_ne_down _ _ _ _, sharesEdge_same n j⟩
      · exact ⟨up_ne_down _ _ _ _, sharesEdge_left n j⟩
      · exact ⟨up_ne_down _ _ _ _, sharesEdge_upper n j⟩
    · rcases hv with rfl | rfl | rfl
      · exact ⟨(up_ne_down _ _ _ _).symm, sharesEdge_symm (sharesEdge_same n j)⟩
      · exact ⟨(up_ne_down _ _ _ _).symm, sharesEdge_symm (sharesEdge_left n j)⟩
      · exact ⟨(up_ne_down _ _ _ _).symm, sharesEdge_symm (sharesEdge_upper n j)⟩
  · rintro ⟨hne, p, q, p', q', hpq, h1, h2, h3, h4⟩
    obtain ⟨n, j, t⟩ := v
    obtain ⟨m, k, u⟩ := w
    cases t <;> cases u
    · -- two up-triangles: they never share two sites unless they coincide
      replace h1 : memTriU n j p q := h1
      replace h2 : memTriU n j p' q' := h2
      replace h3 : memTriU m k p q := h3
      replace h4 : memTriU m k p' q' := h4
      refine absurd ?_ hne
      have hgoal : n = m ∧ j = k := by
        rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
        rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
        rcases h3 with ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ <;>
        rcases h4 with ⟨a4, b4⟩ | ⟨a4, b4⟩ | ⟨a4, b4⟩ <;>
        omega
      rw [hgoal.1, hgoal.2]
    · replace h1 : memTriU n j p q := h1
      replace h2 : memTriU n j p' q' := h2
      replace h3 : memTriD m k p q := h3
      replace h4 : memTriD m k p' q' := h4
      show (m = n ∧ k = j) ∨ (m = n - 1 ∧ k = j + 1) ∨ (m = n ∧ k = j + 1)
      rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
      rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
      rcases h3 with ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ <;>
      rcases h4 with ⟨a4, b4⟩ | ⟨a4, b4⟩ | ⟨a4, b4⟩ <;>
      omega
    · replace h1 : memTriD n j p q := h1
      replace h2 : memTriD n j p' q' := h2
      replace h3 : memTriU m k p q := h3
      replace h4 : memTriU m k p' q' := h4
      show (n = m ∧ j = k) ∨ (n = m - 1 ∧ j = k + 1) ∨ (n = m ∧ j = k + 1)
      rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
      rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
      rcases h3 with ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ <;>
      rcases h4 with ⟨a4, b4⟩ | ⟨a4, b4⟩ | ⟨a4, b4⟩ <;>
      omega
    · -- two down-triangles
      replace h1 : memTriD n j p q := h1
      replace h2 : memTriD n j p' q' := h2
      replace h3 : memTriD m k p q := h3
      replace h4 : memTriD m k p' q' := h4
      refine absurd ?_ hne
      have hgoal : n = m ∧ j = k := by
        rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
        rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
        rcases h3 with ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ <;>
        rcases h4 with ⟨a4, b4⟩ | ⟨a4, b4⟩ | ⟨a4, b4⟩ <;>
        omega
      rw [hgoal.1, hgoal.2]

/-! ### 4. The claimed distance as a natural number -/

theorem dhat0_nonneg (n j : ℤ) : 0 ≤ HexDistance.dhat0 n j := by
  by_cases hj : 0 ≤ j
  · rcases HexDistance.dhat0_cases_nonneg (n := n) (j := j) hj with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;> omega
  · rcases HexDistance.dhat0_cases_neg (n := n) (j := j) (by omega) with
      ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;> omega

theorem dhat0_two_le {n j : ℤ} (hj : 1 ≤ j) : 2 ≤ HexDistance.dhat0 n j := by
  rcases HexDistance.dhat0_cases_nonneg (n := n) (j := j) (by omega) with
    ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;> omega

theorem dhat_nonneg (n j : ℤ) (t : Bool) : 0 ≤ HexDistance.dhat n j t := by
  cases t
  · rw [HexDistance.dhat_false]; exact dhat0_nonneg n j
  · rw [HexDistance.dhat_true]
    split_ifs with h
    · have := dhat0_two_le (n := n) h; omega
    · have := dhat0_nonneg n j; omega

/-- The claimed distance, as a function to `Nat`, which is what `SimpleGraph.dist` returns. -/
def fhat (v : Vert) : ℕ := (HexDistance.dhat v.1 v.2.1 v.2.2).toNat

theorem fhat_up (n j : ℤ) : (fhat (up n j) : ℤ) = HexDistance.dhat n j false :=
  Int.toNat_of_nonneg (dhat_nonneg n j false)

theorem fhat_down (n j : ℤ) : (fhat (down n j) : ℤ) = HexDistance.dhat n j true :=
  Int.toNat_of_nonneg (dhat_nonneg n j true)

/-! ### 5. The three hypotheses of the local criterion -/

/-- (a) the base value. -/
theorem fhat_base : fhat base = 0 := by
  have h : (fhat (up (-1) 0) : ℤ) = 0 := by rw [fhat_up, HexDistance.dhat_base]
  have h2 : fhat base = fhat (up (-1) 0) := rfl
  omega

/-- (b) `fhat` is 1-Lipschitz across every edge of `X`. -/
theorem fhat_lip : ∀ a b : Vert, X.Adj a b → fhat b ≤ fhat a + 1 := by
  intro a b hab
  rcases adj_cases hab with ⟨n, j, rfl, hb⟩ | ⟨n, j, rfl, ha⟩
  · rcases hb with rfl | rfl | rfl
    · have h1 := fhat_up n j
      have h2 := fhat_down n j
      obtain ⟨hl, hr⟩ := HexDistance.lip_same n j
      omega
    · have h1 := fhat_up n j
      have h2 := fhat_down (n - 1) (j + 1)
      obtain ⟨hl, hr⟩ := HexDistance.lip_left n j
      omega
    · have h1 := fhat_up n j
      have h2 := fhat_down n (j + 1)
      obtain ⟨hl, hr⟩ := HexDistance.lip_up n j
      omega
  · rcases ha with rfl | rfl | rfl
    · have h1 := fhat_up n j
      have h2 := fhat_down n j
      obtain ⟨hl, hr⟩ := HexDistance.lip_same n j
      omega
    · have h1 := fhat_up n j
      have h2 := fhat_down (n - 1) (j + 1)
      obtain ⟨hl, hr⟩ := HexDistance.lip_left n j
      omega
    · have h1 := fhat_up n j
      have h2 := fhat_down n (j + 1)
      obtain ⟨hl, hr⟩ := HexDistance.lip_up n j
      omega

/-- (c) every vertex other than the base has a neighbour where `fhat` is one smaller. -/
theorem fhat_descent : ∀ v : Vert, v ≠ base → ∃ w, X.Adj v w ∧ fhat w + 1 = fhat v := by
  rintro ⟨n, j, t⟩ hv
  cases t
  · show ∃ w, X.Adj (up n j) w ∧ fhat w + 1 = fhat (up n j)
    have hne : ¬ (n = -1 ∧ j = 0) := by
      rintro ⟨rfl, rfl⟩; exact hv rfl
    rcases HexDistance.descent_up hne with h | h | h
    · refine ⟨down n j, adj_up_same n j, ?_⟩
      have h1 := fhat_up n j
      have h2 := fhat_down n j
      omega
    · refine ⟨down (n - 1) (j + 1), adj_up_left n j, ?_⟩
      have h1 := fhat_up n j
      have h2 := fhat_down (n - 1) (j + 1)
      omega
    · refine ⟨down n (j + 1), adj_up_upper n j, ?_⟩
      have h1 := fhat_up n j
      have h2 := fhat_down n (j + 1)
      omega
  · show ∃ w, X.Adj (down n j) w ∧ fhat w + 1 = fhat (down n j)
    rcases HexDistance.descent_down n j with h | h | h
    · refine ⟨up n j, adj_down_same n j, ?_⟩
      have h1 := fhat_up n j
      have h2 := fhat_down n j
      omega
    · refine ⟨up (n + 1) (j - 1), adj_down_right n j, ?_⟩
      have h1 := fhat_up (n + 1) (j - 1)
      have h2 := fhat_down n j
      omega
    · refine ⟨up n (j - 1), adj_down_lower n j, ?_⟩
      have h1 := fhat_up n (j - 1)
      have h2 := fhat_down n j
      omega

/-! ### 6. The vertex distance -/

/-- **The claimed distance is the distance.**  This is the implication
    `[base + 1-Lipschitz + descent] implies dhat = d_X` that `HexDistance.lean` left outside
    Lean. -/
theorem dist_eq_fhat (v : Vert) : X.dist base v = fhat v :=
  GraphLocalDistance.dist_eq_of_base_lip_descent fhat_base fhat_lip fhat_descent v

theorem dist_up (n j : ℤ) : (X.dist base (up n j) : ℤ) = HexDistance.dhat n j false := by
  rw [dist_eq_fhat]; exact fhat_up n j

theorem dist_down (n j : ℤ) : (X.dist base (down n j) : ℤ) = HexDistance.dhat n j true := by
  rw [dist_eq_fhat]; exact fhat_down n j

theorem X_preconnected : X.Preconnected := fun u v =>
  (GraphLocalDistance.reachable_of_descent fhat_base fhat_descent u).symm.trans
    (GraphLocalDistance.reachable_of_descent fhat_base fhat_descent v)

/-- `X` is connected; a by-product of the descent hypothesis. -/
theorem X_connected : X.Connected := ⟨X_preconnected⟩

/-! ### 7. The face of a site, and the lamp distance `k` -/

/-- The face of the site `(n,j)`: the set of triangles having `(n,j)` as a corner. -/
def face (n j : ℤ) : Set Vert := {v | memTri v n j}

/-- The paper's `k(n,j)`, written as the minimum over the six corners in the order used by
    `HexDistance.kmin`. -/
noncomputable def kdist (n j : ℤ) : ℕ :=
  min (min (min (X.dist base (up n j)) (X.dist base (up (n - 1) j)))
           (min (X.dist base (up n (j - 1))) (X.dist base (down n j))))
      (min (X.dist base (down (n - 1) j)) (X.dist base (down (n - 1) (j + 1))))

/-- **`kdist` is the distance to the face**, that is, the infimum of `d_X(e, v)` over the
    vertices `v` of the face of `(n,j)`, and not merely the minimum over a hand-picked list. -/
theorem kdist_eq_sInf (n j : ℤ) :
    sInf {d : ℕ | ∃ v ∈ face n j, X.dist base v = d} = kdist n j := by
  set S : Set ℕ := {d : ℕ | ∃ v ∈ face n j, X.dist base v = d} with hS
  have hmem : ∀ v : Vert, memTri v n j → X.dist base v ∈ S := fun v hv => ⟨v, hv, rfl⟩
  have hne : S.Nonempty := ⟨_, hmem (up n j) ((memTri_iff _ n j).2 (by tauto))⟩
  apply le_antisymm
  · have e1 := Nat.sInf_le (hmem (up n j) ((memTri_iff _ n j).2 (by tauto)))
    have e2 := Nat.sInf_le (hmem (up (n - 1) j) ((memTri_iff _ n j).2 (by tauto)))
    have e3 := Nat.sInf_le (hmem (up n (j - 1)) ((memTri_iff _ n j).2 (by tauto)))
    have e4 := Nat.sInf_le (hmem (down n j) ((memTri_iff _ n j).2 (by tauto)))
    have e5 := Nat.sInf_le (hmem (down (n - 1) j) ((memTri_iff _ n j).2 (by tauto)))
    have e6 := Nat.sInf_le (hmem (down (n - 1) (j + 1)) ((memTri_iff _ n j).2 (by tauto)))
    simp only [kdist]
    omega
  · obtain ⟨v, hv, hd⟩ := Nat.sInf_mem hne
    rw [← hd]
    rcases (memTri_iff v n j).1 hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [kdist] <;> omega

theorem kdist_eq_kmin (n j : ℤ) : (kdist n j : ℤ) = HexDistance.kmin n j := by
  have h1 := dist_up n j
  have h2 := dist_up (n - 1) j
  have h3 := dist_up n (j - 1)
  have h4 := dist_down n j
  have h5 := dist_down (n - 1) j
  have h6 := dist_down (n - 1) (j + 1)
  simp only [kdist, HexDistance.kmin]
  omega

/-- **Lemma `lem:krows`, as a statement about the graph distance in `X`.** -/
theorem lem_krows_dist (n j : ℤ) : (kdist n j : ℤ) = HexDistance.kClosed n j := by
  rw [kdist_eq_kmin, HexDistance.kmin_eq_kClosed]

/-- The same, spelled out: the distance in `X` from the base vertex to the vertex set of the
    face of the site `(n,j)` is the closed form displayed in the paper. -/
theorem lem_krows_face (n j : ℤ) :
    ((sInf {d : ℕ | ∃ v ∈ face n j, X.dist base v = d} : ℕ) : ℤ) = HexDistance.kClosed n j := by
  rw [kdist_eq_sInf, lem_krows_dist]

/-! ### 8. Spot checks against the breadth-first search

    `code/zeta_probe/tools/hexdist` computes `d_X` by breadth-first search from `e`.  The values
    below are read off its output; they are recomputed here from the formalised graph. -/

example : X.Adj base (down (-1) 0) := adj_up_same (-1) 0

example : X.dist base base = 0 := by rw [dist_eq_fhat, fhat_base]

example : (X.dist base (down (-1) 0) : ℤ) = 1 := by rw [dist_down]; decide

example : (X.dist base (up 0 0) : ℤ) = 2 := by rw [dist_up]; decide

-- row 0:  k(n,0) = 2n for n >= 0 and -2n-2 for n <= -1
example : (kdist 0 0 : ℤ) = 0 := by rw [lem_krows_dist]; decide
example : (kdist 1 0 : ℤ) = 2 := by rw [lem_krows_dist]; decide
example : (kdist (-1) 0 : ℤ) = 0 := by rw [lem_krows_dist]; decide
example : (kdist (-2) 0 : ℤ) = 2 := by rw [lem_krows_dist]; decide

-- row 1:  k(n,1) = 2n+1 for n >= 0, k(-1,1) = 0, -2n-3 for n <= -2
example : (kdist 0 1 : ℤ) = 1 := by rw [lem_krows_dist]; decide
example : (kdist (-1) 1 : ℤ) = 0 := by rw [lem_krows_dist]; decide
example : (kdist (-2) 1 : ℤ) = 1 := by rw [lem_krows_dist]; decide

-- row 3, the flat valley of Remark `rem:krows-shape`:  5,4,4,4,5,7,9,11,13 at n = -4..4
example : (kdist (-4) 3 : ℤ) = 5 := by rw [lem_krows_dist]; decide
example : (kdist (-3) 3 : ℤ) = 4 := by rw [lem_krows_dist]; decide
example : (kdist (-2) 3 : ℤ) = 4 := by rw [lem_krows_dist]; decide
example : (kdist (-1) 3 : ℤ) = 4 := by rw [lem_krows_dist]; decide
example : (kdist 0 3 : ℤ) = 5 := by rw [lem_krows_dist]; decide
example : (kdist 4 3 : ℤ) = 13 := by rw [lem_krows_dist]; decide

#print axioms adj_iff_sharesEdge
#print axioms memTri_iff
#print axioms dist_eq_fhat
#print axioms dist_up
#print axioms dist_down
#print axioms X_connected
#print axioms kdist_eq_sInf
#print axioms lem_krows_dist
#print axioms lem_krows_face

end HexGraph
