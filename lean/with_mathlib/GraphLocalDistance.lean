/-
  GraphLocalDistance.lean
  =======================
  The local criterion for a graph distance function, in the generality in which it is true.

  Let `G` be a simple graph, `e` a vertex, and `f` a function from the vertices to `ℕ`.  If

      (a)  `f e = 0`,
      (b)  `f w ≤ f a + 1` whenever `a` and `w` are adjacent            (1-Lipschitz),
      (c)  every vertex `v ≠ e` has a neighbour `w` with `f w + 1 = f v` (descent),

  then `f v = d_G(e, v)` for every `v`.  This is the statement that `HexDistance.lean` reduces
  the honeycomb geometry to; it is proved here once, for an arbitrary graph, so that the
  instantiation in `HexGraph.lean` is a matter of supplying (a), (b), (c).

  The two halves are independent:

    * (a) and (c) build, by induction on `f v`, an explicit walk from `e` to `v` of length
      exactly `f v`, whence `d_G(e,v) ≤ f v` and in particular `v` is reachable from `e`;
    * (a) and (b) give `f b ≤ f a + |p|` for every walk `p` from `a` to `b`, by induction on
      the walk, whence `f v ≤ d_G(e,v)` on a walk realising the distance.

  No finiteness, local finiteness, connectedness or decidability is assumed.
-/

import Mathlib.Combinatorics.SimpleGraph.Metric

namespace GraphLocalDistance

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### 1. Descent builds a walk of the claimed length -/

/-- **Descent gives a walk of length exactly `f v`.**  Uses (a) and (c) only. -/
theorem exists_walk_length_eq {e : V} {f : V → ℕ} (h0 : f e = 0)
    (hdesc : ∀ v, v ≠ e → ∃ w, G.Adj v w ∧ f w + 1 = f v) (v : V) :
    ∃ p : G.Walk e v, p.length = f v := by
  suffices h : ∀ n : ℕ, ∀ v : V, f v ≤ n → ∃ p : G.Walk e v, p.length = f v from
    h (f v) v le_rfl
  intro n
  induction n with
  | zero =>
      intro v hv
      by_cases hve : v = e
      · subst hve
        exact ⟨Walk.nil, by rw [Walk.length_nil, h0]⟩
      · obtain ⟨w, _, hfw⟩ := hdesc v hve
        exfalso; omega
  | succ n ih =>
      intro v hv
      by_cases hve : v = e
      · subst hve
        exact ⟨Walk.nil, by rw [Walk.length_nil, h0]⟩
      · obtain ⟨w, haw, hfw⟩ := hdesc v hve
        obtain ⟨p, hp⟩ := ih w (by omega)
        refine ⟨p.concat haw.symm, ?_⟩
        rw [Walk.length_concat, hp]
        omega

/-- **Reachability**, an immediate consequence of (a) and (c). -/
theorem reachable_of_descent {e : V} {f : V → ℕ} (h0 : f e = 0)
    (hdesc : ∀ v, v ≠ e → ∃ w, G.Adj v w ∧ f w + 1 = f v) (v : V) :
    G.Reachable e v :=
  ⟨(exists_walk_length_eq h0 hdesc v).choose⟩

/-! ### 2. A 1-Lipschitz function grows by at most the length of a walk -/

/-- **The Lipschitz bound along a walk.**  Uses (b) only. -/
theorem le_add_length {f : V → ℕ} (hlip : ∀ a b : V, G.Adj a b → f b ≤ f a + 1) :
    ∀ {a b : V} (p : G.Walk a b), f b ≤ f a + p.length := by
  intro a b p
  induction p with
  | nil => simp
  | cons hadj q ih =>
      rw [Walk.length_cons]
      have := hlip _ _ hadj
      omega

/-! ### 3. The criterion -/

/-- **The local criterion for a graph distance.**  If `f` vanishes at `e`, changes by at most
    one across every edge, and strictly descends somewhere out of every vertex other than `e`,
    then `f` is the distance from `e`. -/
theorem dist_eq_of_base_lip_descent {e : V} {f : V → ℕ}
    (h0 : f e = 0)
    (hlip : ∀ a b : V, G.Adj a b → f b ≤ f a + 1)
    (hdesc : ∀ v, v ≠ e → ∃ w, G.Adj v w ∧ f w + 1 = f v)
    (v : V) : G.dist e v = f v := by
  obtain ⟨p, hp⟩ := exists_walk_length_eq h0 hdesc v
  have hle : G.dist e v ≤ f v := by
    have := SimpleGraph.dist_le p
    omega
  have hr : G.Reachable e v := ⟨p⟩
  obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
  have hge := le_add_length hlip q
  omega

/-- The same criterion with the Lipschitz hypothesis in the symmetric two-sided form.  Only one
    direction of the two-sided bound is used; the other is recorded because the two-sided form
    is what a concrete verification naturally produces. -/
theorem dist_eq_of_base_lip_descent' {e : V} {f : V → ℕ}
    (h0 : f e = 0)
    (hlip : ∀ a b : V, G.Adj a b → f a ≤ f b + 1 ∧ f b ≤ f a + 1)
    (hdesc : ∀ v, v ≠ e → ∃ w, G.Adj v w ∧ f w + 1 = f v)
    (v : V) : G.dist e v = f v :=
  dist_eq_of_base_lip_descent h0 (fun a b h => (hlip a b h).2) hdesc v

#print axioms exists_walk_length_eq
#print axioms le_add_length
#print axioms dist_eq_of_base_lip_descent
#print axioms dist_eq_of_base_lip_descent'

end GraphLocalDistance
