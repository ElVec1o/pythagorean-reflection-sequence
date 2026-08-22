/-
The merge on an actual lamp configuration.

`dataOf` gives walk-graph data from a configuration, and both conditions the
re-paired data takes are proved, so `swapData` applies to it.  Composing with
`walkCount_lt` gives what the descent consumes: re-pairing two arrivals lying in
different walks lowers the walk count.

One hypothesis is carried rather than discharged, `hmono`, that connectivity is not
destroyed by the re-pairing.  It is the cycle-minus-an-edge fact: each walk is a
cycle and loses one turn-edge, so it stays connected, and the surviving path
transports into the re-paired graph by `le_swapData`.  `reach_delete_turn` supplies
it for one edge at a time; assembling both is what remains.
-/
import Mathlib.Tactic
import DataBuild
import WalkGraph

namespace ConfigMerge

open EndType DataBuild WalkGraph

variable {n : ℕ} {m : Fin n → ℕ}

/-- The re-paired data of a configuration.  Both side conditions are supplied by the
two lemmas proved for the purpose.  The inputs are that `d` and `d'` are the
turn-partners of the two arrivals `a` and `a'`, that the four lie at one site, and
that they are pairwise distinct in the six ways the involution argument uses. -/
noncomputable def swapDataOf (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (a d a' d' : Endpt n m)
    (hta : turn up a = d) (hta' : turn up a' = d')
    (hd : siteOf d = siteOf a) (ha' : siteOf a' = siteOf a) (hd' : siteOf d' = siteOf a)
    (hda : d ≠ a) (hd'a : d' ≠ a) (ha'a : a' ≠ a)
    (hd'd : d' ≠ d) (ha'd' : a' ≠ d') (hda' : d ≠ a') :
    WalkGraph.Data (Endpt n m) :=
  swapData (dataOf up hbal) a d a' d'
    (swapT_invol (turn_invol up hbal) hta hta' hda hd'a ha'a hd'd ha'd' hda')
    (swapT_ne _ a d a' d' (turn_ne up hbal) hd'a hda')
    (partner_ne_swapT siteOf partner (turn up) a d a' d'
      (fun x => partner_site_ne x) (fun x => turnAt_site up hbal x) hd ha' hd')

/-- Reachability survives deleting a set of edges as soon as every adjacency is
itself recoverable in the smaller graph.  This is the general form of the
cycle-minus-an-edge argument: walk along the original path and replace each step
that used a deleted edge by a detour. -/
theorem reach_of_adj_reach {V : Type*} (G : SimpleGraph V) (S : Set (Sym2 V))
    (h : ∀ x y, G.Adj x y → (G.deleteEdges S).Reachable x y) :
    ∀ x y, G.Reachable x y → (G.deleteEdges S).Reachable x y := by
  intro x y hxy
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- `hmono` for the re-paired data: if every adjacency of the original walk graph
survives the deletion of the two re-paired turn-edges, then the re-pairing destroys
no connectivity, since the deleted graph sits inside the re-paired one. -/
theorem mono_swapData {α : Type*} [DecidableEq α] [Fintype α] (D : WalkGraph.Data α)
    (a d a' d' : α)
    (hd : D.t a = d) (hd' : D.t a' = d') (h1 h2 h3)
    (h : ∀ x y, (graph D).Adj x y →
      ((graph D).deleteEdges {s(a, d), s(a', d')}).Reachable x y) :
    ∀ x y, (graph D).Reachable x y →
      (graph (swapData D a d a' d' h1 h2 h3)).Reachable x y := by
  intro x y hxy
  exact ((reach_of_adj_reach (graph D) _ h) x y hxy).mono (le_swapData D a d a' d' hd hd' h1 h2 h3)

/-! ### The side conditions are not independent

The descent was stated with the turn-partner equations, six distinctness facts and a
"turn back" equation all as separate hypotheses.  All seven follow from the turn
structure together with `hsplit`, the one hypothesis that carries content.  Proving
that both shrinks the statement and is evidence against vacuity: a contradictory
hypothesis set would not admit these derivations with `hsplit` still standing. -/

section Derive
variable {α : Type*} [DecidableEq α] [Fintype α] (D : WalkGraph.Data α)
  {a d a' d' : α}

/-- The turn from `d'` goes back to `a'`: immediate from the involution. -/
theorem back_of_turn' {β : Type*} (D : WalkGraph.Data β) {a' d' : β}
    (hta' : D.t a' = d') : D.t d' = a' := by
  rw [← hta', D.t_invol]

/-- Two ends in different components are distinct. -/
theorem ne_of_split (hsplit : ¬ (graph D).Reachable a a') : a' ≠ a := by
  rintro rfl; exact hsplit (SimpleGraph.Reachable.refl _)

/-- An end differs from its own turn-partner. -/
theorem dep_ne_arr' {β : Type*} (D : WalkGraph.Data β) {a d : β}
    (hta : D.t a = d) : d ≠ a := by
  rw [← hta]; exact D.t_ne a

/-- Distinct arrivals have distinct turn-partners. -/
theorem dep_ne_dep' {β : Type*} (D : WalkGraph.Data β) {a d a' d' : β}
    (hta : D.t a = d) (hta' : D.t a' = d')
    (ha'a : a' ≠ a) : d' ≠ d := by
  intro h
  apply ha'a
  have : D.t (D.t a') = D.t (D.t a) := by rw [hta, hta', h]
  rwa [D.t_invol, D.t_invol] at this

/-- If one arrival were the other's turn-partner they would share a walk, which
`hsplit` forbids. -/
theorem dep_ne_other (hta' : D.t a' = d')
    (hsplit : ¬ (graph D).Reachable a a') : d' ≠ a := by
  rintro rfl
  exact hsplit (SimpleGraph.Adj.reachable (Or.inr hta'.symm)).symm

theorem dep_ne_other' (hta : D.t a = d)
    (hsplit : ¬ (graph D).Reachable a a') : d ≠ a' := by
  rintro rfl
  exact hsplit (SimpleGraph.Adj.reachable (Or.inr hta.symm))

end Derive

/-- **The descent on an actual configuration.**  Re-pairing two arrivals that lie
at a common site but in *different* walks lowers the walk count.

Every hypothesis is about the configuration rather than about an abstract graph:
`hta`/`hta'` say `d`, `d'` are the turn-partners; the `siteOf` equations say the
four ends share a site; the distinctness facts are the six the involution argument
uses; `hadj` is the cycle-minus-an-edge input; the `k`-conditions say the walk
through `d'` does not re-use the two re-paired edges before closing; and `hsplit`
is the hypothesis that gives the descent its content, that `a` and `a'` start in
different walks. -/
theorem config_walkCount_lt (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (a d a' d' : Endpt n m)
    (hta : turn up a = d) (hta' : turn up a' = d')
    (hd : siteOf d = siteOf a) (ha' : siteOf a' = siteOf a) (hd' : siteOf d' = siteOf a)
    (hda : d ≠ a) (hd'a : d' ≠ a) (ha'a : a' ≠ a)
    (hd'd : d' ≠ d) (ha'd' : a' ≠ d') (hda' : d ≠ a')
    (hadj : ∀ x y, (graph (dataOf up hbal)).Adj x y →
      ((graph (dataOf up hbal)).deleteEdges {s(a, d), s(a', d')}).Reachable x y)
    (M : ℕ) (hM : (sig (dataOf up hbal))^[M] d' = d') (hpos : 0 < M)
    (k₁ : ∀ k, k < M - 1 →
      s((sig (dataOf up hbal))^[k] d',
        (dataOf up hbal).p ((sig (dataOf up hbal))^[k] d')) ∉
        ({s(a, d), s(a', d')} : Set (Sym2 (Endpt n m))))
    (k₂ : ∀ k, k < M - 1 →
      s((dataOf up hbal).p ((sig (dataOf up hbal))^[k] d'),
        (dataOf up hbal).t ((dataOf up hbal).p ((sig (dataOf up hbal))^[k] d'))) ∉
        ({s(a, d), s(a', d')} : Set (Sym2 (Endpt n m))))
    (klast : s((sig (dataOf up hbal))^[M-1] d',
        (dataOf up hbal).p ((sig (dataOf up hbal))^[M-1] d')) ∉
        ({s(a, d), s(a', d')} : Set (Sym2 (Endpt n m))))
    (hback : (dataOf up hbal).t d' = a')
    (hsplit : ¬ (graph (dataOf up hbal)).Reachable a a') :
    walkCount (swapDataOf up hbal a d a' d' hta hta' hd ha' hd'
        hda hd'a ha'a hd'd ha'd' hda') <
      walkCount (dataOf up hbal) := by
  refine walkCount_lt _ _ ?_ a a' hsplit ?_
  · exact mono_swapData (dataOf up hbal) a d a' d' hta hta' _ _ _ hadj
  · exact merge_connects_full (dataOf up hbal) a d a' d' hta hta' _ _ _
      M hM hpos k₁ k₂ klast hback

/-- **The descent, with the redundant side conditions discharged.**

Same conclusion as `config_walkCount_lt`, but the six distinctness facts and the
turn-back equation are now *derived* rather than assumed.  What remains are the two
turn-partner equations, the shared site, the cycle input `hadj`, the walk-closure
data, and `hsplit`. -/
theorem config_descent (up : Fin n → ℕ)
    (hbal : ∀ s : ℤ, (arrAt (m := m) up s).card = (depAt (m := m) up s).card)
    (a d a' d' : Endpt n m)
    (hta : turn up a = d) (hta' : turn up a' = d')
    (hd : siteOf d = siteOf a) (ha' : siteOf a' = siteOf a) (hd' : siteOf d' = siteOf a)
    (hadj : ∀ x y, (graph (dataOf up hbal)).Adj x y →
      ((graph (dataOf up hbal)).deleteEdges {s(a, d), s(a', d')}).Reachable x y)
    (M : ℕ) (hM : (sig (dataOf up hbal))^[M] d' = d') (hpos : 0 < M)
    (k₁ : ∀ k, k < M - 1 →
      s((sig (dataOf up hbal))^[k] d',
        (dataOf up hbal).p ((sig (dataOf up hbal))^[k] d')) ∉
        ({s(a, d), s(a', d')} : Set (Sym2 (Endpt n m))))
    (k₂ : ∀ k, k < M - 1 →
      s((dataOf up hbal).p ((sig (dataOf up hbal))^[k] d'),
        (dataOf up hbal).t ((dataOf up hbal).p ((sig (dataOf up hbal))^[k] d'))) ∉
        ({s(a, d), s(a', d')} : Set (Sym2 (Endpt n m))))
    (klast : s((sig (dataOf up hbal))^[M-1] d',
        (dataOf up hbal).p ((sig (dataOf up hbal))^[M-1] d')) ∉
        ({s(a, d), s(a', d')} : Set (Sym2 (Endpt n m))))
    (hsplit : ¬ (graph (dataOf up hbal)).Reachable a a') :
    walkCount (swapDataOf up hbal a d a' d' hta hta' hd ha' hd'
        (dep_ne_arr' (dataOf up hbal) hta) (dep_ne_other (dataOf up hbal) hta' hsplit) (ne_of_split (dataOf up hbal) hsplit)
        (dep_ne_dep' (dataOf up hbal) hta hta' (ne_of_split (dataOf up hbal) hsplit)) 
        (Ne.symm (dep_ne_arr' (dataOf up hbal) hta')) (dep_ne_other' (dataOf up hbal) hta hsplit)) <
      walkCount (dataOf up hbal) :=
  config_walkCount_lt up hbal a d a' d' hta hta' hd ha' hd'
    (dep_ne_arr' (dataOf up hbal) hta) (dep_ne_other (dataOf up hbal) hta' hsplit) (ne_of_split (dataOf up hbal) hsplit)
    (dep_ne_dep' (dataOf up hbal) hta hta' (ne_of_split (dataOf up hbal) hsplit))
    (Ne.symm (dep_ne_arr' (dataOf up hbal) hta')) (dep_ne_other' (dataOf up hbal) hta hsplit)
    hadj M hM hpos k₁ k₂ klast (back_of_turn' (dataOf up hbal) hta') hsplit

/-! ### The entry point of the descent

The descent needs `hsplit`: two ends in different walks.  That is available exactly
when there is more than one walk, which is the condition under which the descent is
invoked in the first place. -/

theorem exists_split_of_walkCount {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (h : 1 < walkCount D) :
    ∃ x y : α, ¬ (graph D).Reachable x y := by
  obtain ⟨c₁, c₂, hne⟩ := Fintype.exists_pair_of_one_lt_card h
  obtain ⟨x, hx⟩ := Quot.exists_rep c₁
  obtain ⟨y, hy⟩ := Quot.exists_rep c₂
  refine ⟨x, y, fun hr => hne ?_⟩
  rw [← hx, ← hy]
  exact SimpleGraph.ConnectedComponent.eq.mpr hr

/-- Contrapositive: if every pair of ends is joined, there is exactly one walk.  This
is the descent's stopping condition. -/
theorem walkCount_le_one_of_connected {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (h : ∀ x y : α, (graph D).Reachable x y) :
    walkCount D ≤ 1 := by
  by_contra hc
  obtain ⟨x, y, hxy⟩ := exists_split_of_walkCount D (by omega)
  exact hxy (h x y)

/-- **The descent principle.**  If from any data with more than one walk we can step
to data with strictly fewer walks while preserving a property `P`, then from any `P`
we reach data with a single walk.  This is the shape M6's argument uses: the merge
lowers the walk count, so iterating it ends. -/
theorem reaches_one {α : Type*} [DecidableEq α] [Fintype α]
    {P : WalkGraph.Data α → Prop}
    (step : ∀ D, 1 < walkCount D → P D → ∃ D', P D' ∧ walkCount D' < walkCount D) :
    ∀ D, P D → ∃ D', P D' ∧ walkCount D' ≤ 1 := by
  have key : ∀ n D, walkCount D = n → P D → ∃ D', P D' ∧ walkCount D' ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro D hn hP
      by_cases h : 1 < walkCount D
      · obtain ⟨D', hP', hlt⟩ := step D h hP
        exact ih (walkCount D') (hn ▸ hlt) D' rfl hP'
      · exact ⟨D, hP, by omega⟩
  exact fun D hP => key (walkCount D) D rfl hP

/-! ### `hadj` is not an extra assumption

The cycle input `hadj` quantifies over every adjacency, but the walk graph has only
two kinds of edge and each is handled.

A *crossing* edge is never one of the deleted turn edges -- that is `crossing_ne_turn`
below, and it is exactly `pt_ne` doing its work.  A *turn* edge that is not deleted
survives; a turn edge that is deleted has the detour supplied by
`reach_delete_turn_set`.  So `hadj` follows from orbit data at the two arrivals, of
the same kind the merge already carries. -/

section Hadj

/-- **A crossing edge is never a turn edge.**  If `{x, p x} = {z, t z}` then either
`p x = t x`, or `p (t z) = t (t z)`; both contradict `pt_ne`. -/
theorem crossing_ne_turn {α : Type*} (D : WalkGraph.Data α) (x z : α) :
    s(x, D.p x) ≠ s(z, D.t z) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; exact D.pt_ne x h2
  · subst h1
    exact D.pt_ne (D.t z) (by rw [h2, D.t_invol])

/-- Consequently no crossing edge lies in the two-element set of deleted turn edges. -/
theorem crossing_notMem {α : Type*} (D : WalkGraph.Data α) (x a a' : α) :
    s(x, D.p x) ∉ ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨crossing_ne_turn D x a, crossing_ne_turn D x a'⟩

end Hadj

/-- **`hadj` reduces to two detours.**  Given that each deleted turn edge's endpoints
remain joined after the deletion, every adjacency survives: crossing edges are never
deleted, undeleted turn edges are still there, and a deleted turn edge is exactly one
of the two with a detour. -/
theorem hadj_of_detours {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a a' : α)
    (Ra : ((graph D).deleteEdges
      ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α))).Reachable a (D.t a))
    (Ra' : ((graph D).deleteEdges
      ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α))).Reachable a' (D.t a')) :
    ∀ x y, (graph D).Adj x y →
      ((graph D).deleteEdges
        ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α))).Reachable x y := by
  intro x y hxy
  rcases hxy with h | h
  · -- a crossing edge, never deleted
    subst h
    exact (SimpleGraph.deleteEdges_adj.mpr
      ⟨Or.inl rfl, crossing_notMem D x a a'⟩).reachable
  · subst h
    by_cases hmem : s(x, D.t x) ∈
        ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α))
    · -- a deleted turn edge: it is one of the two, so it has its detour
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at hmem
      rcases hmem with (⟨h1, _⟩ | ⟨h1, h2⟩) | (⟨h1, _⟩ | ⟨h1, h2⟩)
      · subst h1; exact Ra
      · subst h1; rw [D.t_invol]; exact Ra.symm
      · subst h1; exact Ra'
      · subst h1; rw [D.t_invol]; exact Ra'.symm
    · exact (SimpleGraph.deleteEdges_adj.mpr ⟨Or.inr rfl, hmem⟩).reachable

/-! ### One condition, three instances

The descent's remaining hypotheses were three different-looking things: the cycle
input, the walk-closure data, and the join.  They are all the same condition -- an
orbit closes without using the deleted edges before its last step -- applied at the
two arrivals and at one departure. -/

/-- The `sig`-orbit through `x` closes after `M` steps without touching `S` before
the last step. -/
def ClosesAvoiding {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (S : Set (Sym2 α)) (x : α) (M : ℕ) : Prop :=
  (sig D)^[M] x = x ∧ 0 < M ∧
  (∀ k, k < M - 1 → s((sig D)^[k] x, D.p ((sig D)^[k] x)) ∉ S) ∧
  (∀ k, k < M - 1 → s(D.p ((sig D)^[k] x), D.t (D.p ((sig D)^[k] x))) ∉ S) ∧
  s((sig D)^[M - 1] x, D.p ((sig D)^[M - 1] x)) ∉ S

/-- A closing orbit gives the detour across `x`'s turn edge. -/
theorem detour_of_closes {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (S : Set (Sym2 α)) (x : α) (M : ℕ)
    (h : ClosesAvoiding D S x M) :
    ((graph D).deleteEdges S).Reachable x (D.t x) := by
  obtain ⟨hM, hpos, k₁, k₂, klast⟩ := h
  exact reach_delete_turn_set D S x M hM hpos k₁ k₂ klast

/-- **The descent, with uniform hypotheses.**  Three instances of `ClosesAvoiding` --
at the two arrivals and at the second departure -- replace the cycle input, the
walk-closure data and the join.  Everything else is the placement: the two arrivals
share a site and lie in different walks. -/
theorem config_descent_uniform {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a a' : α)
    (Ma Ma' Md : ℕ)
    (ha : ClosesAvoiding D ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α)) a Ma)
    (ha' : ClosesAvoiding D ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α)) a' Ma')
    (hd : ClosesAvoiding D ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α)) (D.t a') Md)
    (hsplit : ¬ (graph D).Reachable a a')
    (h1 h2 h3) :
    walkCount (swapData D a (D.t a) a' (D.t a') h1 h2 h3) < walkCount D := by
  refine walkCount_lt D _ ?_ a a' hsplit ?_
  · exact mono_swapData D a (D.t a) a' (D.t a') rfl rfl h1 h2 h3
      (hadj_of_detours D a a' (detour_of_closes D _ a Ma ha)
        (detour_of_closes D _ a' Ma' ha'))
  · obtain ⟨hM, hpos, k₁, k₂, klast⟩ := hd
    exact merge_connects_full D a (D.t a) a' (D.t a') rfl rfl h1 h2 h3
      Md hM hpos k₁ k₂ klast (back_of_turn' D rfl)

/-! ### Orbits always close

Two of `ClosesAvoiding`'s five parts are free.  `sig` is injective and the end set is
finite, so every orbit is periodic: `hM` and `hpos` cost nothing.  The content of the
condition is entirely in the three avoidance clauses. -/

/-- **Every `sig`-orbit closes.**  The iterates of `x` cannot all be distinct, and
`sig` is injective, so an early repeat can be cancelled back to `x` itself. -/
theorem exists_closes {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (x : α) :
    ∃ M : ℕ, 0 < M ∧ (sig D)^[M] x = x := by
  classical
  obtain ⟨i, j, hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (Fintype.card α + 1) => (sig D)^[n.val] x) (by simp)
  have hinj : ∀ k : ℕ, Function.Injective ((sig D)^[k]) :=
    fun k => Function.Injective.iterate (sig_injective D) k
  rcases lt_or_gt_of_ne (fun hc : i.val = j.val => hne (Fin.ext hc)) with hlt | hlt
  · refine ⟨j.val - i.val, by omega, ?_⟩
    apply hinj i.val
    rw [← Function.iterate_add_apply]
    have : i.val + (j.val - i.val) = j.val := by omega
    rw [this]
    exact h.symm
  · refine ⟨i.val - j.val, by omega, ?_⟩
    apply hinj j.val
    rw [← Function.iterate_add_apply]
    have : j.val + (i.val - j.val) = i.val := by omega
    rw [this]
    exact h

/-- **Four of the five clauses are free.**  The deleted set consists of *turn* edges.
Clauses `k₁` and `klast` are about *crossing* edges, which `crossing_notMem` says are
never turn edges; `hM` and `hpos` come from `exists_closes`.  All the content of
`ClosesAvoiding` sits in `k₂`, the clause about the orbit's turn edges. -/
theorem closes_of_turn_clause {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a a' x : α) (M : ℕ)
    (hM : (sig D)^[M] x = x) (hpos : 0 < M)
    (k₂ : ∀ k, k < M - 1 →
      s(D.p ((sig D)^[k] x), D.t (D.p ((sig D)^[k] x))) ∉
        ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α))) :
    ClosesAvoiding D ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α)) x M :=
  ⟨hM, hpos, fun _ _ => crossing_notMem D _ a a', k₂, crossing_notMem D _ a a'⟩

/-- The turn edge the orbit uses at step `k` runs from `p (sig^k x)` to `sig^(k+1) x`,
since `sig y = t (p y)`.  This is what makes `k₂` a statement about where the orbit
goes next. -/
theorem orbit_turn_edge {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (x : α) (k : ℕ) :
    D.t (D.p ((sig D)^[k] x)) = (sig D)^[k + 1] x := by
  rw [Function.iterate_succ_apply']
  rfl

/-- Every point of an orbit is in the same walk as its start: each `sig` step is two
graph edges, through the crossing partner. -/
theorem reach_sig_iter {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (x : α) (k : ℕ) :
    (graph D).Reachable x ((sig D)^[k] x) := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    refine ih.trans ?_
    rw [Function.iterate_succ_apply']
    exact (SimpleGraph.Adj.reachable (G := graph D) (Or.inl rfl)).trans
      (SimpleGraph.Adj.reachable (G := graph D) (Or.inr rfl))

/-- **The cross-walk half of `k₂`.**  An orbit starting at `a` never meets the turn
edge of `a'`, because every point it visits is in `a`'s walk and `a'` is not.  This
uses `hsplit` and nothing else. -/
theorem orbit_avoids_other {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a a' : α)
    (hsplit : ¬ (graph D).Reachable a a') (k : ℕ) :
    s(D.p ((sig D)^[k] a), D.t (D.p ((sig D)^[k] a))) ≠ s(a', D.t a') := by
  intro h
  -- every point of `a`'s orbit, and its crossing partner, lies in `a`'s walk
  have hreach : (graph D).Reachable a (D.p ((sig D)^[k] a)) :=
    (reach_sig_iter D a k).trans (SimpleGraph.Adj.reachable (G := graph D) (Or.inl rfl))
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hsplit (h1 ▸ hreach)
  · -- it landed on `t a'`, which is joined to `a'` by a turn edge
    exact hsplit ((h1 ▸ hreach).trans
      (SimpleGraph.Adj.reachable (G := graph D) (Or.inr rfl)).symm)

/-! ### The structure of `sig`, and the parity gap

Two identities relate `sig` to its two involutions.  They are worth banking: they say
the walk graph carries a dihedral action, `p` conjugating `sig` to its inverse.

They do *not* close the remaining half of `k₂`.  That half needs `p a` never to lie
in `a`'s own `sig`-orbit, which is true -- each walk is an even cycle alternating
crossing and turn edges, and the two `sig`-orbits are its two alternating classes --
but it is a *parity* fact about the cycle, not a consequence of the identities below.
The dihedral relations alone are consistent with `p a = sig^k a`; what rules it out
is that the cycle has even length and `p a` is adjacent to `a` on it. -/

/-- **`sig` after `p` is `t`.**  Since `sig y = t (p y)` and `p` is an involution. -/
theorem sig_p_eq_t {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (x : α) : sig D (D.p x) = D.t x := by
  unfold sig
  rw [D.p_invol]

/-- **`p ∘ t` inverts `sig`.**  So the two involutions generate a dihedral action, with
`p` conjugating `sig` to `sig⁻¹`. -/
theorem p_t_sig {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (x : α) : D.p (D.t (sig D x)) = x := by
  unfold sig
  rw [D.t_invol, D.p_invol]

/-- **The remaining half of `k₂`, stated.**  If the orbit at `a` meets `a`'s own turn
edge at step `k`, then either the orbit closes early -- excluded by minimality -- or
`p a` lies in the orbit, which is the parity fact still to be proved. -/
theorem k2_self_dichotomy {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a : α) (k : ℕ)
    (h : s(D.p ((sig D)^[k] a), D.t (D.p ((sig D)^[k] a))) = s(a, D.t a)) :
    (sig D)^[k + 1] a = a ∨ (sig D)^[k] a = D.p a := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
  · right
    have h := congrArg D.p h1
    rwa [D.p_invol] at h
  · left
    rwa [orbit_turn_edge D a k] at h2

/-! ### The parity fact, closed

`p a` never lies in `a`'s own `sig`-orbit.  The argument needs neither the period nor
modular arithmetic: conjugating by `sig^[k]` turns `p_ne` and `t_ne` at `sig^[k] a`
into `p a ≠ sig^[2k] a` and `t a ≠ sig^[2k] a`.  Since `p a = sig^[m] a` gives
`t a = sig^[m+1] a`, and one of `m`, `m+1` is even, taking `k` to be half of it
contradicts one or the other.

(Checked first on all 6426 fixed-point-free involution pairs with `p x ≠ t x` on 4, 6
and 8 points: no violations.) -/

/-- `sig` conjugates `p` across one step. -/
theorem sig_p_sig {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (y : α) : sig D (D.p (sig D y)) = D.p y := by
  unfold sig
  rw [D.p_invol, D.t_invol]

/-- Conjugating by `sig^[k]` returns `p`. -/
theorem conj_iter {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a : α) (k : ℕ) :
    (sig D)^[k] (D.p ((sig D)^[k] a)) = D.p a := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [sig_p_sig]
    exact ih

/-- `p_ne`, conjugated: `p a` is never an even iterate. -/
theorem p_ne_even {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a : α) (k : ℕ) : D.p a ≠ (sig D)^[2 * k] a := by
  intro h
  have hinj : Function.Injective ((sig D)^[k]) :=
    Function.Injective.iterate (sig_injective D) k
  apply D.p_ne ((sig D)^[k] a)
  apply hinj
  rw [conj_iter D a k, h, two_mul, Function.iterate_add_apply]

/-- `t_ne`, conjugated: `t a` is never an even iterate either. -/
theorem t_ne_even {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a : α) (k : ℕ) : D.t a ≠ (sig D)^[2 * k] a := by
  intro h
  have hinj : Function.Injective ((sig D)^[k]) :=
    Function.Injective.iterate (sig_injective D) k
  apply D.t_ne ((sig D)^[k] a)
  apply hinj
  have hcomm : (sig D)^[k] (D.t ((sig D)^[k] a)) = D.t a := by
    rw [← sig_p_eq_t D ((sig D)^[k] a), ← Function.iterate_succ_apply,
      Function.iterate_succ_apply', conj_iter D a k]
    exact sig_p_eq_t D a
  rw [hcomm, h, two_mul, Function.iterate_add_apply]

/-- **The parity fact.**  `p a` never lies in `a`'s own `sig`-orbit.

If `p a = sig^[m] a` then `t a = sig^[m+1] a`, and one of `m`, `m+1` is even.  An even
iterate is excluded for `p a` by `p_ne_even` and for `t a` by `t_ne_even`, so either
way there is a contradiction.  No period and no modular arithmetic are needed. -/
theorem p_not_in_orbit {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a : α) (m : ℕ) : D.p a ≠ (sig D)^[m] a := by
  intro h
  have hta : D.t a = (sig D)^[m + 1] a := by
    rw [← sig_p_eq_t D a, h, Function.iterate_succ_apply']
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact p_ne_even D a k (by rw [h, hk]; ring_nf)
  · exact t_ne_even D a (k + 1) (by rw [hta, hk]; ring_nf)

/-- **The self half of `k₂`.**  With `M` minimal, the orbit at `a` never meets `a`'s
own turn edge before its last step: `k2_self_dichotomy`'s first case is excluded by
minimality and its second by the parity fact. -/
theorem orbit_avoids_self {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a : α) (M : ℕ)
    (hmin : ∀ j, 0 < j → j < M → (sig D)^[j] a ≠ a)
    (k : ℕ) (hk : k < M - 1) (hM : 0 < M) :
    s(D.p ((sig D)^[k] a), D.t (D.p ((sig D)^[k] a))) ≠ s(a, D.t a) := by
  intro h
  rcases k2_self_dichotomy D a k h with hclose | hp
  · exact hmin (k + 1) (by omega) (by omega) hclose
  · exact p_not_in_orbit D a k hp.symm

/-- **`k₂` holds.**  Both halves: the orbit at `a` avoids `a`'s own turn edge by
minimality and parity, and `a'`'s turn edge because `a'` is in another walk. -/
theorem k2_holds {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a a' : α)
    (hsplit : ¬ (graph D).Reachable a a') (M : ℕ) (hM : 0 < M)
    (hmin : ∀ j, 0 < j → j < M → (sig D)^[j] a ≠ a) :
    ∀ k, k < M - 1 →
      s(D.p ((sig D)^[k] a), D.t (D.p ((sig D)^[k] a))) ∉
        ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α)) := by
  intro k hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨orbit_avoids_self D a M hmin k hk hM, orbit_avoids_other D a a' hsplit k⟩

/-- **`ClosesAvoiding` holds at either arrival.**  Taking the minimal period, every
clause is discharged: `hM`/`hpos` from `exists_closes`, `k₁`/`klast` because they are
crossing edges, and `k₂` from `k2_holds`. -/
theorem closes_at {α : Type*} [DecidableEq α] [Fintype α]
    (D : WalkGraph.Data α) (a a' : α)
    (hsplit : ¬ (graph D).Reachable a a') :
    ∃ M, ClosesAvoiding D ({s(a, D.t a), s(a', D.t a')} : Set (Sym2 α)) a M := by
  classical
  have hex : ∃ M : ℕ, 0 < M ∧ (sig D)^[M] a = a := exists_closes D a
  let M := Nat.find hex
  have hspec : 0 < M ∧ (sig D)^[M] a = a := Nat.find_spec hex
  refine ⟨M, closes_of_turn_clause D a a' a M hspec.2 hspec.1 ?_⟩
  refine k2_holds D a a' hsplit M hspec.1 ?_
  intro j hj hjM hcon
  exact Nat.find_min hex hjM ⟨hj, hcon⟩

-- Certification (Rule 5).
#print axioms ConfigMerge.k2_holds
#print axioms ConfigMerge.closes_at
