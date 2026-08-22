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
theorem back_of_turn (hta' : D.t a' = d') : D.t d' = a' := by
  rw [← hta', D.t_invol]

/-- Two ends in different components are distinct. -/
theorem ne_of_split (hsplit : ¬ (graph D).Reachable a a') : a' ≠ a := by
  rintro rfl; exact hsplit (SimpleGraph.Reachable.refl _)

/-- An end differs from its own turn-partner. -/
theorem dep_ne_arr (hta : D.t a = d) : d ≠ a := by
  rw [← hta]; exact D.t_ne a

/-- Distinct arrivals have distinct turn-partners. -/
theorem dep_ne_dep (hta : D.t a = d) (hta' : D.t a' = d')
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
        (dep_ne_arr (dataOf up hbal) hta) (dep_ne_other (dataOf up hbal) hta' hsplit) (ne_of_split (dataOf up hbal) hsplit)
        (dep_ne_dep (dataOf up hbal) hta hta' (ne_of_split (dataOf up hbal) hsplit)) 
        (Ne.symm (dep_ne_arr (dataOf up hbal) hta')) (dep_ne_other' (dataOf up hbal) hta hsplit)) <
      walkCount (dataOf up hbal) :=
  config_walkCount_lt up hbal a d a' d' hta hta' hd ha' hd'
    (dep_ne_arr (dataOf up hbal) hta) (dep_ne_other (dataOf up hbal) hta' hsplit) (ne_of_split (dataOf up hbal) hsplit)
    (dep_ne_dep (dataOf up hbal) hta hta' (ne_of_split (dataOf up hbal) hsplit))
    (Ne.symm (dep_ne_arr (dataOf up hbal) hta')) (dep_ne_other' (dataOf up hbal) hta hsplit)
    hadj M hM hpos k₁ k₂ klast (back_of_turn (dataOf up hbal) hta') hsplit

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

-- Certification (Rule 5).
#print axioms ConfigMerge.reaches_one
