/-
The walk graph of two involutions, and its 2-regularity.

Adjacency is "the other end of my crossing, or my partner at my site".  Both maps
are involutions, so the relation is symmetric; each is fixed-point free and they
never agree, since one moves between the two sites of an edge and the other stays
at a site, so every end has exactly two neighbours.

This is the graph whose components are the walks.  2-regularity is what makes those
components cycles, and hence what makes every edge lie in a cycle, which by
`SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem` makes no edge a bridge and
discharges `WalkMerge.conn_merge`'s hypothesis.
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import WalkMerge
import TurnBuild
import OrbitCount

namespace WalkGraph

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The data of a walk graph: two fixed-point-free involutions that never agree. -/
structure Data (α : Type*) where
  p : α → α
  t : α → α
  p_invol : ∀ x, p (p x) = x
  t_invol : ∀ x, t (t x) = x
  p_ne : ∀ x, p x ≠ x
  t_ne : ∀ x, t x ≠ x
  pt_ne : ∀ x, p x ≠ t x

variable (D : Data α)

/-- Adjacency: the crossing partner or the site partner. -/
def Adj (x y : α) : Prop := y = D.p x ∨ y = D.t x

omit [DecidableEq α] [Fintype α] in
theorem adj_symm {x y : α} (h : Adj D x y) : Adj D y x := by
  rcases h with rfl | rfl
  · exact Or.inl (D.p_invol x).symm
  · exact Or.inr (D.t_invol x).symm

omit [DecidableEq α] [Fintype α] in
theorem adj_irrefl (x : α) : ¬ Adj D x x := by
  rintro (h | h)
  · exact D.p_ne x h.symm
  · exact D.t_ne x h.symm

/-- The walk graph. -/
def graph : SimpleGraph α where
  Adj := Adj D
  symm := fun _ _ h => adj_symm D h
  loopless := ⟨adj_irrefl D⟩

instance : DecidableRel (graph D).Adj := fun _ _ => by
  unfold graph Adj; infer_instance

/-- The neighbours of an end are exactly its two partners. -/
theorem neighbor_eq (x : α) :
    (graph D).neighborFinset x = {D.p x, D.t x} := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  exact Iff.rfl

/-- **2-regularity.**  Every end has exactly two neighbours, since the two partners
are distinct. -/
theorem degree_eq_two (x : α) : (graph D).degree x = 2 := by
  unfold SimpleGraph.degree
  rw [neighbor_eq D x]
  rw [Finset.card_insert_of_notMem (by simpa using D.pt_ne x), Finset.card_singleton]

/-! ### Non-vacuity: a four-end configuration satisfying the data. -/

def pW : Fin 4 → Fin 4 := ![1, 0, 3, 2]
def tW : Fin 4 → Fin 4 := ![2, 3, 0, 1]

def dataW : Data (Fin 4) where
  p := pW
  t := tW
  p_invol := by decide
  t_invol := by decide
  p_ne := by decide
  t_ne := by decide
  pt_ne := by decide

theorem witness_degree : (graph dataW).degree 0 = 2 := degree_eq_two dataW 0

/-! ### From "not a bridge" to the path the merge needs -/

omit [DecidableEq α] [Fintype α] in
/-- The turn-edge at `x` is an edge of the walk graph. -/
theorem adj_turn (x : α) : (graph D).Adj x (D.t x) := Or.inr rfl

omit [DecidableEq α] [Fintype α] in
/-- **The reduction.**  If the turn-edge at `x` is not a bridge, its endpoints stay
connected after it is deleted.  That surviving path is `WalkMerge.conn_merge`'s
hypothesis: it uses only crossing-edges and turn-edges other than the deleted one,
all of which the re-paired graph still has. -/
theorem reachable_delete_of_not_bridge (x : α)
    (hnb : ¬ (graph D).IsBridge s(x, D.t x)) :
    ((graph D).deleteEdges {s(x, D.t x)}).Reachable x (D.t x) := by
  rw [SimpleGraph.isBridge_iff] at hnb
  push Not at hnb
  exact hnb (adj_turn D x)

omit [DecidableEq α] [Fintype α] in
/-- Equivalently, exhibiting a cycle through the turn-edge suffices.  This is the
form 2-regularity feeds: in a 2-regular graph every edge lies in a cycle, so no
edge is a bridge. -/
theorem not_bridge_of_cycle (x : α) {u : α} (c : (graph D).Walk u u)
    (hc : c.IsCycle) (hmem : s(x, D.t x) ∈ c.edges) :
    ¬ (graph D).IsBridge s(x, D.t x) := by
  rw [SimpleGraph.isBridge_iff_adj_and_forall_cycle_notMem]
  rintro ⟨-, hall⟩
  exact hall c hc hmem

omit [DecidableEq α] [Fintype α] in
/-- The two composed: a cycle through the turn-edge gives the path. -/
theorem reachable_delete_of_cycle (x : α) {u : α} (c : (graph D).Walk u u)
    (hc : c.IsCycle) (hmem : s(x, D.t x) ∈ c.edges) :
    ((graph D).deleteEdges {s(x, D.t x)}).Reachable x (D.t x) :=
  reachable_delete_of_not_bridge D x (not_bridge_of_cycle D x c hc hmem)

/-! ### What the cycle construction needs, and the structure it rests on

The remaining obligation is one cycle through a turn-edge.  An attempt to build it
by iterating the alternating step ran into dependent-type plumbing rather than
mathematics, so what the attempt established is recorded here instead of a broken
construction.

Write `sigma = t ∘ p`.  The alternating walk from `x` visits

    x,  p x,  sigma x,  p (sigma x),  sigma² x,  …

so its vertices are the `sigma`-orbit of `x` together with the `p`-images of that
orbit.  Those are two `sigma`-cycles, which is exactly why the structured
measurement found `cycles(sigma) = 2 * walks`.

The turn-edge at `x` closes it: `t x = sigma (p x)`, so `t x` lies in the *other*
`sigma`-cycle and is reached last, immediately before the walk returns to `x` along
the very edge that gets deleted.  Deleting it therefore leaves a path from `x` to
`t x`, which is the merge hypothesis.

To finish, one needs: the walk of length `2m` where `m` is the `sigma`-order of
`x`; that it is closed, from `sigma^[m] x = x`; and that it is a cycle, which is
where `SimpleGraph.Walk.IsCycle` has to be discharged.  The first two are routine;
the third is the work.
-/

omit [DecidableEq α] [Fintype α] in
/-- The crossing-edge at an end. -/
theorem adj_cross (x : α) : (graph D).Adj x (D.p x) := Or.inl rfl

/-! ### Reachability after deleting a turn-edge

Working with `Reachable`, which is `Prop`-valued, avoids the dependent-type
difficulty of carrying a walk whose endpoint moves with the recursion. -/

/-- The alternating step. -/
def sig (x : α) : α := D.t (D.p x)

/-- `t x` is the crossing partner of `sig`-inverse of `x`: applying `sig` to
`p (t x)` returns `x`, which is what places `t x` at the far end of the walk. -/
theorem sig_p_t {β : Type*} (D : Data β) (x : β) : sig D (D.p (D.t x)) = x := by
  unfold sig
  rw [D.p_invol, D.t_invol]

omit [DecidableEq α] [Fintype α] in
/-- In the graph with one turn-edge removed, a crossing-edge is still available. -/
theorem reach_cross (e : Sym2 α) (x : α) (h : s(x, D.p x) ≠ e) :
    ((graph D).deleteEdges {e}).Reachable x (D.p x) :=
  SimpleGraph.Adj.reachable (by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨adj_cross D x, by simpa using h⟩)

omit [DecidableEq α] [Fintype α] in
/-- And a turn-edge, provided it is not the removed one. -/
theorem reach_turn (e : Sym2 α) (x : α) (h : s(x, D.t x) ≠ e) :
    ((graph D).deleteEdges {e}).Reachable x (D.t x) :=
  SimpleGraph.Adj.reachable (by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨adj_turn D x, by simpa using h⟩)

omit [DecidableEq α] [Fintype α] in
/-- One alternating step is available whenever neither of its two edges is the
removed one. -/
theorem reach_sig_step (e : Sym2 α) (x : α)
    (h₁ : s(x, D.p x) ≠ e) (h₂ : s(D.p x, D.t (D.p x)) ≠ e) :
    ((graph D).deleteEdges {e}).Reachable x (sig D x) :=
  (reach_cross D e x h₁).trans (reach_turn D e (D.p x) h₂)

omit [DecidableEq α] [Fintype α] in
/-- **The alternating walk, as reachability.**  If no step uses the removed edge,
then every iterate of `sig` is reachable from the start. -/
theorem reach_sig_iterate (e : Sym2 α) (x : α)
    (h₁ : ∀ y, s(y, D.p y) ≠ e)
    (h₂ : ∀ y, s(D.p y, D.t (D.p y)) ≠ e) :
    ∀ n : ℕ, ((graph D).deleteEdges {e}).Reachable x ((sig D)^[n] x) := by
  intro n
  induction n generalizing x with
  | zero =>
      simp only [Function.iterate_zero_apply]
      exact SimpleGraph.Reachable.refl x
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact (reach_sig_step D e x (h₁ x) (h₂ x)).trans (ih (sig D x))

omit [DecidableEq α] [Fintype α] in
/-- **The usable form.**  `reach_sig_iterate` above is true but inapplicable to the
case the merge needs: its hypothesis `∀ y, s(p y, t (p y)) ≠ e` fails at `y = p x`
when `e` is the turn-edge at `x`, since `p (p x) = x`.  So the conditions are
restricted here to the orbit points the walk actually traverses. -/
theorem reach_sig_iterate' (e : Sym2 α) (x : α) : ∀ n : ℕ,
    (∀ k, k < n → s((sig D)^[k] x, D.p ((sig D)^[k] x)) ≠ e) →
    (∀ k, k < n → s(D.p ((sig D)^[k] x), D.t (D.p ((sig D)^[k] x))) ≠ e) →
    ((graph D).deleteEdges {e}).Reachable x ((sig D)^[n] x) := by
  intro n
  induction n generalizing x with
  | zero =>
      intro _ _
      simp only [Function.iterate_zero_apply]
      exact SimpleGraph.Reachable.refl x
  | succ m ih =>
      intro h₁ h₂
      rw [Function.iterate_succ_apply]
      refine (reach_sig_step D e x ?_ ?_).trans (ih (sig D x) ?_ ?_)
      · simpa using h₁ 0 (Nat.succ_pos m)
      · simpa using h₂ 0 (Nat.succ_pos m)
      · intro k hk
        have := h₁ (k + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this
      · intro k hk
        have := h₂ (k + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this

/-! ### Landing the endpoint -/

omit [DecidableEq α] [Fintype α] in
/-- The alternating map is injective, being a composite of two involutions. -/
theorem sig_injective : Function.Injective (sig D) := by
  intro a b h
  unfold sig at h
  have h1 := congrArg D.t h
  rw [D.t_invol, D.t_invol] at h1
  have h2 := congrArg D.p h1
  rwa [D.p_invol, D.p_invol] at h2

omit [DecidableEq α] [Fintype α] in
/-- A crossing-edge is never the turn-edge at `x`, since the two partners of an end
are distinct. -/
theorem cross_ne_turn (x y : α) : s(y, D.p y) ≠ s(x, D.t x) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact D.pt_ne x (h1 ▸ h2)
  · have : D.t x = D.p x := by
      have := congrArg D.p h2
      rw [D.p_invol] at this
      rw [← this, h1]
    exact D.pt_ne x this.symm

omit [DecidableEq α] [Fintype α] in
/-- `p (t x)` is the `sig`-predecessor of `x`. -/
theorem p_t_eq_iterate (x : α) (m : ℕ) (hm : (sig D)^[m] x = x) (hpos : 0 < m) :
    D.p (D.t x) = (sig D)^[m-1] x := by
  apply sig_injective D
  rw [sig_p_t D x]
  have : (sig D) ((sig D)^[m-1] x) = (sig D)^[m] x := by
    rw [← Function.iterate_succ_apply' (sig D) (m-1) x]
    congr 1
    omega
  rw [this, hm]

omit [DecidableEq α] [Fintype α] in
/-- **The path after deleting a turn-edge.**  With `m` the minimal period of `x`
under the alternating map, and `p x` outside the orbit of `x` (which is the
distinctness of the two `sig`-cycles making up a walk), deleting the turn-edge at
`x` leaves `x` reachable from `t x`.

This is `WalkMerge.conn_merge`'s hypothesis, obtained without constructing a cycle
or invoking `IsCycle`: the walk goes out along the orbit and lands on `t x` by one
final crossing-step, since `t x = p (sig^[m-1] x)`. -/
theorem reach_delete_turn (x : α) (m : ℕ)
    (hm : (sig D)^[m] x = x) (hpos : 0 < m)
    (hmin : ∀ j, 0 < j → j < m → (sig D)^[j] x ≠ x)
    (hnotorbit : ∀ k, k < m → (sig D)^[k] x ≠ D.p x) :
    ((graph D).deleteEdges {s(x, D.t x)}).Reachable x (D.t x) := by
  have hstep : ∀ k, k < m - 1 →
      s(D.p ((sig D)^[k] x), D.t (D.p ((sig D)^[k] x))) ≠ s(x, D.t x) := by
    intro k hk hcon
    rw [Sym2.eq_iff] at hcon
    rcases hcon with ⟨ha, _⟩ | ⟨ha, _⟩
    · have h' := congrArg D.p ha
      rw [D.p_invol] at h'
      exact hnotorbit k (by omega) h'
    · have hpt := congrArg D.p ha
      rw [D.p_invol] at hpt
      rw [p_t_eq_iterate D x m hm hpos] at hpt
      -- `sig^[k] x = sig^[m-1] x` with `k < m-1` contradicts minimality
      have hinj : Function.Injective ((sig D)^[k]) :=
        Function.Injective.iterate (sig_injective D) k
      have hsum : k + (m - 1 - k) = m - 1 := by omega
      have hkey : (sig D)^[m - 1 - k] x = x := by
        apply hinj
        rw [← Function.iterate_add_apply, hsum]
        exact hpt.symm
      exact hmin (m - 1 - k) (by omega) (by omega) hkey
  have hout := reach_sig_iterate' D s(x, D.t x) x (m - 1)
    (fun k _ => cross_ne_turn D x _) hstep
  have hland : ((graph D).deleteEdges {s(x, D.t x)}).Reachable
      ((sig D)^[m-1] x) (D.p ((sig D)^[m-1] x)) :=
    reach_cross D _ _ (cross_ne_turn D x _)
  have hend : D.p ((sig D)^[m-1] x) = D.t x := by
    rw [← p_t_eq_iterate D x m hm hpos, D.p_invol]
  exact hend ▸ hout.trans hland

/-! ### Bridging the two formulations

`WalkMerge` states connectivity as `Relation.ReflTransGen` of a step relation;
`WalkGraph` uses `SimpleGraph.Reachable`.  They agree, which lets the merge lemma
consume `reach_delete_turn`. -/

omit [DecidableEq α] [Fintype α] in
/-- A step of `WalkMerge` is an edge of the walk graph. -/
theorem step_adj {x y : α} (h : WalkMerge.Step D.p D.t x y) : (graph D).Adj x y := h

omit [DecidableEq α] [Fintype α] in
/-- Connectivity in the step sense implies reachability in the graph. -/
theorem reachable_of_conn {x y : α} (h : WalkMerge.Conn D.p D.t x y) :
    (graph D).Reachable x y := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl x
  | tail _ hstep ih => exact ih.trans (SimpleGraph.Adj.reachable (step_adj D hstep))

omit [DecidableEq α] [Fintype α] in
/-- And conversely: an edge of the graph is a step. -/
theorem conn_of_adj {x y : α} (h : (graph D).Adj x y) : WalkMerge.Conn D.p D.t x y :=
  WalkMerge.conn_of_step h

/-! ### The re-paired data

Re-pairing two arrivals at one site.  The new turn is again an involution, and the
conditions it needs are exactly the ones the site structure supplies: the four ends
are distinct, and no swapped pair coincides with a crossing partner, which holds
because the swap stays inside a site while the crossing map moves between the two
sites of an edge. -/

/-- The re-paired turn: `a` now points at `d'` and `a'` at `d`. -/
def swapT (t : α → α) (a d a' d' : α) : α → α := fun x =>
  if x = a then d' else if x = d' then a else
  if x = a' then d else if x = d then a' else t x

theorem swapT_invol {β : Type*} [DecidableEq β] {t : β → β} {a d a' d' : β}
    (ht : ∀ x, t (t x) = x) (hta : t a = d) (hta' : t a' = d')
    (hda : d ≠ a) (hd'a : d' ≠ a) (ha'a : a' ≠ a) (hd'd : d' ≠ d)
    (ha'd' : a' ≠ d') (hda' : d ≠ a') :
    ∀ x, swapT t a d a' d' (swapT t a d a' d' x) = x := by
  intro x
  by_cases h1 : x = a
  · subst h1; unfold swapT; split_ifs <;> simp_all
  by_cases h2 : x = d'
  · subst h2; unfold swapT; split_ifs <;> simp_all
  by_cases h3 : x = a'
  · subst h3; unfold swapT; split_ifs <;> simp_all
  by_cases h4 : x = d
  · subst h4; unfold swapT; split_ifs <;> simp_all
  -- `x` is none of the four; then neither is `t x`, so the turn acts as before
  have hx : t x ≠ a := fun hc => h4 (by rw [← hta, ← hc, ht])
  have hx2 : t x ≠ d := fun hc => h1 (by rw [← hta] at hc; rw [← ht x, hc, ht])
  have hx3 : t x ≠ a' := fun hc => h2 (by rw [← hta', ← hc, ht])
  have hx4 : t x ≠ d' := fun hc => h3 (by rw [← hta'] at hc; rw [← ht x, hc, ht])
  simp [swapT, h1, h2, h3, h4, hx, hx2, hx3, hx4, ht]

/-- The re-paired data, given that the new turn is fixed-point free and still never
agrees with the crossing map. -/
def swapData (D : Data α) (a d a' d' : α)
    (hinv : ∀ x, swapT D.t a d a' d' (swapT D.t a d a' d' x) = x)
    (hne : ∀ x, swapT D.t a d a' d' x ≠ x)
    (hpt : ∀ x, D.p x ≠ swapT D.t a d a' d' x) : Data α where
  p := D.p
  t := swapT D.t a d a' d'
  p_invol := D.p_invol
  t_invol := hinv
  p_ne := D.p_ne
  t_ne := hne
  pt_ne := hpt

omit [Fintype α] in
@[simp] theorem swapData_t (D : Data α) (a d a' d' : α) (h1 h2 h3) :
    (swapData D a d a' d' h1 h2 h3).t = swapT D.t a d a' d' := rfl

omit [Fintype α] in
@[simp] theorem swapData_p (D : Data α) (a d a' d' : α) (h1 h2 h3) :
    (swapData D a d a' d' h1 h2 h3).p = D.p := rfl

omit [Fintype α] in
/-- **The merging edge.**  In the re-paired data, `a` is adjacent to `d'`, which lay
in the other walk.  This is the edge that joins them. -/
theorem adj_merge (D : Data α) (a d a' d' : α) (h1 h2 h3) :
    (graph (swapData D a d a' d' h1 h2 h3)).Adj a d' := by
  refine Or.inr ?_
  simp [swapData, swapT]

omit [Fintype α] in
/-- **The surviving edges.**  Every edge of the original graph other than the two
turn-edges being re-paired is an edge of the re-paired graph: crossing-edges are
untouched, and a turn-edge at an end outside the four is unchanged because the new
turn agrees with the old there. -/
theorem le_swapData (D : Data α) (a d a' d' : α)
    (hd : D.t a = d) (hd' : D.t a' = d') (h1 h2 h3) :
    (graph D).deleteEdges {s(a, d), s(a', d')} ≤ graph (swapData D a d a' d' h1 h2 h3) := by
  intro u v huv
  rw [SimpleGraph.deleteEdges_adj] at huv
  obtain ⟨hadj, hnot⟩ := huv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
  rcases hadj with hc | ht
  · exact Or.inl hc
  · -- a turn-edge; it is unchanged unless `u` is one of the four
    refine Or.inr ?_
    subst ht
    show D.t u = swapT D.t a d a' d' u
    unfold swapT
    have hua : u ≠ a := by
      rintro rfl; exact hnot.1 (by rw [hd])
    have hua' : u ≠ a' := by
      rintro rfl; exact hnot.2 (by rw [hd'])
    have hud : u ≠ d := by
      intro hc
      apply hnot.1
      have htu : D.t u = a := by rw [hc, ← hd, D.t_invol]
      rw [htu, hc, Sym2.eq_swap]
    have hud' : u ≠ d' := by
      intro hc
      apply hnot.2
      have htu : D.t u = a' := by rw [hc, ← hd', D.t_invol]
      rw [htu, hc, Sym2.eq_swap]
    rw [if_neg hua, if_neg hud', if_neg hua', if_neg hud]

omit [Fintype α] in
/-- **The merge.**  Re-pairing two arrivals joins their walks: the merging edge
carries `a` to `d'`, and the surviving half of the second walk carries `d'` to `a'`,
transported into the re-paired graph by `le_swapData`.

The path hypothesis is over the graph with *both* re-paired turn-edges deleted.
`reach_delete_turn` supplies it with one deleted; the second deletion is harmless
because that edge lies in the other walk, which the path never enters.  That
containment is the one step not carried out here, so it appears as the hypothesis
rather than being assumed silently. -/
theorem merge_connects (D : Data α) (a d a' d' : α)
    (hd : D.t a = d) (hd' : D.t a' = d') (h1 h2 h3)
    (path : ((graph D).deleteEdges {s(a, d), s(a', d')}).Reachable d' a') :
    (graph (swapData D a d a' d' h1 h2 h3)).Reachable a a' :=
  (SimpleGraph.Adj.reachable (adj_merge D a d a' d' h1 h2 h3)).trans
    (path.mono (le_swapData D a d a' d' hd hd' h1 h2 h3))

/-! ### Deleting a set of edges

The merge needs both re-paired turn-edges gone at once, so the chain is restated
for a set. -/

omit [DecidableEq α] [Fintype α] in
theorem reach_cross_set (S : Set (Sym2 α)) (x : α) (h : s(x, D.p x) ∉ S) :
    ((graph D).deleteEdges S).Reachable x (D.p x) :=
  SimpleGraph.Adj.reachable (by
    rw [SimpleGraph.deleteEdges_adj]; exact ⟨adj_cross D x, h⟩)

omit [DecidableEq α] [Fintype α] in
theorem reach_turn_set (S : Set (Sym2 α)) (x : α) (h : s(x, D.t x) ∉ S) :
    ((graph D).deleteEdges S).Reachable x (D.t x) :=
  SimpleGraph.Adj.reachable (by
    rw [SimpleGraph.deleteEdges_adj]; exact ⟨adj_turn D x, h⟩)

omit [DecidableEq α] [Fintype α] in
theorem reach_sig_step_set (S : Set (Sym2 α)) (x : α)
    (h₁ : s(x, D.p x) ∉ S) (h₂ : s(D.p x, D.t (D.p x)) ∉ S) :
    ((graph D).deleteEdges S).Reachable x (sig D x) :=
  (reach_cross_set D S x h₁).trans (reach_turn_set D S (D.p x) h₂)

omit [DecidableEq α] [Fintype α] in
/-- The alternating walk with a whole set of edges removed. -/
theorem reach_sig_iterate_set (S : Set (Sym2 α)) (x : α) : ∀ n : ℕ,
    (∀ k, k < n → s((sig D)^[k] x, D.p ((sig D)^[k] x)) ∉ S) →
    (∀ k, k < n → s(D.p ((sig D)^[k] x), D.t (D.p ((sig D)^[k] x))) ∉ S) →
    ((graph D).deleteEdges S).Reachable x ((sig D)^[n] x) := by
  intro n
  induction n generalizing x with
  | zero =>
      intro _ _
      simp only [Function.iterate_zero_apply]
      exact SimpleGraph.Reachable.refl x
  | succ m ih =>
      intro h₁ h₂
      rw [Function.iterate_succ_apply]
      refine (reach_sig_step_set D S x ?_ ?_).trans (ih (sig D x) ?_ ?_)
      · simpa using h₁ 0 (Nat.succ_pos m)
      · simpa using h₂ 0 (Nat.succ_pos m)
      · intro k hk
        have := h₁ (k + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this
      · intro k hk
        have := h₂ (k + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this

omit [DecidableEq α] [Fintype α] in
/-- **The path, with a set of edges removed.**  The conditions are now explicit
non-membership statements along the orbit, so the set may contain the other walk's
re-paired turn-edge as well: that edge simply never occurs along this orbit. -/
theorem reach_delete_turn_set (S : Set (Sym2 α)) (x : α) (m : ℕ)
    (hm : (sig D)^[m] x = x) (hpos : 0 < m)
    (h₁ : ∀ k, k < m - 1 → s((sig D)^[k] x, D.p ((sig D)^[k] x)) ∉ S)
    (h₂ : ∀ k, k < m - 1 → s(D.p ((sig D)^[k] x), D.t (D.p ((sig D)^[k] x))) ∉ S)
    (hlast : s((sig D)^[m-1] x, D.p ((sig D)^[m-1] x)) ∉ S) :
    ((graph D).deleteEdges S).Reachable x (D.t x) := by
  have hout := reach_sig_iterate_set D S x (m - 1) h₁ h₂
  have hland := reach_cross_set D S ((sig D)^[m-1] x) hlast
  have hend : D.p ((sig D)^[m-1] x) = D.t x := by
    rw [← p_t_eq_iterate D x m hm hpos, D.p_invol]
  exact hend ▸ hout.trans hland

omit [Fintype α] in
/-- **The merge, with no path hypothesis.**  Re-pairing two arrivals joins their
walks, given only that the second walk's orbit avoids both re-paired turn-edges,
which is what the two arrivals lying in different walks provides. -/
theorem merge_connects_full (D : Data α) (a d a' d' : α)
    (hd : D.t a = d) (hd' : D.t a' = d') (h1 h2 h3)
    (m : ℕ) (hm : (sig D)^[m] d' = d') (hpos : 0 < m)
    (k₁ : ∀ k, k < m - 1 →
      s((sig D)^[k] d', D.p ((sig D)^[k] d')) ∉ ({s(a, d), s(a', d')} : Set (Sym2 α)))
    (k₂ : ∀ k, k < m - 1 →
      s(D.p ((sig D)^[k] d'), D.t (D.p ((sig D)^[k] d'))) ∉
        ({s(a, d), s(a', d')} : Set (Sym2 α)))
    (klast : s((sig D)^[m-1] d', D.p ((sig D)^[m-1] d')) ∉
      ({s(a, d), s(a', d')} : Set (Sym2 α)))
    (hda' : D.t d' = a') :
    (graph (swapData D a d a' d' h1 h2 h3)).Reachable a a' := by
  have path : ((graph D).deleteEdges {s(a, d), s(a', d')}).Reachable d' a' := by
    have := reach_delete_turn_set D {s(a, d), s(a', d')} d' m hm hpos k₁ k₂ klast
    rwa [hda'] at this
  exact merge_connects D a d a' d' hd hd' h1 h2 h3 path

/-! ### The walk count

A walk is a connected component of the walk graph, so the walk count is the number
of those.  The merge lowers it by one: the induced map on components is onto, and
it identifies the two walks being joined. -/

/-- The components form a finite type. -/
noncomputable instance compFintype (D : Data α) :
    Fintype (graph D).ConnectedComponent :=
  Fintype.ofFinite _

/-- The number of walks. -/
noncomputable def walkCount (D : Data α) : ℕ :=
  Fintype.card (graph D).ConnectedComponent

omit [DecidableEq α] in
/-- **The merge lowers the walk count.**  `hmono` says connectivity is not
destroyed, which the merge does not do since each walk is a cycle and loses only
one edge; `hsplit` and `hjoin` say the two arrivals were in different walks and are
now in one. -/
theorem walkCount_lt (D D' : Data α)
    (hmono : ∀ x y : α, (graph D).Reachable x y → (graph D').Reachable x y)
    (a a' : α)
    (hsplit : ¬ (graph D).Reachable a a')
    (hjoin : (graph D').Reachable a a') :
    walkCount D' < walkCount D := by
  classical
  -- the map on components induced by the identity on ends
  let f : (graph D).ConnectedComponent → (graph D').ConnectedComponent :=
    Quot.lift (fun v => (graph D').connectedComponentMk v)
      (fun v w h => SimpleGraph.ConnectedComponent.eq.mpr (hmono v w h))
  have hsurj : Function.Surjective f := by
    intro b
    induction b using Quot.inductionOn with
    | _ z => exact ⟨(graph D).connectedComponentMk z, rfl⟩
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    apply hsplit
    have : f ((graph D).connectedComponentMk a) = f ((graph D).connectedComponentMk a') :=
      SimpleGraph.ConnectedComponent.eq.mpr hjoin
    exact SimpleGraph.ConnectedComponent.eq.mp (hinj this)
  exact OrbitCount.card_lt_of_surjective_not_injective f hsurj hnotinj

/-! ### The re-paired turn stays inside its site

The two conditions `swapData` takes, that the new turn is fixed-point free and
never agrees with the crossing map, both follow from the swap staying inside one
site.  That is the fact recorded here, and it is what makes those conditions
available for an actual configuration rather than assumed. -/

/-- **The re-paired turn preserves sites**, given that the original does and the
four ends being re-paired lie at one site. -/
theorem swapT_site {β : Type*} [DecidableEq β] (site : β → ℤ) (t : β → β)
    (a d a' d' : β)
    (ht : ∀ x, site (t x) = site x)
    (hd : site d = site a) (ha' : site a' = site a) (hd' : site d' = site a) :
    ∀ x, site (swapT t a d a' d' x) = site x := by
  intro x
  unfold swapT
  by_cases h1 : x = a
  · subst h1; simp [hd']
  by_cases h2 : x = d'
  · subst h2; simp [h1, hd'.symm]
  by_cases h3 : x = a'
  · subst h3; simp [h1, h2, ha', hd]
  by_cases h4 : x = d
  · subst h4; simp [h1, h2, h3, hd, ha']
  simp [h1, h2, h3, h4, ht]

/-- Consequently the crossing map and the re-paired turn never agree, by the same
structural argument as before: one moves between sites and the other does not. -/
theorem partner_ne_swapT {β : Type*} [DecidableEq β] (site : β → ℤ) (p t : β → β)
    (a d a' d' : β)
    (hp : ∀ x, site (p x) ≠ site x)
    (ht : ∀ x, site (t x) = site x)
    (hd : site d = site a) (ha' : site a' = site a) (hd' : site d' = site a) :
    ∀ x, p x ≠ swapT t a d a' d' x :=
  TurnBuild.partner_ne_turn site p (swapT t a d a' d') hp
    (swapT_site site t a d a' d' ht hd ha' hd')

/-- **The re-paired turn is fixed-point free.**  On the four ends it moves, each is
sent to one of the others, and only two distinctness facts are needed for that;
away from them it is the original turn, which fixes nothing. -/
theorem swapT_ne {β : Type*} [DecidableEq β] (t : β → β) (a d a' d' : β)
    (ht : ∀ x, t x ≠ x) (hd'a : d' ≠ a) (hda' : d ≠ a') :
    ∀ x, swapT t a d a' d' x ≠ x := by
  intro x
  unfold swapT
  by_cases h1 : x = a
  · subst h1; rw [if_pos rfl]; exact hd'a
  by_cases h2 : x = d'
  · subst h2; rw [if_neg h1, if_pos rfl]; exact Ne.symm hd'a
  by_cases h3 : x = a'
  · subst h3; rw [if_neg h1, if_neg h2, if_pos rfl]; exact hda'
  by_cases h4 : x = d
  · subst h4; rw [if_neg h1, if_neg h2, if_neg h3, if_pos rfl]; exact Ne.symm hda'
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]; exact ht x

/-- **The re-pairing preserves the arrival/departure alternation.**  The new turn
sends each arrival to the *other* arrival's departure, so roles still alternate. -/
theorem swapT_arr {β : Type*} [DecidableEq β] (isArr : β → Bool) (t : β → β)
    (a d a' d' : β)
    (hflip : ∀ x, isArr (t x) = !isArr x)
    (hd : d = t a) (hd' : d' = t a')
    (ha : isArr a = true) (ha2 : isArr a' = true) :
    ∀ x, isArr (swapT t a d a' d' x) = !isArr x := by
  intro x
  unfold swapT
  by_cases h1 : x = a
  · subst h1; rw [if_pos rfl, hd', hflip, ha2, ha]
  by_cases h2 : x = d'
  · subst h2; rw [if_neg h1, if_pos rfl, ha, hd', hflip, ha2]; rfl
  by_cases h3 : x = a'
  · subst h3; rw [if_neg h1, if_neg h2, if_pos rfl, hd, hflip, ha, ha2]
  by_cases h4 : x = d
  · subst h4; rw [if_neg h1, if_neg h2, if_neg h3, if_pos rfl, ha2, hd, hflip, ha]; rfl
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  exact hflip x

/-! ### Desubdivision: collapsing two `p`-partnered extra points

Extending `α` by two points `u = inr false`, `v = inr true`, glued to *each other* by
`p` (`p u = v`) and to `α` by `t` (`t u`, `t v` land back in `α` -- forced, since `p u
= v` rules out `t u = v` via `pt_ne`, and `t_ne` rules out `t u = u`, leaving only the
two `α`-shaped branches of `Sum`), is exactly *subdividing* one edge of the smaller
graph into a path through two new degree-preserving points.  Subdividing an edge never
changes how many connected components a graph has (generic case), or changes it by
exactly one, when the edge being subdivided is a self-loop-to-be, i.e. when the two
real neighbours the subdivision attaches to were already `p`-partners of each other
(corner case).  This is the fact `Elt.dataOf`'s `Classical.choice`-derived turn needs,
proved once, generically, in the `Data` model itself -- with no hypothesis at all on
*which* involution `t` extends to past the two new points, since the argument only
ever uses where `t` sends `u` and `v`, never how it behaves anywhere else. -/

section ReachMap

variable {β γ : Type*} [DecidableEq β] [Fintype β] [DecidableEq γ] [Fintype γ]

omit [DecidableEq β] [Fintype β] [DecidableEq γ] [Fintype γ] in
/-- **Mapping reachability along a step function.**  If every `Db`-edge becomes a
`Dc`-reachable pair under `f`, every `Db`-reachable pair does too: induct on the walk,
using `hstep` at each edge and `Reachable.trans` to thread them together. -/
theorem reach_of_step (Db : Data β) (Dc : Data γ) (f : β → γ)
    (hstep : ∀ x y, Adj Db x y → (graph Dc).Reachable (f x) (f y)) :
    ∀ {x y}, (graph Db).Reachable x y → (graph Dc).Reachable (f x) (f y) := by
  rintro x y ⟨w⟩
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h w ih => exact (hstep _ _ h).trans ih

end ReachMap

section Desub

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `p` never carries a real point out of `α`: the only two points it could land on
outside `α` are already `p`'s images of `u` and `v`, and `p` is injective. -/
theorem desub_p_real (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (a : α) : ∃ a', D.p (Sum.inl a) = Sum.inl a' := by
  have hinj : Function.Injective D.p := Function.Involutive.injective D.p_invol
  have hvu : D.p (Sum.inr true) = Sum.inr false := by
    have h := D.p_invol (Sum.inr false); rwa [hpuv] at h
  rcases hD : D.p (Sum.inl a) with a' | b
  · exact ⟨a', rfl⟩
  · exfalso
    cases b with
    | false => exact Sum.inl_ne_inr (hinj (hD.trans hvu.symm))
    | true => exact Sum.inl_ne_inr (hinj (hD.trans hpuv.symm))

/-- **`u` and `v` always have real turn-partners.**  Neither `t u` nor `t v` can be
`u`, `v` or each other (`t_ne` and `pt_ne` rule those out), so -- there being nothing
else in `Bool` -- both land in `α`.  This is what makes `walkCount_desub` applicable to
*any* `Data (α ⊕ Bool)` with `p u = v`, without having to name `x0`, `x1` up front:
whatever `t` turns out to be (in particular, whatever
`TurnBuild.exists_involution_of_card_eq`'s `Classical.choice` picked), its two real
turn-partners exist and can be read off after the fact. -/
theorem desub_exists_x0x1 (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true) :
    ∃ x0 x1 : α, D.t (Sum.inr false) = Sum.inl x0 ∧ D.t (Sum.inr true) = Sum.inl x1 := by
  have hvu : D.p (Sum.inr true) = Sum.inr false := by
    have hh := D.p_invol (Sum.inr false); rwa [hpuv] at hh
  have h0 : D.t (Sum.inr false) ≠ Sum.inr false := D.t_ne _
  have h0' : D.t (Sum.inr false) ≠ Sum.inr true := fun h =>
    D.pt_ne (Sum.inr false) (hpuv.trans h.symm)
  have h1 : D.t (Sum.inr true) ≠ Sum.inr true := D.t_ne _
  have h1' : D.t (Sum.inr true) ≠ Sum.inr false := fun h =>
    D.pt_ne (Sum.inr true) (hvu.trans h.symm)
  obtain ⟨x0, hx0⟩ : ∃ x0, D.t (Sum.inr false) = Sum.inl x0 := by
    rcases hD0 : D.t (Sum.inr false) with x0 | b0
    · exact ⟨x0, rfl⟩
    · cases b0 with
      | false => exact absurd hD0 h0
      | true => exact absurd hD0 h0'
  obtain ⟨x1, hx1⟩ : ∃ x1, D.t (Sum.inr true) = Sum.inl x1 := by
    rcases hD1 : D.t (Sum.inr true) with x1 | b1
    · exact ⟨x1, rfl⟩
    · cases b1 with
      | false => exact absurd hD1 h1'
      | true => exact absurd hD1 h1
  exact ⟨x0, x1, hx0, hx1⟩

/-- The two real turn-partners of `u` and `v` are distinct: `t` is injective and
`u ≠ v`. -/
theorem desub_hx0x1 (D : Data (α ⊕ Bool)) (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1) :
    x0 ≠ x1 := by
  intro h
  have hinj : Function.Injective D.t := Function.Involutive.injective D.t_invol
  have heq : D.t (Sum.inr false) = D.t (Sum.inr true) := by rw [hx0, hx1, h]
  exact absurd (hinj heq) (by simp)

theorem desub_t_x0_eq (D : Data (α ⊕ Bool)) (x0 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) : D.t (Sum.inl x0) = Sum.inr false := by
  have h := D.t_invol (Sum.inr false); rwa [hx0] at h

theorem desub_t_x1_eq (D : Data (α ⊕ Bool)) (x1 : α)
    (hx1 : D.t (Sum.inr true) = Sum.inl x1) : D.t (Sum.inl x1) = Sum.inr true := by
  have h := D.t_invol (Sum.inr true); rwa [hx1] at h

/-- Away from `x0`/`x1`, `t` also never carries a real point out of `α`. -/
theorem desub_t_real (D : Data (α ⊕ Bool)) (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (a : α) (h1 : a ≠ x0) (h2 : a ≠ x1) :
    ∃ b, D.t (Sum.inl a) = Sum.inl b := by
  have hinj : Function.Injective D.t := Function.Involutive.injective D.t_invol
  rcases hD : D.t (Sum.inl a) with b | c
  · exact ⟨b, rfl⟩
  · exfalso
    cases c with
    | false => exact h1 (Sum.inl_injective (hinj (hD.trans (desub_t_x0_eq D x0 hx0).symm)))
    | true => exact h2 (Sum.inl_injective (hinj (hD.trans (desub_t_x1_eq D x1 hx1).symm)))

/-- **The desubdivided crossing map.**  `D.p` with the two virtual points forgotten;
well defined by `desub_p_real`. -/
noncomputable def desubP (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true) :
    α → α := fun a => (desub_p_real D hpuv a).choose

theorem desubP_spec (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (a : α) : D.p (Sum.inl a) = Sum.inl (desubP D hpuv a) :=
  (desub_p_real D hpuv a).choose_spec

/-- **The desubdivided turn.**  `D.t` with the two virtual points removed and their
outer real neighbours `x0`, `x1` wired directly to each other -- exactly
un-subdividing the length-3 path `x0 - u - v - x1` down to a single edge `x0 - x1`. -/
noncomputable def desubT (D : Data (α ⊕ Bool)) (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1) :
    α → α := fun a =>
  if _ : a = x0 then x1
  else if _ : a = x1 then x0
  else (desub_t_real D x0 x1 hx0 hx1 a ‹a ≠ x0› ‹a ≠ x1›).choose

theorem desubT_x0 (D : Data (α ⊕ Bool)) (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1) :
    desubT D x0 x1 hx0 hx1 x0 = x1 := by
  simp [desubT]

theorem desubT_x1 (D : Data (α ⊕ Bool)) (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1) :
    desubT D x0 x1 hx0 hx1 x1 = x0 := by
  have hxx : x0 ≠ x1 := desub_hx0x1 D x0 x1 hx0 hx1
  unfold desubT
  rw [dif_neg (Ne.symm hxx), dif_pos rfl]

theorem desubT_spec (D : Data (α ⊕ Bool)) (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (a : α) (h1 : a ≠ x0) (h2 : a ≠ x1) :
    D.t (Sum.inl a) = Sum.inl (desubT D x0 x1 hx0 hx1 a) := by
  unfold desubT
  rw [dif_neg h1, dif_neg h2]
  exact (desub_t_real D x0 x1 hx0 hx1 a h1 h2).choose_spec

theorem desubP_invol (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (a : α) : desubP D hpuv (desubP D hpuv a) = a := by
  have h1 := desubP_spec D hpuv a
  have h2 := desubP_spec D hpuv (desubP D hpuv a)
  have h3 := D.p_invol (Sum.inl a)
  rw [h1, h2] at h3
  exact Sum.inl_injective h3

theorem desubT_invol (D : Data (α ⊕ Bool)) (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (a : α) :
    desubT D x0 x1 hx0 hx1 (desubT D x0 x1 hx0 hx1 a) = a := by
  by_cases h1 : a = x0
  · rw [h1, desubT_x0 D x0 x1 hx0 hx1, desubT_x1 D x0 x1 hx0 hx1]
  by_cases h2 : a = x1
  · rw [h2, desubT_x1 D x0 x1 hx0 hx1, desubT_x0 D x0 x1 hx0 hx1]
  have hb := desubT_spec D x0 x1 hx0 hx1 a h1 h2
  have hbx0 : desubT D x0 x1 hx0 hx1 a ≠ x0 := by
    intro hcon
    have e1 : D.t (Sum.inl a) = Sum.inl x0 := hcon ▸ hb
    have e2 : D.t (D.t (Sum.inl a)) = D.t (Sum.inl x0) := congrArg D.t e1
    rw [D.t_invol (Sum.inl a), desub_t_x0_eq D x0 hx0] at e2
    exact Sum.inl_ne_inr e2
  have hbx1 : desubT D x0 x1 hx0 hx1 a ≠ x1 := by
    intro hcon
    have e1 : D.t (Sum.inl a) = Sum.inl x1 := hcon ▸ hb
    have e2 : D.t (D.t (Sum.inl a)) = D.t (Sum.inl x1) := congrArg D.t e1
    rw [D.t_invol (Sum.inl a), desub_t_x1_eq D x1 hx1] at e2
    exact Sum.inl_ne_inr e2
  have hbspec := desubT_spec D x0 x1 hx0 hx1 _ hbx0 hbx1
  have e4 : D.t (Sum.inl (desubT D x0 x1 hx0 hx1 a)) = Sum.inl a := by
    rw [← hb, D.t_invol (Sum.inl a)]
  rw [hbspec] at e4
  exact Sum.inl_injective e4

theorem desubP_ne (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (a : α) : desubP D hpuv a ≠ a := by
  intro hcon
  have h1 := desubP_spec D hpuv a
  rw [hcon] at h1
  exact D.p_ne (Sum.inl a) h1

theorem desubT_ne (D : Data (α ⊕ Bool)) (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (a : α) : desubT D x0 x1 hx0 hx1 a ≠ a := by
  by_cases h1 : a = x0
  · rw [h1, desubT_x0 D x0 x1 hx0 hx1]
    exact (desub_hx0x1 D x0 x1 hx0 hx1).symm
  by_cases h2 : a = x1
  · rw [h2, desubT_x1 D x0 x1 hx0 hx1]
    exact desub_hx0x1 D x0 x1 hx0 hx1
  intro hcon
  have hb := desubT_spec D x0 x1 hx0 hx1 a h1 h2
  rw [hcon] at hb
  exact D.t_ne (Sum.inl a) hb

theorem desub_pt_ne (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (hne : desubP D hpuv x0 ≠ x1) (a : α) :
    desubP D hpuv a ≠ desubT D x0 x1 hx0 hx1 a := by
  by_cases h1 : a = x0
  · rw [h1, desubT_x0 D x0 x1 hx0 hx1]
    exact hne
  by_cases h2 : a = x1
  · rw [h2, desubT_x1 D x0 x1 hx0 hx1]
    intro hcon
    have h3 : desubP D hpuv (desubP D hpuv x1) = desubP D hpuv x0 :=
      congrArg (desubP D hpuv) hcon
    rw [desubP_invol D hpuv] at h3
    exact hne h3.symm
  intro hcon
  have hpspec := desubP_spec D hpuv a
  have htspec := desubT_spec D x0 x1 hx0 hx1 a h1 h2
  rw [hcon, ← htspec] at hpspec
  exact D.pt_ne (Sum.inl a) hpspec

/-- **The desubdivided datum.**  A genuine `Data α`: the two virtual points are gone,
`p` is exactly the original crossing map restricted to `α`, and `t` is the original
turn restricted to `α`, except at the two points that used to look across at the
virtual points, which now look directly at each other.  Only defined in the *generic*
case `desubP D hpuv x0 ≠ x1`: if the two outer neighbours were already `p`-partners,
wiring them together directly would repeat an edge (`pt_ne` would fail), and the
corner case needs the different treatment recorded in the block that formalizes this
lemma. -/
noncomputable def desubData (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (hne : desubP D hpuv x0 ≠ x1) : Data α where
  p := desubP D hpuv
  t := desubT D x0 x1 hx0 hx1
  p_invol := desubP_invol D hpuv
  t_invol := desubT_invol D x0 x1 hx0 hx1
  p_ne := desubP_ne D hpuv
  t_ne := desubT_ne D x0 x1 hx0 hx1
  pt_ne := desub_pt_ne D hpuv x0 x1 hx0 hx1 hne

/-- Collapse the two virtual points onto the real turn-partner each looks across at. -/
def rep (x0 x1 : α) : α ⊕ Bool → α
  | Sum.inl a => a
  | Sum.inr false => x0
  | Sum.inr true => x1

theorem desub_hstepI (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (hne : desubP D hpuv x0 ≠ x1) :
    ∀ x y : α ⊕ Bool, Adj D x y →
      (graph (desubData D hpuv x0 x1 hx0 hx1 hne)).Reachable
        (rep x0 x1 x) (rep x0 x1 y) := by
  intro x y hxy
  rcases hxy with rfl | rfl
  · rcases x with a | b
    · rw [desubP_spec D hpuv a]
      exact SimpleGraph.Adj.reachable (Or.inl rfl)
    · cases b with
      | false =>
        rw [hpuv]
        exact SimpleGraph.Adj.reachable
          (Or.inr (desubT_x0 D x0 x1 hx0 hx1).symm)
      | true =>
        have hvu : D.p (Sum.inr true) = Sum.inr false := by
          have h := D.p_invol (Sum.inr false); rwa [hpuv] at h
        rw [hvu]
        exact SimpleGraph.Adj.reachable
          (Or.inr (desubT_x1 D x0 x1 hx0 hx1).symm)
  · rcases x with a | b
    · by_cases h1 : a = x0
      · rw [h1, desub_t_x0_eq D x0 hx0]; exact SimpleGraph.Reachable.refl _
      by_cases h2 : a = x1
      · rw [h2, desub_t_x1_eq D x1 hx1]; exact SimpleGraph.Reachable.refl _
      · rw [desubT_spec D x0 x1 hx0 hx1 a h1 h2]
        exact SimpleGraph.Adj.reachable (Or.inr rfl)
    · cases b with
      | false => rw [hx0]; exact SimpleGraph.Reachable.refl _
      | true => rw [hx1]; exact SimpleGraph.Reachable.refl _

theorem desub_hstepII (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (hne : desubP D hpuv x0 ≠ x1) :
    ∀ a b : α, Adj (desubData D hpuv x0 x1 hx0 hx1 hne) a b →
      (graph D).Reachable (Sum.inl a : α ⊕ Bool) (Sum.inl b) := by
  intro a b hab
  rcases hab with rfl | rfl
  · show (graph D).Reachable (Sum.inl a) (Sum.inl (desubP D hpuv a))
    rw [← desubP_spec D hpuv a]
    exact SimpleGraph.Adj.reachable (Or.inl rfl)
  · show (graph D).Reachable (Sum.inl a) (Sum.inl (desubT D x0 x1 hx0 hx1 a))
    by_cases h1 : a = x0
    · rw [h1, desubT_x0 D x0 x1 hx0 hx1]
      have s1 : Adj D (Sum.inl x0) (Sum.inr false) := Or.inr (desub_t_x0_eq D x0 hx0).symm
      have s2 : Adj D (Sum.inr false : α ⊕ Bool) (Sum.inr true) := Or.inl hpuv.symm
      have s3 : Adj D (Sum.inr true : α ⊕ Bool) (Sum.inl x1) := Or.inr hx1.symm
      exact (SimpleGraph.Adj.reachable s1).trans
        ((SimpleGraph.Adj.reachable s2).trans (SimpleGraph.Adj.reachable s3))
    by_cases h2 : a = x1
    · rw [h2, desubT_x1 D x0 x1 hx0 hx1]
      have hvu : D.p (Sum.inr true) = Sum.inr false := by
        have h := D.p_invol (Sum.inr false); rwa [hpuv] at h
      have s1 : Adj D (Sum.inl x1) (Sum.inr true) := Or.inr (desub_t_x1_eq D x1 hx1).symm
      have s2 : Adj D (Sum.inr true : α ⊕ Bool) (Sum.inr false) := Or.inl hvu.symm
      have s3 : Adj D (Sum.inr false : α ⊕ Bool) (Sum.inl x0) := Or.inr hx0.symm
      exact (SimpleGraph.Adj.reachable s1).trans
        ((SimpleGraph.Adj.reachable s2).trans (SimpleGraph.Adj.reachable s3))
    · rw [← desubT_spec D x0 x1 hx0 hx1 a h1 h2]
      exact SimpleGraph.Adj.reachable (Or.inr rfl)

/-- **The desubdivision equivalence.**  Components of `D` correspond exactly to
components of `desubData D`, via collapsing the two virtual points onto their real
turn-partners one way, and the real embedding the other. -/
noncomputable def desubEquiv (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (hne : desubP D hpuv x0 ≠ x1) :
    (graph D).ConnectedComponent ≃
      (graph (desubData D hpuv x0 x1 hx0 hx1 hne)).ConnectedComponent where
  toFun := Quot.lift
    (fun x => (graph (desubData D hpuv x0 x1 hx0 hx1 hne)).connectedComponentMk
      (rep x0 x1 x))
    (fun x y h => SimpleGraph.ConnectedComponent.eq.mpr
      (reach_of_step D (desubData D hpuv x0 x1 hx0 hx1 hne) (rep x0 x1)
        (desub_hstepI D hpuv x0 x1 hx0 hx1 hne) h))
  invFun := Quot.lift
    (fun a => (graph D).connectedComponentMk (Sum.inl a))
    (fun a b h => SimpleGraph.ConnectedComponent.eq.mpr
      (reach_of_step (desubData D hpuv x0 x1 hx0 hx1 hne) D Sum.inl
        (desub_hstepII D hpuv x0 x1 hx0 hx1 hne) h))
  left_inv := by
    intro c
    induction c using Quot.inductionOn with
    | _ x =>
      show (graph D).connectedComponentMk (Sum.inl (rep x0 x1 x))
          = (graph D).connectedComponentMk x
      apply SimpleGraph.ConnectedComponent.eq.mpr
      apply SimpleGraph.Reachable.symm
      rcases x with a | b
      · exact SimpleGraph.Reachable.refl _
      · cases b with
        | false =>
          exact SimpleGraph.Adj.reachable
            (show Adj D (Sum.inr false) (Sum.inl x0) from Or.inr hx0.symm)
        | true =>
          exact SimpleGraph.Adj.reachable
            (show Adj D (Sum.inr true) (Sum.inl x1) from Or.inr hx1.symm)
  right_inv := by
    intro c
    induction c using Quot.inductionOn with
    | _ a => rfl

/-- **`walkCount` is unchanged by forgetting the two virtual points**, in the generic
case where their real turn-partners were not already `p`-partners of each other.  No
hypothesis at all is placed on *how* `t` behaves past `u`, `v` and `x0`, `x1` --
`TurnBuild.exists_involution_of_card_eq`'s `Classical.choice` can pick anything, and
the identity still holds, since the whole argument is that subdividing an edge never
changes the number of components. -/
theorem walkCount_desub (D : Data (α ⊕ Bool)) (hpuv : D.p (Sum.inr false) = Sum.inr true)
    (x0 x1 : α)
    (hx0 : D.t (Sum.inr false) = Sum.inl x0) (hx1 : D.t (Sum.inr true) = Sum.inl x1)
    (hne : desubP D hpuv x0 ≠ x1) :
    walkCount D = walkCount (desubData D hpuv x0 x1 hx0 hx1 hne) :=
  Fintype.card_congr (desubEquiv D hpuv x0 x1 hx0 hx1 hne)

end Desub

-- Certification (Rule 5).
#print axioms WalkGraph.swapT_arr
#print axioms WalkGraph.reach_of_step
#print axioms WalkGraph.desub_p_real
#print axioms WalkGraph.desub_exists_x0x1
#print axioms WalkGraph.desub_hx0x1
#print axioms WalkGraph.desub_t_real
#print axioms WalkGraph.desubP_spec
#print axioms WalkGraph.desubT_spec
#print axioms WalkGraph.desubP_invol
#print axioms WalkGraph.desubT_invol
#print axioms WalkGraph.desubP_ne
#print axioms WalkGraph.desubT_ne
#print axioms WalkGraph.desub_pt_ne
#print axioms WalkGraph.desub_hstepI
#print axioms WalkGraph.desub_hstepII
#print axioms WalkGraph.walkCount_desub
