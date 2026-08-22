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

theorem adj_symm {x y : α} (h : Adj D x y) : Adj D y x := by
  rcases h with rfl | rfl
  · exact Or.inl (D.p_invol x).symm
  · exact Or.inr (D.t_invol x).symm

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

/-- The turn-edge at `x` is an edge of the walk graph. -/
theorem adj_turn (x : α) : (graph D).Adj x (D.t x) := Or.inr rfl

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

/-- Equivalently, exhibiting a cycle through the turn-edge suffices.  This is the
form 2-regularity feeds: in a 2-regular graph every edge lies in a cycle, so no
edge is a bridge. -/
theorem not_bridge_of_cycle (x : α) {u : α} (c : (graph D).Walk u u)
    (hc : c.IsCycle) (hmem : s(x, D.t x) ∈ c.edges) :
    ¬ (graph D).IsBridge s(x, D.t x) := by
  rw [SimpleGraph.isBridge_iff_adj_and_forall_cycle_notMem]
  rintro ⟨-, hall⟩
  exact hall c hc hmem

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

/-- In the graph with one turn-edge removed, a crossing-edge is still available. -/
theorem reach_cross (e : Sym2 α) (x : α) (h : s(x, D.p x) ≠ e) :
    ((graph D).deleteEdges {e}).Reachable x (D.p x) :=
  SimpleGraph.Adj.reachable (by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨adj_cross D x, by simpa using h⟩)

/-- And a turn-edge, provided it is not the removed one. -/
theorem reach_turn (e : Sym2 α) (x : α) (h : s(x, D.t x) ≠ e) :
    ((graph D).deleteEdges {e}).Reachable x (D.t x) :=
  SimpleGraph.Adj.reachable (by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨adj_turn D x, by simpa using h⟩)

/-- One alternating step is available whenever neither of its two edges is the
removed one. -/
theorem reach_sig_step (e : Sym2 α) (x : α)
    (h₁ : s(x, D.p x) ≠ e) (h₂ : s(D.p x, D.t (D.p x)) ≠ e) :
    ((graph D).deleteEdges {e}).Reachable x (sig D x) :=
  (reach_cross D e x h₁).trans (reach_turn D e (D.p x) h₂)

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

-- Certification (Rule 5).
#print axioms WalkGraph.adj_symm
#print axioms WalkGraph.adj_irrefl
#print axioms WalkGraph.neighbor_eq
#print axioms WalkGraph.degree_eq_two
#print axioms WalkGraph.witness_degree
#print axioms WalkGraph.adj_turn
#print axioms WalkGraph.reachable_delete_of_not_bridge
#print axioms WalkGraph.not_bridge_of_cycle
#print axioms WalkGraph.reachable_delete_of_cycle
#print axioms WalkGraph.sig_p_t
#print axioms WalkGraph.reach_sig_step
#print axioms WalkGraph.reach_sig_iterate
#print axioms WalkGraph.reach_sig_iterate'

end WalkGraph
