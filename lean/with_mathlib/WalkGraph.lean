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

-- Certification (Rule 5).
#print axioms WalkGraph.adj_symm
#print axioms WalkGraph.adj_irrefl
#print axioms WalkGraph.neighbor_eq
#print axioms WalkGraph.degree_eq_two
#print axioms WalkGraph.witness_degree

end WalkGraph
