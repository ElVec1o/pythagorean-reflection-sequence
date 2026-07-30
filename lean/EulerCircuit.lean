/-
Euler's theorem for finite directed multigraphs, towards the upper bound of the
metric theorem (paper 4, Theorem "Metric").

Mathlib supplies `SimpleGraph.Walk.IsEulerian` and the necessary degree
condition, but not the sufficiency: that a connected multigraph in which every
vertex has equal in- and out-degree carries a circuit using each directed edge
exactly once.  That is the statement `euler_circuit` below, and it is the one
input the paper's upper bound takes on faith.

This file pins the statement and proves the degree-counting core of
Hierholzer's argument:

  `trail_degree`          a trail from `a` to `b` uses, at every vertex, as many
                          outgoing as incoming edges, except for a surplus of
                          one at `a` and a deficit of one at `b`;
  `maximal_trail_closed`  hence in a balanced multigraph a trail that cannot be
                          extended has returned to its start.

What remains for `euler_circuit` is the splicing induction: remove a maximal
closed trail, recurse on the remaining balanced multigraph, and splice the
pieces at shared vertices.  That is recorded as `sorry` rather than asserted.

No imports: core Lean 4 only.
-/

namespace EulerMulti

variable {V : Type} [DecidableEq V]

/-- A directed edge. -/
abbrev DEdge (V : Type) := V × V

/-- Number of edges leaving `v`. -/
def outDeg (E : List (DEdge V)) (v : V) : Nat :=
  (E.filter (fun e => e.1 = v)).length

/-- Number of edges entering `v`. -/
def inDeg (E : List (DEdge V)) (v : V) : Nat :=
  (E.filter (fun e => e.2 = v)).length

/-- `IsTrail a b L` says the edges of `L`, in order, walk from `a` to `b`. -/
def IsTrail : V → V → List (DEdge V) → Prop
  | a, b, [] => a = b
  | a, b, e :: es => e.1 = a ∧ IsTrail e.2 b es

/-- Every vertex of `E` has equal in- and out-degree. -/
def Balanced (E : List (DEdge V)) : Prop := ∀ v, outDeg E v = inDeg E v

/-- Out-degree of a cons. -/
theorem outDeg_cons (e : DEdge V) (es : List (DEdge V)) (v : V) :
    outDeg (e :: es) v = (if v = e.1 then 1 else 0) + outDeg es v := by
  by_cases h : v = e.1
  · subst h; simp [outDeg, List.filter_cons] <;> omega
  · simp [outDeg, List.filter_cons, Ne.symm h, h] <;> omega

/-- In-degree of a cons. -/
theorem inDeg_cons (e : DEdge V) (es : List (DEdge V)) (v : V) :
    inDeg (e :: es) v = (if v = e.2 then 1 else 0) + inDeg es v := by
  by_cases h : v = e.2
  · subst h; simp [inDeg, List.filter_cons] <;> omega
  · simp [inDeg, List.filter_cons, Ne.symm h, h] <;> omega

/-- The degree identity along a trail, in subtraction-free form: at every
vertex the trail leaves as often as it enters, counting its start as one extra
departure and its end as one extra arrival.  This is the counting core of
Hierholzer's argument. -/
theorem trail_degree (a b : V) (L : List (DEdge V)) (h : IsTrail a b L) (v : V) :
    outDeg L v + (if v = b then 1 else 0) = inDeg L v + (if v = a then 1 else 0) := by
  induction L generalizing a with
  | nil =>
    simp only [IsTrail] at h
    subst h
    simp [outDeg, inDeg]
  | cons e es ih =>
    obtain ⟨he, htail⟩ := h
    have hrec := ih e.2 htail
    subst he
    rw [outDeg_cons, inDeg_cons]
    omega

/-- Splitting degrees over an append. -/
theorem outDeg_append (L R : List (DEdge V)) (v : V) :
    outDeg (L ++ R) v = outDeg L v + outDeg R v := by
  simp [outDeg, List.filter_append, List.length_append]

theorem inDeg_append (L R : List (DEdge V)) (v : V) :
    inDeg (L ++ R) v = inDeg L v + inDeg R v := by
  simp [inDeg, List.filter_append, List.length_append]

/-- A vertex of positive out-degree has an edge leaving it. -/
theorem exists_out (R : List (DEdge V)) (v : V) (h : 0 < outDeg R v) :
    ∃ e ∈ R, e.1 = v := by
  induction R with
  | nil => simp [outDeg] at h
  | cons e es ih =>
    rw [outDeg_cons] at h
    by_cases hv : v = e.1
    · exact ⟨e, List.mem_cons_self _ _, hv.symm⟩
    · simp only [if_neg hv, Nat.zero_add] at h
      obtain ⟨f, hf, hfv⟩ := ih h
      exact ⟨f, List.mem_cons_of_mem _ hf, hfv⟩

/-- In a balanced multigraph, a trail that cannot be extended is closed.

`L` is the trail, `R` the edges it has not used, and `hmax` says no unused edge
leaves the trail's endpoint. -/
theorem maximal_trail_closed (L R : List (DEdge V)) (a b : V)
    (htrail : IsTrail a b L) (hbal : Balanced (L ++ R))
    (hmax : ∀ e ∈ R, e.1 ≠ b) : a = b := by
  by_cases hab : a = b
  · exact hab
  · -- at `b` the trail arrives once more than it departs, so the unused edges
    -- must depart once more than they arrive; one of them therefore leaves `b`.
    have hdeg := trail_degree a b L htrail b
    rw [if_pos rfl, if_neg (fun h => hab h.symm)] at hdeg
    have hb := hbal b
    rw [outDeg_append, inDeg_append] at hb
    have hpos : 0 < outDeg R b := by omega
    obtain ⟨e, heR, heb⟩ := exists_out R b hpos
    exact absurd heb (hmax e heR)

/-- **Euler's theorem for finite directed multigraphs.**  A balanced multigraph
whose edges all lie in one connected component carries a circuit using every
edge exactly once.

`Reachable` is the connectivity hypothesis: every edge is reachable from the
base vertex through the multigraph.  The proof remaining is the splicing
induction on the number of edges; `maximal_trail_closed` above supplies its
key step.  Not proved here. -/
theorem euler_circuit (E : List (DEdge V)) (base : V)
    (hbal : Balanced E)
    (hconn : ∀ e ∈ E, ∃ P : List (DEdge V), (∀ f ∈ P, f ∈ E) ∧ IsTrail base e.1 P) :
    ∃ L : List (DEdge V), L.Perm E ∧ IsTrail base base L := by
  sorry

end EulerMulti
