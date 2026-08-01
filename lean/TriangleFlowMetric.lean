/-
Arithmetic core of the lower bound in the metric theorem for the translation
subgroup of a planar triangle reflection group (paper 4, Theorem "Metric").

The theorem states  ell(c) = ||phi(c)||_1 + 2 * st(c).  Its lower bound splits
into two halves:

  (a) graph-theoretic: the edges a closed walk traverses form a connected
      subgraph containing the base vertex, so the traversed edges carrying zero
      net flow already connect the support of the flow, whence their number is
      at least st(c);
  (b) arithmetic: on each edge the number of traversals dominates the net flow
      and has its parity, so an edge of zero net flow that is traversed at all
      is traversed at least twice, and summing over edges gives the bound.

Half (b) is formalized here in full; half (a) enters `lower_bound` as the
explicit hypothesis `hst`.  The second half of the file does the same for the
upper bound: the balance condition that makes the multigraph Eulerian, and the
length and flow of the word read off a circuit, are proved, while Euler's
theorem itself is the unformalized input.  No imports: core Lean 4 only, so
the file is checked by `lean TriangleFlowMetric.lean` with no toolchain beyond
Lean itself.
-/

namespace TriangleFlow

/-- The traversal record of one edge: (forward count, backward count). -/
abbrev Edge := Nat × Nat

/-- Total number of traversals of an edge, in either direction. -/
def traversals (e : Edge) : Nat := e.1 + e.2

/-- Net signed traversal count: the flow the edge carries. -/
def netFlow (e : Edge) : Int := (e.1 : Int) - (e.2 : Int)

/-- Contribution of an edge to the l1 norm of the flow. -/
def flowNorm (e : Edge) : Nat := (netFlow e).natAbs

/-- An edge traversed by the walk but carrying no net flow: a connector. -/
def isConnector (e : Edge) : Bool := netFlow e = 0 && 0 < traversals e

/-- Sum of a list of naturals. -/
def lsum : List Nat → Nat
  | [] => 0
  | x :: xs => x + lsum xs

/-- Number of steps of a walk: the traversals of its edges, summed. -/
def steps (es : List Edge) : Nat := lsum (es.map traversals)

/-- l1 norm of the flow of a walk. -/
def l1 (es : List Edge) : Nat := lsum (es.map flowNorm)

/-- Number of connectors of a walk. -/
def connectors : List Edge → Nat
  | [] => 0
  | e :: es => (if isConnector e then 1 else 0) + connectors es

/-- Traversals dominate the flow. -/
theorem flowNorm_le_traversals (e : Edge) : flowNorm e ≤ traversals e := by
  simp only [flowNorm, netFlow, traversals]
  omega

/-- Traversals and flow have the same parity. -/
theorem traversals_parity (e : Edge) : traversals e % 2 = flowNorm e % 2 := by
  simp only [flowNorm, netFlow, traversals]
  omega

/-- A connector carries no flow. -/
theorem connector_flowNorm (e : Edge) (h : isConnector e = true) : flowNorm e = 0 := by
  simp only [isConnector, netFlow, traversals, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [flowNorm, netFlow]
  omega

/-- A connector is traversed at least twice: it is traversed, and by parity its
traversal count is even. -/
theorem connector_two_le (e : Edge) (h : isConnector e = true) : 2 ≤ traversals e := by
  simp only [isConnector, netFlow, traversals, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [traversals]
  omega

/-- Summing over the edges of a walk: the number of steps is at least the l1
norm of the flow plus twice the number of connectors. -/
theorem steps_ge (es : List Edge) : l1 es + 2 * connectors es ≤ steps es := by
  induction es with
  | nil => simp [l1, steps, connectors, lsum]
  | cons e es ih =>
    simp only [l1, steps, connectors, List.map_cons, lsum] at *
    by_cases h : isConnector e = true
    · have h2 : 2 ≤ traversals e := connector_two_le e h
      have h0 : flowNorm e = 0 := connector_flowNorm e h
      simp only [h, if_true]
      omega
    · have hle : flowNorm e ≤ traversals e := flowNorm_le_traversals e
      simp only [h, if_false, Bool.false_eq_true]
      omega

/-- Lower bound of the metric theorem, arithmetic half.  `st` is the Steiner
number of the configuration; the hypothesis `hst` is the graph-theoretic half,
namely that the connectors of the walk already connect the support of the flow
together with the base vertex, so that there are at least `st` of them. -/
theorem lower_bound (es : List Edge) (st : Nat) (hst : st ≤ connectors es) :
    l1 es + 2 * st ≤ steps es := by
  have h := steps_ge es
  omega

/-- The number of steps has the parity of the l1 norm of the flow; with the
computation of that norm on the honeycomb this is why every translation has
even word length. -/
theorem steps_parity (es : List Edge) : steps es % 2 = l1 es % 2 := by
  induction es with
  | nil => simp [l1, steps, lsum]
  | cons e es ih =>
    have hp := traversals_parity e
    simp only [l1, steps, List.map_cons, lsum] at *
    omega

/-! ## The upper bound

The upper bound builds, from a flow `phi` and a connector set `M`, the directed
multigraph carrying `|phi_E|` copies of each support edge, directed by the sign
of the flow, and one copy of each direction of each connector.  Reading the
letters of an Eulerian circuit of that multigraph backwards yields a word whose
flow is `phi` and whose length is `||phi||_1 + 2|M|`.

Two of the three ingredients are formalized below: that every vertex of the
multigraph is balanced, which is what makes it Eulerian, and that the circuit
read off it has the stated length and flow.  The third, Euler's theorem itself
(a connected balanced multigraph admits a circuit using every directed edge
exactly once), is not formalized; Mathlib supplies `IsEulerian` and the
necessary degree condition but not this sufficiency. -/

/-- Positive part of a flow: the copies directed away from the vertex. -/
def posPart (z : Int) : Nat := z.toNat

/-- Negative part of a flow: the copies directed into the vertex. -/
def negPart (z : Int) : Nat := (-z).toNat

/-- Sum of a list of integers. -/
def lsumI : List Int → Int
  | [] => 0
  | x :: xs => x + lsumI xs

theorem posPart_sub_negPart (l : List Int) :
    (lsum (l.map posPart) : Int) - (lsum (l.map negPart) : Int) = lsumI l := by
  induction l with
  | nil => simp [lsum, lsumI]
  | cons x xs ih =>
    simp only [List.map_cons, lsum, lsumI, posPart, negPart] at *
    omega

/-- Out-degree of a vertex of the multigraph: one copy per unit of outgoing
flow, plus one per connector. -/
def outDeg (flows : List Int) (conn : Nat) : Nat := lsum (flows.map posPart) + conn

/-- In-degree, symmetrically. -/
def inDeg (flows : List Int) (conn : Nat) : Nat := lsum (flows.map negPart) + conn

/-- Every vertex of the multigraph is balanced.  This is exactly the cycle
condition: the signed flows at a vertex sum to zero. -/
theorem balanced (flows : List Int) (conn : Nat) (h : lsumI flows = 0) :
    outDeg flows conn = inDeg flows conn := by
  have := posPart_sub_negPart flows
  simp only [outDeg, inDeg]
  omega

/-- The traversal record an Eulerian circuit produces on one edge: the support
edges are traversed `|phi|` times in the direction of the flow, the connectors
once in each direction. -/
def realize (phi : Int) (conn : Bool) : Edge :=
  (posPart phi + (if conn then 1 else 0), negPart phi + (if conn then 1 else 0))

/-- The circuit realizes the prescribed flow. -/
theorem realize_flow (phi : Int) (conn : Bool) : netFlow (realize phi conn) = phi := by
  cases conn <;> simp only [realize, netFlow, posPart, negPart] <;> omega

/-- On one edge the circuit costs `|phi|` steps, plus two for a connector. -/
theorem realize_traversals (phi : Int) (conn : Bool) :
    traversals (realize phi conn) = phi.natAbs + 2 * (if conn then 1 else 0) := by
  cases conn <;> simp only [realize, traversals, posPart, negPart] <;> omega

/-- Number of connectors in a list. -/
def countConn : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countConn bs

/-- The word read off an Eulerian circuit has length `||phi||_1 + 2|M|`: the
upper bound of the metric theorem, given the circuit. -/
theorem upper_bound (phis : List Int) (conns : List Bool) :
    steps (List.zipWith realize phis conns)
      = lsum ((List.zipWith realize phis conns).map flowNorm)
        + 2 * countConn (conns.take phis.length) := by
  induction phis generalizing conns with
  | nil => cases conns <;> simp [steps, lsum, countConn, List.zipWith]
  | cons p ps ih =>
    cases conns with
    | nil => simp [steps, lsum, countConn, List.zipWith]
    | cons c cs =>
      have hr := realize_traversals p c
      have hf : flowNorm (realize p c) = p.natAbs := by
        simp only [flowNorm, realize_flow]
      have h := ih cs
      simp only [List.zipWith, steps, l1, List.map_cons, lsum, countConn,
        List.take, List.length_cons] at *
      omega

end TriangleFlow

-- Rule 5 axiom audit (added 2026-08-01): declare every axiom these results rest on.
#print axioms TriangleFlow.flowNorm_le_traversals
#print axioms TriangleFlow.traversals_parity
#print axioms TriangleFlow.connector_flowNorm
#print axioms TriangleFlow.connector_two_le
#print axioms TriangleFlow.steps_ge
#print axioms TriangleFlow.lower_bound
#print axioms TriangleFlow.steps_parity
#print axioms TriangleFlow.posPart_sub_negPart
#print axioms TriangleFlow.balanced
#print axioms TriangleFlow.realize_flow
#print axioms TriangleFlow.realize_traversals
#print axioms TriangleFlow.upper_bound
