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
explicit hypothesis `hst`.  No imports: core Lean 4 only, so the file is
checked by `lean TriangleFlowMetric.lean` with no toolchain beyond Lean itself.
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

end TriangleFlow
