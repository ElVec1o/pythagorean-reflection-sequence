# Lean files for the triangle reflection paper

Checked with `lean <file>` on Lean 4.13; none of the three imports anything, so
no Mathlib build is required.

| file | proved | left open |
|---|---|---|
| `TriangleFlowMetric.lean` | the combinatorial core of both bounds of the metric theorem: per-edge domination and parity, doubling of connectors, the summation (`lower_bound`), vertex balance, and the length and flow of the word read off a circuit (`upper_bound`) | nothing; the graph inputs enter as hypotheses `hst` and the circuit |
| `EulerCircuit.lean` | **Euler's theorem for finite directed multigraphs** (`euler_circuit`): a balanced multigraph whose edges are reachable from a base vertex carries a circuit using every edge once. Complete, no `sorry`. Mathlib has only the necessary degree condition, not this sufficiency | nothing |
| `RotationRelations.lean` | the letter invariants; block peeling and the two bounds; **the classification** (`classify_normal_forms`), **the converse** (`markBoth_valid`) and **the count** (`admissible_count`: `(n-1)^2` admissible index pairs, that is `c^2`). No `sorry` | the free-product torsion argument |

No file contains a `sorry`. Declarations in `TriangleFlowMetric.lean` and
`EulerCircuit.lean` have axioms `[propext, Quot.sound]`; the classification
theorems in `RotationRelations.lean` additionally use `Classical.choice`, the
third of Lean's standard axioms.

`euler_circuit` avoids decomposing the multigraph into connected components,
which is what makes the usual presentation heavy. The circuit is grown one
closed trail at a time: while some unused edge leaves a vertex of the current
circuit, a greedy walk from that vertex is closed (balance), is cut into the
circuit (`trail_split_at`, `splice`), and the induction proceeds on the number
of unused edges. When no unused edge leaves the circuit, connectivity forces
the remainder to be empty.
