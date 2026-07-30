# Lean files for the triangle reflection paper

Checked with `lean <file>` on Lean 4.13; none of the three imports anything, so
no Mathlib build is required.

| file | proved | left open |
|---|---|---|
| `TriangleFlowMetric.lean` | the combinatorial core of both bounds of the metric theorem: per-edge domination and parity, doubling of connectors, the summation (`lower_bound`), vertex balance, and the length and flow of the word read off a circuit (`upper_bound`) | nothing; the graph inputs enter as hypotheses `hst` and the circuit |
| `EulerCircuit.lean` | the degree-counting core of Hierholzer: `trail_degree`, and `maximal_trail_closed`, that in a balanced multigraph a trail which cannot be extended is closed | `euler_circuit`, the splicing induction |
| `RotationRelations.lean` | the letter invariants of the rotation relations: the concatenation law by parity, and that reversal negates them on even-length words, which is the pairing the theorem uses | `count_normal_forms`, the `c^2` count, and the free-product torsion argument |

Every proved declaration has axioms `[propext, Quot.sound]` only. The two
`sorry`s are exactly the two statements named in the table; they are stated so
that their semantics are pinned, and nothing else depends on them.
