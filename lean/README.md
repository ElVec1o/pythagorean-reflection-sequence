# Lean 4 formalisation

Two Lean 4 projects sit here.

| Directory | Toolchain | Targets | Mathlib |
|---|---|---|---|
| `lean/` (this one) | `leanprover/lean4:v4.13.0` | 6 | no |
| `lean/with_mathlib/` | `leanprover/lean4:v4.30.0` | 60 | yes |

Neither contains a `sorry`. Every target is registered both as a `[[lean_lib]]`
and in `defaultTargets`, so a clean `lake build` builds and checks all of them
and all are covered by the axiom audit.

Certification discipline: a file counts as checked only when a cold elaboration
exits 0, and the axiom list is read afterwards. An empty `#print axioms` line is
not evidence of success, since it also appears for a failed constant, and it is
the legitimate output for a `decide`-proved theorem. Grepping the log for
`error` is not a substitute for the exit status.

For the statement-to-declaration tables, and for the list of what is deliberately
not formalised and why, see the Lean sections of the papers themselves:
`paper1.tex` (`tab:lean-index`), `paper2.tex` (the site-cost index and the table
of blocked analytic atoms), `paper4.tex`, `paper_orthoscheme.tex` and
`hahn_exton_qcosine.tex`. Absence of a statement from those tables means there is
no certificate for it. `README_triangle.md` in this directory tabulates the files
backing paper 4 and the rotation-relation chain.


## This project (no Mathlib)

Six files, core Lean 4 only, `import Lean.Data.Rat` at most. Counted with
`grep -cE '^\s*(theorem|lemma)\s'`, they carry 152 declarations.

| File | Contents |
|---|---|
| `RightTriangleReflection.lean` | The eight length-10 affine relations driving A396406 on the canonical `(3,4,5)` triangle, the Coxeter relations `R_i^2 = 1` and `(R_0R_1)^2 = 1`, the explicit affine matrix of each relation and their pairwise distinctness, relation 1 on the `(5,12,13)` triangle, a first-principles layer-by-layer BFS of the Cayley orbit in exact rational arithmetic reproducing `a(0)..a(17)`, and the Fibonacci coincidence with its deficit-of-8 break at `n = 10`. `decide` and `native_decide`. |
| `EulerCircuit.lean` | Euler's theorem for finite directed multigraphs (`euler_circuit`): a balanced multigraph whose edges are reachable from a base vertex carries a circuit using every edge once. Mathlib has the necessary degree condition but not this sufficiency. This is the one input paper 4's metric upper bound otherwise takes on faith. |
| `TriangleFlowMetric.lean` | The arithmetic core of both bounds of paper 4's metric theorem: per-edge domination and parity, doubling of connectors, the summation (`lower_bound`), vertex balance, and the length and flow of the word read off a circuit (`upper_bound`). The graph-theoretic half of the lower bound enters as the hypothesis `hst`. |
| `RotationRelations.lean` | The letter invariants `c_i(w)`, block peeling and the two bounds, the classification `classify_normal_forms`, its converse `markBoth_valid`, and the count `admissible_count` (`(n-1)^2` admissible index pairs). The free-product torsion step is not here; it is `with_mathlib/CoxeterTorsion.lean`. This file is also compiled in place by the `with_mathlib` package through a `srcDir` entry, so there is exactly one copy of it. |
| `PaperExtraMod2.lean` | `prop:mod2-automaton` of paper 1's appendices: the mod-2 reduction of `u_d` is eventually 3-periodic with pre-period 1, is not purely periodic, and satisfies the order-2 Fibonacci recurrence from `d = 3` but not at `d = 2`. Kernel evaluation only, no `native_decide`. The closing step from eventual periodicity to algebraicity over `F_2(t)` is not formalised. |
| `PaperExtraCounts.lean` | The combinatorial and logical content of three of paper 1's appendix propositions, including the 52-pair search grid of `prop:no-dfinite` with the over-determination condition made explicit, and the arithmetic of the withdrawn nonlinear search in `prop:no-recurrence-strong` (ii). |

`RightTriangleReflection.lean` uses `native_decide` and so trusts the Lean
compiler in addition to the kernel; the other five do not.

### Requirements and build

- Disk: about 500 MB, the Lean toolchain only.
- RAM: about 1 GB peak.
- Build: about 20 seconds clean on a 2024 Mac mini (M2, 24 GB). Depths 0 to 12
  of the BFS build in under a second; depth 17 takes the bulk of the time.

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
source "$HOME/.elan/env"
cd lean && lake build
```

A successful build means the proofs check; Lean is its own checker. Building the
BFS deeper than depth 17 is possible but the cost grows roughly geometrically.
`code/rust_bfs/` is the tool for high-depth computation.

### Why no Mathlib here

These six files are finite rational and integer arithmetic plus self-contained
combinatorics. Keeping them Mathlib-free holds disk use to about 500 MB instead
of about 10 GB and build time to seconds. Anything needing real analysis, group
rings, `MvPolynomial`, free products or q-series lives in `with_mathlib/`.


## Reference

Bonfioli, V., the five papers in `paper/journal/`, 2026.
GitHub: <https://github.com/ElVec1o/pythagorean-reflection-sequence>
Zenodo: [10.5281/zenodo.20370090](https://doi.org/10.5281/zenodo.20370090)
OEIS: [A396406](https://oeis.org/A396406)
