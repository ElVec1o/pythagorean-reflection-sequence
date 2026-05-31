# Lean 4 machine-checked verification

This folder contains a Lean 4 file (`RightTriangleReflection.lean`) that
machine-verifies the eight length-10 affine relations driving OEIS
[A396406](https://oeis.org/A396406) on the canonical (3, 4, 5) right
triangle. All proofs are by `native_decide` over exact rational
arithmetic and run in seconds.

## What is verified

| | Statement | # theorems |
|---|---|---|
| 1 | Basic Coxeter relations $R_i^2 = 1$ for $i \in \{0, 1, 2\}$ and $(R_0 R_1)^2 = 1$ | 4 |
| 2 | All eight length-10 word-pair equalities (Table 1 of the manuscript) | 8 |
| 3 | The explicit affine matrix value of each of the eight relations (six half-turns and two pure translations) | 8 |
| 4 | Pairwise distinctness of the eight collision-pair affine matrices | 1 |
| 5 | Relation #1 also holds on the (5, 12, 13) right triangle (a concrete instance of universality) | 1 |
| 6 | Direct BFS computation of $a(0), a(1), \ldots, a(17)$, matching OEIS A396406 exactly through depth 17 | 18 |
| | **Total** | **40 machine-checked theorems** |

All proofs are by `native_decide`. The BFS computation in (6) performs an actual layer-by-layer breadth-first search of the Cayley orbit in exact rational arithmetic — this is a direct first-principles verification of the OEIS data through depth 17 (where $a(17) = 4971$).

## Requirements

- Disk: ~500 MB (Lean toolchain only — no Mathlib needed)
- RAM: ~1 GB peak
- Build time: ~20 seconds full clean build on a 2024 Mac mini (M2, 24 GB RAM)
  - Depths 0–12 build in under a second
  - Depths 13–15 add a few seconds each
  - Depth 17 takes the bulk of the time (~15 s)
- Lean: pinned to `leanprover/lean4:v4.13.0` via `lean-toolchain`

(Building deeper than depth 17 is possible but build time grows roughly geometrically — depth 18 would take a few minutes, depth 19+ rapidly becomes impractical.  The Rust BFS in `code/rust_bfs/` is the right tool for high-depth computation; Lean is the right tool for kernel-verified low-depth machine checking.)

## Install Lean (one-time, ~5 minutes)

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
source "$HOME/.elan/env"
lean --version    # should print "Lean (version 4.13.0, ...)"
```

## Build and check

From this directory:

```bash
lake build
```

A successful build means **all proofs check**. There is no separate
"run tests" step — Lean is its own checker.

If the build succeeds, you will see output like:

```
[1/1] Building RightTriangleReflection
```

with no `error:` lines. Any false claim in the file would have failed
the build with a concrete kernel-rejection message.

## File contents

- `RightTriangleReflection.lean` — the actual verification
- `lakefile.toml` — Lake build configuration
- `lean-toolchain` — pinned Lean version

## Why no Mathlib?

The verification is purely a finite rational-arithmetic check on the
canonical (3, 4, 5) right triangle. We import `Rat` from
`Lean.Data.Rat` (a module that ships with the Lean toolchain itself),
so no Mathlib dependency is needed. This keeps disk usage to ~500 MB
instead of ~12 GB and build time to seconds instead of an hour.

The structural Universality Theorem (the cyclic-ideal identification of
$\ker \rho_T$ over $\mathbb{Z}[Q]$) requires significantly more
infrastructure and is *not* formalized here — it would need Mathlib's
group-ring machinery and a substantial development. The present file
verifies the concrete computation at depths 0–17 on the (3, 4, 5)
triangle and at depth 10 on the (5, 12, 13) triangle.

## Reference

Bonfioli, V., *The Universal Right-Triangle Reflection Sequence
(Unequal Legs)*, 2026.
GitHub: <https://github.com/ElVec1o/pythagorean-reflection-sequence>
Zenodo DOI: [10.5281/zenodo.20370090](https://doi.org/10.5281/zenodo.20370090)
OEIS: [A396406](https://oeis.org/A396406)
