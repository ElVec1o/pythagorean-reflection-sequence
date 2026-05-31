# Symbolic verification (with Mathlib)

This is a **separate Lean project** that requires Mathlib.  It proves
that **all eight relations of Table 1 of the paper hold symbolically
over ℚ(a, b)** — that is, simultaneously for every right triangle with
positive unequal rational legs, not just on the concrete triangles
checked in the parent `RightTriangleReflection.lean` file.

This is the strongest machine-checked statement of the universality
phenomenon currently in the artifact:

> **`SymbolicVerification.lean`**: `rel1_symbolic` through `rel8_symbolic`.
> Each pair of length-10 words in Table 1 evaluates to the same element
> of `Aff(ℚ(a, b))` for the affine isometry encoding described in the
> file.  Proved by the `ring` tactic over `MvPolynomial (Fin 2) ℚ`.
>
> **`SchurGeneral.lean`**: the four uniform polynomial identities
> `schur_base_step`, `schur_k2_step`, `schur_inductive_step`,
> `schur_boundary_step` that together capture the algebraic skeleton
> of the general-$n$ Schur-complement determinant identity
> $\det Q_n = -\prod_{i=1}^n a_i^2$.  All four are dispatched in
> milliseconds by the `ring` tactic.
>
> **`SymbolicUniversality.lean`**: canonical-Coxeter-word enumeration
> and Fibonacci-phase counts: $|\{$canonical length-$n$ words$\}| = F(n+3)$
> for $n = 0, \ldots, 10$, with the depth-10 count of 233 also proven.
> 11 theorems by `native_decide`.
>
> **`ComputableUniversality.lean`** (the main universality result):
> a hand-rolled computable bivariate polynomial type `CPoly` (no
> `MvPolynomial` dependency), a tracked-denominator affine isometry
> type `CAff`, and cumulative cross-multiplication dedup
> `dedupBy CAff.equivB`.  Together these give 13 machine-checked
> theorems:
>
> > `universal_layers_through_22 : allLayerCounts 22 = [1, 3, 5, 8, 13,
> > 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066, 3203, 4971,
> > 7574, 11543, 17683, 27108, 41067]`
> >
> > i.e. the BFS layer counts $a(0)..a(22)$ of OEIS A396406 are exactly
> > the universal sequence, for **every** right triangle with positive
> > unequal legs.
>
> The proof is a single `native_decide` performing one breadth-first
> sweep over canonical Coxeter words, deduplicating symbolic affine
> isometries over $\mathbb{Q}(a,b)$ by their numerators relative to the
> common denominator $(a^2+b^2)^{22}$ — hence holding simultaneously for
> all triangles, not any specific one.  Build time ~22 min on a Mac mini
> (M2, 24 GB).  Depth 22 matches the depth reached by the paper's
> independent multi-triangle verification.
>
> `slow_fast_agree_at_10`, `universality_at_depth_10`, `layer_10_eq_225`,
> and `layer_11_eq_351` are retained as cheaper cross-checks pinning the
> two equivalence notions (slow cross-multiplication vs. fast hashed
> common-denominator) together.

## Hardware requirements

- Disk: **~10 GB** (Mathlib cache, persistent)
- RAM: ~4 GB during `lake build`
- First-time install: ~15–45 minutes (mostly downloading and unpacking
  the prebuilt Mathlib cache)
- Subsequent rebuilds: ~40 seconds for the 8 symbolic theorems
- Lean toolchain: pinned to `leanprover/lean4:v4.20.0` via
  `lean-toolchain` (matches Mathlib `v4.20.0`)

## One-time install

From this directory:

```bash
lake update           # fetches the Mathlib source (~few minutes)
lake exe cache get    # downloads prebuilt Mathlib .olean files (~30 min)
lake build            # builds this file
```

After the first build, incremental rebuilds take seconds.

## Why is this a separate project?

The parent directory `../` contains a Mathlib-free Lean project that
builds in 20 seconds and machine-checks 62 theorems by `native_decide`
on concrete rational arithmetic.  That artifact is intentionally
lightweight so anyone can verify it on a fresh machine with no
heavyweight dependencies.

This subdirectory adds **one** stronger theorem at the cost of pulling
in Mathlib.  Both projects can live side by side; you only build this
one if you want the symbolic statement.
