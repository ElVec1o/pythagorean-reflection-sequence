# Symbolic verification (with Mathlib)

This is a **separate Lean project** that requires Mathlib.  It proves
that **all eight relations of Table 1 of the paper hold symbolically
over ℚ(a, b)** — that is, simultaneously for every right triangle with
positive unequal rational legs, not just on the concrete triangles
checked in the parent `RightTriangleReflection.lean` file.

This is the strongest machine-checked statement of the universality
phenomenon currently in the artifact:

> **`theorem rel1_symbolic` through `rel8_symbolic`**: each pair of
> length-10 words in Table 1 evaluates to the same element of
> `Aff(ℚ(a, b))` for the affine isometry encoding described in the
> file.  Proved by the `ring` tactic over `MvPolynomial (Fin 2) ℚ`.

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
