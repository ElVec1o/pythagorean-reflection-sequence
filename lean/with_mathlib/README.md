# Symbolic verification (with Mathlib)

This is a **separate Lean project** that requires Mathlib.  It proves
that Relation #1 of Table 1 of the paper holds **symbolically over
ℚ(a, b)** — that is, for every right triangle with positive unequal
rational legs, not just on the concrete triangles checked in the
parent `RightTriangleReflection.lean` file.

This is the strongest machine-checked statement of the universality
phenomenon currently in the artifact:

> **`theorem rel1_symbolic`**: the two length-10 words
> `R_0 R_1 R_2 R_0 R_2 R_0 R_1 R_2 R_1 R_2` and
> `R_2 R_1 R_2 R_0 R_1 R_2 R_0 R_2 R_0 R_1`
> evaluate to the same element of `Aff(ℚ(a, b))`.

## Hardware requirements

- Disk: **~12 GB** (Mathlib cache, persistent)
- RAM: ~4 GB during `lake build`
- First-time install: ~30–60 minutes (mostly downloading and unpacking
  the prebuilt Mathlib cache)

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
