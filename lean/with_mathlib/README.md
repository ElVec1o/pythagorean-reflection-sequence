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

## Transcendence-paper atoms (Paper 2)

Two further files machine-check the delicate atoms of the transcendence proof
(`paper/journal/paper2.tex`). Both report axioms `[propext, Classical.choice,
Quot.sound]` only, with no `sorry`.

> **`AtomN.lean`** — the numerator amplitude atom ("Atom N"). Theorem
> `cross_term` proves the half-integer cross-term identity
> `j₃⁄₂·j₅⁄₂ + y₃⁄₂·y₅⁄₂ = 3/X³ + 2/X` from `sin²+cos²=1`; theorem
> `h_bounds` proves `1 ≤ h(X) ≤ 3/2` for all `X>0`, where the two-Bessel
> envelope coefficient is `h(X)=(1+3/2X²)/(1+1/X²)`. Together these make the
> numerator amplitude `1+O(τ)` with explicit constant `3/2` — no saddle, no
> turning-point analysis (`route_b/amplitude_bound.tex`, `lem:twobessel`).
>
> **`GaussHS.lean`** — the analytic backbone of the Hubbard–Stratonovich
> representation (`paper2.tex`, `rem:gaussint`, `eq:HS`). Theorem
> `gaussian_moment` proves
> `∫_ℝ e^{−u²/(4τ)} e^{iju} du = √(4πτ)·e^{−τj²}` (`τ>0`, `j∈ℝ`) from Mathlib's
> `GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I`. This is the exact
> identity that recasts the denominator block `S_e` as a real Gaussian integral
> with an *entire* amplitude, so its steepest-descent estimate rests on a
> classical stationary-phase theorem with trivial hypotheses rather than on the
> bounded-variation lemma `lem:Bbounded`.
>
> **`PolyaCarlson.lean`** — the coefficient-growth input to the *unconditional*
> block-transcendence theorem (`paper2.tex`, `thm:blocks`). The travel block Σ₁ is
> built as a truncated integer power series from its `A/C` recursion; theorem
> `coeff_bound` `native_decide`s the super-polynomial-growth-along-the-squares
> bound `2^{j+1} ≤ |[q^{(j+1)²}] Σ₁|` for `j = 0,…,9` (coefficients
> `2, −4, 14, −52, 178, −856, 4626, −27524, 150214, −816268`), which rules out the
> rational alternative in Pólya–Carlson and forces `|q|=1` to be a natural
> boundary. Axioms `[propext, Lean.ofReduceBool]`.
>
> **`SigmaKernel.lean`** — machine-checked non-automaticity evidence for the
> arithmetic route (`paper2.tex`, `sec:modp`). Σ₁ is built mod 3 (as `ZMod 3`
> coefficients from the same `A/C` recursion); theorem `kernel_full_tree`
> `native_decide`s that the 3-kernel through level 3 is the **full ternary tree** —
> all `1+3+9+27 = 40` decimation words of length ≤ 3 give pairwise-distinct
> sequences (compared on 18 terms), no collapses. So the 3-kernel has ≥ 40 elements
> (maximal growth), strong evidence that Σ₁ is not 3-automatic, hence transcendental
> over `𝔽₃(q)`. Axioms `[propext, Classical.choice, Lean.ofReduceBool, Quot.sound]`.
>
> **`UKernel.lean`** — the same certificate for the **actual** true series `u_n = A396406`
> (not just the block), now at **level 3**. It embeds `(u_n mod 3)` for `n ≤ 270` — the validated
> output of the polynomial-time engine `tools/u_modp_rust` (self-checked against the 43 known
> terms; byte-identical to the earlier validated `n ≤ 180` run on the overlap) — and
> `native_decide`s (theorem `u_kernel_full_tree`) that the 3-kernel through level 3 is the full
> ternary tree: all `1+3+9+27 = 40` decimation words of length ≤ 3 pairwise-distinct (comparison
> length 10; the tree is equally full at length 9). So `u_n`'s 3-kernel has ≥ 40 elements,
> deficit 0, no collapses — the earlier level-3 "deficit 1" at short prefixes was a
> comparison-length artifact, exactly as the sibling `SigmaKernel.lean` predicted.
>
> **`DiscreteConserved.lean`** — the two conserved quantities of the symmetric three-term
> recurrence `w(n+1) = bₙ·wₙ − w(n-1)` underlying the block-`S_e` amplitude analysis.
> `casoratian_const`: the discrete Casoratian `zₙ·z'(n-1) − z(n-1)·z'ₙ` of two solutions is
> constant (the exact pair-Casoratian `lem:pairC` that pins the `ν=±1/2` amplitude product).
> `energy_drift`: the discrete energy `E_n = z(n+1)²+zₙ²−bₙzₙz(n+1)` drifts by exactly
> `zₙz(n-1)(b(n-1)−bₙ)` (the envelope drift; zero for constant `b`). Both close by `ring` over
> any `CommRing`; axioms `[propext, Quot.sound]`.

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
