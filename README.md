# The Universal Right-Triangle Reflection Sequence

[![DOI](https://zenodo.org/badge/1235839920.svg)](https://doi.org/10.5281/zenodo.20370090)
[![OEIS A396406](https://img.shields.io/badge/OEIS-A396406-blue)](https://oeis.org/A396406)
[![OEIS A396927](https://img.shields.io/badge/OEIS-A396927-blue)](https://oeis.org/A396927)
[![Lean](https://img.shields.io/badge/Lean%204-checked-success)](./lean/)

Take any right triangle in the plane and reflect it repeatedly across its three
sides. Count the distinct images at each word-length: you get a sequence that
**begins identically for every triangle** — Fibonacci through depth 9, then a
characteristic deviation — and that we call the *universal right-triangle
reflection sequence* ([A396406](https://oeis.org/A396406)). This repository
contains the proof that the universality is **sharp**: it holds exactly through
depth 32 and then, for every algebraic shape, breaks.

**Sequence A396406** (offset 0; first 39 terms):

```
1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066,
3203, 4971, 7574, 11543, 17683, 27108, 41067, 62263, 94622, 143881,
217101, 327832, 495443, 749195, 1127236, 1697179, 2554961, 3848384,
5777651, 8679441, 13031206, 19574659, 29338781
```

For `1 ≤ n ≤ 9`, `u_n = F(n+3)` (Fibonacci); the first deviation is at `n = 10`,
`u_10 = 225 = F(13) − 8`. The **isosceles** case (`a = b`) is genuinely
different (`1, 3, 5, 8, 11, 13, 16, …`).

## Main results

1. **Sharp universality, then refutation.** For every right triangle with
   positive unequal rational legs, the orbit-growth sequence agrees with the
   common sequence `u_d` *through depth 32*, and this is **sharp**: the `(1,2)`
   triangle deviates at depth 33. The natural conjecture that the agreement
   persists at all depths is **false** — for every rational (indeed every
   *algebraic*) shape we construct an explicit nontrivial element of `ker ρ_T`,
   a conjugated product of glide-reflection squares, so each shape deviates at a
   first depth `n_T` with `max(33, c_T) ≤ n_T ≤ 24·c_T + 8`, linear in the
   arithmetic complexity `c_T` of the shape. The agreement through depth 30 is
   re-proved uniformly by an arithmetic certificate (Gauss's lemma + rank-0
   elliptic descent), and through depth 38 by a Rust certificate that also
   confirms the published terms `a(31)…a(38)` are the generic ones.

2. **Structure of the generic group.** The common sequence `u_d` is exactly the
   orbit growth of the *generic* right triangle — realized precisely by
   transcendental leg ratios. That generic group is **virtually the lamplighter
   `ℤ ≀ ℤ`**: amenable, of exponential growth, and *not finitely presentable*
   (which explains why Knuth–Bendix completion never terminates). Its
   translation lattice is computed exactly (`𝒯 = 2(t−1)ℤ[t^±]`, by a mod-2
   collapse of the two legs onto a single mirror), the kernel of every algebraic
   specialization is classified as a principal ideal, and the word metric is
   solved by an explicit lamplighter walk-and-deposit optimization.

3. **Closed-form `n`-dimensional growth rate.** The right-corner orthoscheme
   reflection group in ℝⁿ with pairwise distinct legs has asymptotic ratio
   `r_n = 1 + 2·cos(2π/(n+3))`.

4. **Class C unconditional faithfulness.** For pairwise distinct legs in every
   dimension `n ≥ 3`, the affine representation is faithful, via the uniform
   Schur-complement identity `det Q_n = −∏ a_i²` and rank-0 descent on the
   Cremona elliptic curves 24a1, 32a2, 72a2.

5. **The growth series.** `A396406` admits no constant-coefficient linear
   recurrence of order ≤ 21, no holonomic recurrence within
   `(order+1)(deg+1) ≤ 32`, and no algebraic equation with `deg_F ≤ 6`,
   `deg_x ≤ 14` (all exact, positive-control validated). Consistent with Parry's
   theorem on tour-cost wreath-product growth, the series is **conjecturally
   algebraic of high degree**; the asymptotic ratio is `β₂ = 1.4995 ± 0.001`
   (near, but not provably equal to, 3/2).

## Repository contents

| Path | Contents |
|---|---|
| `paper/paper.tex`, `paper.pdf` | **Main paper** (~22 pp): the sharp universality threshold and refutation, the virtually-`ℤ≀ℤ` structure, the metric formula, and the growth-series analysis. |
| `paper/paper_extra.tex`, `paper_ndim.tex` | Companion documents (conjectural material; the `n`-dimensional family). |
| `paper/OEIS/` | OEIS submission drafts and b-files; `paper/OEIS/submit/` holds paste-ready blocks for the `n`-dim family. |
| `code/zeta_probe/` | The core machinery: the symbolic group model, the word-metric solver (`lamp_profile.py`), the kernel witnesses (`witness.py`), and the arithmetic certificates (`certify.py`, `certify38_rust/`, `fire_rust/`). See `code/zeta_probe/README.md` for an index. |
| `code/rust_bfs/` | Disk-streaming exact-rational BFS (Rust); computes `u_d` to depth 42. |
| `code/mordell/`, `code/ideal/`, `code/g_modules/` | Sage rank-0 descent scripts, the cyclic-ideal check, and symbolic verification scripts. |
| `lean/`, `lean/with_mathlib/` | Lean 4 verification: the eight length-10 relations over ℚ(a,b), the Schur identity, and machine-checked universality **through depth 22**. |
| `reproduce/`, `data/` | Reproduction scripts and raw output. |
| `LICENSE.md`, `CITATION.cff` | License (text CC-BY-4.0 / code MIT) and citation metadata. |

## How to reproduce

Python 3.10+; Rust 1.70+ for the compiled components.

```bash
# Word-metric solver self-check (fast)
python3 code/zeta_probe/lamp_profile.py 14          # 0 mismatches vs BFS

# The theory regenerates A396406 from the metric formula, no BFS:
cd code/zeta_probe/fire_rust && cargo run --release -- fire 16

# Uniform universality certificate through depth 30 (~3 min):
python3 code/zeta_probe/certify.py 30

# Depth-38 certificate (Rust, ~3 min, validates a(31)..a(38)):
cd code/zeta_probe/certify38_rust && cargo run --release

# Full sequence to depth 42 (Rust):
cd code/rust_bfs && cargo build --release && ./target/release/*bfs* --depth 42
```

## OEIS status

| Sequence | What it counts | Status |
|---|---|---|
| [A396406](https://oeis.org/A396406) | 2D right triangle, unequal legs (the universal sequence) | **Published** |
| [A396927](https://oeis.org/A396927) | 5D orthoscheme, distinct legs | **Published** |
| `A_4D_classC`, `A_6D_classC`, `A_3D_classC` | 4D / 6D / 3D orthoschemes, distinct legs | Prepared (`paper/OEIS/submit/`) |
| `A_3D_classB` | 3D tetrahedron `(1,1,2)` | Prepared (no closed form) |
| 3D cube corner `(1,1,1)` | — | **Dropped** (duplicate of [A008137](https://oeis.org/A008137)) |

## Author

Vico Bonfioli (independent researcher). Contact via GitHub issues or the
corresponding-author address in the paper PDF.

## On the use of AI

This work was produced through extended human–AI collaboration. The mathematical
development was AI-led under human direction: the principal model was Anthropic's
Claude, cross-checked against other large language models in a multi-model,
adversarial review process. The AI derived and wrote the proofs and the paper
text, wrote the exact-rational BFS and Rust code, produced the SymPy/SageMath
symbolic and elliptic-curve (rank-0 descent) verifications, and carried out the
Lean 4 formalization. The author (an independent researcher, not a professional
mathematician) directed the investigation, ran the cross-checking, verified that
the computational artifacts run and reproduce, and is responsible for the final
text and any remaining errors. The Lean 4 certificates are provided precisely so
the central machine-verifiable claims need not rest on trust in either the human
or the AI contributors.

## License

- Text and papers: CC-BY-4.0.
- Code: MIT.
