# `zeta_probe/`: symbolic group model, word metric, and certificates

This directory holds the machinery behind the structural and analytic results on
the right-triangle reflection group, the generic group being virtually the
lamplighter `Z wr Z`. The structural half operates on the triangle-independent
symbolic normal form `(eps, delta, k, P)`: sign, mirror flag, rotation power, and
an integer Laurent polynomial `P` recording the lamp deposits, in which the shape
enters only through the rotation number `zeta_T = (a+bi)/(a-bi)`.

`route_b/` and `workflow_routes/` were exploration scratch and narration and are
no longer part of the release (`.gitignore`, research Rule 10). Every statement
they once carried is reproduced in full in the papers.


## Paper 1: the group model, the metric and universality

| File | What it is |
|---|---|
| `lamp_profile.py` | The word-metric solver. Connectivity-aware geodesic dynamic program; computes the word length of any group element. Self-checks against BFS with zero mismatches to radius 14. `python3 lamp_profile.py 14`. |
| `witness.py` | The explicit kernel witnesses `w_T`, conjugated glide-reflection squares, that refute all-depths universality. Exact `Q(i)` arithmetic. |
| `certify.py` | Uniform-in-`T` universality certificate: `u_d^T = u_d` for all unequal-leg triangles through depth 30. `python3 certify.py 30`. |
| `certify38_rust/` | The Rust certificate at depth 38, crash-resumable, plus `ldist`, the meet-in-the-middle exact kernel shortest-vector length. |
| `fire_rust/` | Regenerates A396406 from the normal form and the metric formula with no BFS (`fire`, `verify`, `deep` modes). `cargo run --release -- fire 16`. |
| `exact_check.py` | Exact `Q(i)` verification of the collision pairs exported by `certify38_rust`. |
| `lamp_geo.py`, `lamp_formula.py` | The relaxed, connectivity-free metric and the first geodesic-length structure probes. |
| `fire.py` | Python prototype of the theory-only regeneration, superseded by `fire_rust/`. |
| `probe.py`, `probe2.py`, `probe3.py`, `probe4.py` | The early symbolic-group BFS and the arithmetic difference screen, the Gaussian-integer divisibility attack. |
| `route_c_height_family.py` | The height-graded family: `mu` for `sqrt 2` and `phi`, the `L_1`/Mahler-measure sandwich, and the degree-2 deviation-depth law. |
| `series_tests.py` | Exact complexity tests on the 43 known terms: no constant-coefficient linear recurrence, no holonomic recurrence in the stated box, positive-control validated. |
| `algguess.py` | Exact search for an algebraic equation `P(x, F) = 0` satisfied by the growth series. |
| `wf2_relaxed_*.py`, `wf2_relaxed_README.md` | The relaxed-model counting dynamic program and the catalytic-kernel scaffold used for the growth-rate analysis. |


## Paper 2: the transcendence certificates

Each of these regenerates a numbered statement of `paper/journal/paper2.tex`.
The scripts that state a verdict run at two working precisions and disagreement
is treated as a bug.

| File | What it certifies |
|---|---|
| `blocks_growth.py` | The coefficient-growth hypothesis of `thm:blocks`, in exact integer arithmetic, by two independent routes: the `A/C` recursion and the q-trigonometric closed forms, agreeing to degree 1160. |
| `f2_pole_route.py` | The pole route to alternative (a) of `thm:blocks`, which excludes the rational branch for the denominators with no coefficient-growth hypothesis. |
| `qtrig_verify.py` | `prop:qtrig` and `rem:qtrig`: the sinh-form of `S_e` against the q-cosine, at generic `q`. |
| `qnumerator_certificate.py` | The numerator layer: `lem:qsinenum`, `lem:halfstep` and `prop:numnonvanish`, the last being the exact identity `Sigma_0 S_0 = 2q/(1-q)` at a travel pole. |
| `halfstep_verify.py` | The half-step functional equations for the q-cosine and q-sine. |
| `annulus_certificate.py` | Appendix `app:annulus`: `app:rep`, `app:euler`, `app:theta`, `app:M2` and `prop:selower`. |
| `m2_certificate.py` | The sharpness remark of `app:M2`. It is what showed that `M_2/w^4` does not converge, so the earlier constant `0.07` was a single-sample artifact; the load-bearing `M_2 <= 7 w^4` survives. |
| `star_gate_certificate.py` | The gate closure for `thm:U` and `app:star`, at 120-digit working precision with explicit truncation control. |
| `t2abs_smalltau.py` | The small-`tau` half of `lem:T2abs`, the range the verified enclosure does not cover, with explicit constants from Stirling and Binet. |
| `t2abs_certificate.py` | Adaptive-quadrature cross-check of `lem:T2abs`. **Superseded as the certificate** on 2026-08-15: the lemma is now proved by a verified enclosure of the same majorant, `tools/t2abs_iv`. Kept because it shares no code with the enclosure and so is an independent check. |
| `assembly_certificate.py` | The block-assembly inputs, by two independent arithmetic models. |
| `gaussint_verify.py` | The Hubbard-Stratonovich Gaussian-integral representation of `S_e` (`rem:gaussint`, `eq:HS`). |
| `cumulant_verify.py` | The cumulant chain at the tabulated travel poles. That route is closed and superseded; the script is kept as a check on the identities it verifies. |
| `budget.py`, `budget_iv.py` | The bound chain of the same closed route, the second in interval arithmetic. |

## paper_orthoscheme

| File | What it certifies |
|---|---|
| `orthoscheme_dichotomy.py` | Orthoscheme growth against the right-angled Coxeter envelope. |
| `orthoscheme_rigidity.py` | The two geometric facts under `thm:rigidity`, symbolically in the legs, so for all legs rather than at a sample. |
| `orthoscheme_universality.py` | The universality prefix in every dimension, of which the planar case is paper 1. |

## `tools/`

Rust and Python backends, one directory per tool, indexed in `tools/README.md`.
The certificates cited by name in the papers are `t2abs_iv` (verified enclosure
of the rectangle bound of `lem:T2abs`), `sitecost` (the site-cost law and the
gap-run cycle count of the transfer model), `ortho_len6` and `ortho_cd` (the
length-six kernel exclusion and the collision depth), `nodfinite` and `norec`
(the finite-horizon exclusion certificates and their Lean data), `u_modp_rust`
(the mod-`p` kernel census), `shape_arith`, `hexdist`, `paper4_ball12` and
`paper4_strata`.

## Build

```
cd <tool> && cargo build --release && ./target/release/<tool> ...
```

`target/` directories are regenerable and are not stored here.
