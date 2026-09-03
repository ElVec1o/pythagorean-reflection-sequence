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
| `lamp_profile.py` | The word-metric solver. Connectivity-aware geodesic dynamic program; computes the word length of any group element. Self-checks against BFS with zero mismatches to radius 14. `python3 lamp_profile.py 11` (160 s; the cost roughly doubles per radius, so radius 14 runs for tens of minutes). |
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

## 2026-09-03 — reproducibility audit of the paper-cited Python

Prompted by the same failure found in `tools/nogap`, where three cited scripts
referenced a `side.py` that no longer existed.  Scope here: every `.py` a
current paper cites.

**Existence.**  Every script cited by a shipping paper is present.  The one
dangling citation, `code/zeta_probe/orthoscheme_universality.py`, appears only
in `paper/old/universality_principle.tex`, an archived draft.

**A missing input, and the chain behind it.**  `elemY3_verify.py` and
`phase_match_verify.py` -- both cited -- read `poles.txt`, which was absent:
never committed, never in git history, and not gitignored.  It is produced by
`route_b/travel_poles_mp.py`, and `route_b/` is untracked (`.gitignore:77`).  So
the chain ran

    paper  ->  elemY3_verify.py  ->  poles.txt  ->  route_b/travel_poles_mp.py (untracked)

and broke at the third link.  Both scripts died with `FileNotFoundError` on a
clean checkout, and nothing caught it because nothing had re-run them.

Repaired by regenerating `poles.txt` (40 poles, `travel_poles_mp.py 40`) and
**tracking** it, since the generator is not tracked and the committed file is
therefore the only copy on a fresh clone.  Both scripts now run and reproduce
their constants:

    elemY3_verify.py       |Sum d_k|/tau^2.5 over m = 6,10,14,20,26:
                           0.267205, 0.266030, 0.265641, 0.265412, 0.265316
                           -> 3/(8 sqrt2) = 0.2651650
    phase_match_verify.py  dw/tau^1.5 -> 0.1768087 against sqrt2/8 = 0.1767767,
                           chi agreeing with its closed form to ~9 digits

The mathematics was right and the input file was missing -- the third instance
of that pattern, after paper4's cylinder scripts and `tools/nogap`.

**Clean otherwise.**  A static sweep for unresolved `open()` targets and local
imports over the tracked, paper-cited directories found nothing else.  The 200-odd
further hits are all inside `route_b/`, which is gitignored scratch and ships
with nothing.  `code/reproduce/certify_beta2_pole.py` runs and passes (winding 1
over 566 certified segments).

**Not covered.**  Whether each script's *output* still matches the number the
paper quotes was checked for the two repaired here and for
`certify_beta2_pole.py`, not for the rest of the cited set.
