# `zeta_probe/` — symbolic group model, word metric, and certificates

This directory holds the machinery behind the structural results on the
right-triangle reflection group (the "generic group" that is virtually the
lamplighter `ℤ ≀ ℤ`). Everything operates on the **triangle-independent symbolic
normal form** `(ε, δ, k, P)` — sign, mirror flag, rotation power, and an integer
Laurent polynomial `P` (the lamp deposits) — in which the shape enters only via
the rotation number `ζ_T = (a+bi)/(a−bi)`.

## Canonical (referenced by the paper)

| File | What it is |
|---|---|
| `lamp_profile.py` | **The word-metric solver.** Connectivity-aware ("plumber profile") geodesic DP; computes the exact word length of any group element. Self-checks against BFS with zero mismatches to radius 14. `python3 lamp_profile.py 14`. |
| `witness.py` | The explicit kernel witnesses `w_T` (conjugated glide-reflection squares) that refute all-depths universality; verified in exact ℚ(i) arithmetic. |
| `certify.py` | Uniform-in-T universality certificate (Python/NumPy) — proves `u_d^T = u_d` for all unequal-leg triangles through depth 30. |
| `certify38_rust/` | The Rust certificate: depth-38 version (crash-resumable), plus `ldist` (meet-in-the-middle exact kernel shortest-vector length). |
| `fire_rust/` | The "fire" engine: regenerates A396406 from the normal form × metric formula with **no BFS** (`fire`/`verify`/`deep` modes). `overnight.sh`, `night2.sh` are batch drivers. |

## Exact-arithmetic tools

| File | What it is |
|---|---|
| `series_tests.py` | Exact recurrence / holonomic / β₂ tests over the 43 known terms (positive-control validated on Fibonacci & Catalan). |
| `algguess.py` | Exact search for an algebraic equation `P(x,F)=0` of the growth series. |
| `exact_check.py` | Exact ℚ(i) verification of suspected collision pairs (used with `certify38_rust`). |

## Exploratory probes (the trail of the investigation)

| File | What it is |
|---|---|
| `probe.py`, `probe2.py`, `probe3.py`, `probe4.py` | Early symbolic-group BFS and the arithmetic difference-screen (the Gaussian-integer divisibility attack). |
| `lamp_geo.py`, `lamp_formula.py` | The relaxed (connectivity-free) metric and the first geodesic-length structure probes. |
| `fire.py` | Python prototype of the theory-only sequence regeneration (superseded by `fire_rust/`). |
| `wf2_relaxed_dp.py`, `wf2_relaxed_transfer.py`, `wf2_relaxed_README.md` | The relaxed-model counting DP and the catalytic-kernel scaffold (growth-rate analysis). |
| `route_b/` | The Route-B investigations: the deposit-family refutation of "bounded component count", the corrected per-component **strand** bound + 8-shape census, and the **catalytic functional equation** (`catalytic_*.py`, `funceq_build.py`, `route_b_funceq.tex`) — the q-difference structure showing the growth series is q-holonomic, not algebraic. (`shape_bound_lemma_SUPERSEDED.tex` records a flawed surgery proof; the correct excursion-parity proof is in the paper.) |
| `route_c_height_family.py` | The height-graded family: μ for √2 and φ, the L₁/Mahler-measure sandwich, and the degree-2 deviation-depth law. |
| `workflow_routes/` | Archived multi-agent workflow scripts and verdicts (`VERDICT.md`, `VERDICT2.md`): the rationality assault and the kernel/breakthrough round. |

## The arc, in one paragraph

The symbolic model (`probe.py`) reduces universality to a Diophantine question on
`ζ_T`; the arithmetic screen (`probe2–4.py`, `certify.py`, `certify38_rust/`)
proves universality uniformly through depth 38; the glide-square ideal
(`witness.py`) **refutes** it at all depths and yields the exact first-deviation
depth as a shortest-vector length; the lamplighter identification gives the word
metric (`lamp_profile.py`), which `fire_rust/` uses to regenerate the sequence
from pure theory; and the growth-series complexity (`series_tests.py`,
`algguess.py`, `route_b/`, `workflow_routes/`) places A396406 as conjecturally
algebraic of high degree. Full narrative: `workflow_routes/VERDICT2.md`.
