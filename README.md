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

## Corpus status (v2.0.0 — consolidated)

Three companion papers in `paper/journal/`, every claim tiered honestly:

| paper | headline | status |
|---|---|---|
| **Paper 1** (44 pp) | metric theorem `ℓ_T = ℓ_R + 2c`; virtually-lamplighter structure; universality sharp at 32/33; deviation depth `n_T = K(T)/2` + closed-form law; `β₂ = 1.4916177871…` exact | **unconditional** (law's general exactness conjectural; certified at (1,2)) |
| **Paper 2** (14 pp) | blocks transcendental over ℚ(q); relaxed series `V` transcendental over ℚ(x); true series `U` transcendental **conditional on one amplitude estimate (⋆)**; `β₂`-as-a-number: reduced to a Hahn–Exton value question, with a proven no-go ledger (`ρ = 1/2`, cyclotomic floor `12/π² > 1`) locating the precise open frontier | **V unconditional; U conditional on (⋆); β₂ number-status open** |
| **Paper 3** (4 pp) | universality–deviation dichotomy (dimension-free); generic rigidity (co-null shape set); rational RACG envelope with rate `r_n = 1+2cos(2π/(n+3))`; geometric group = proper amenable quotient (finite-horizon envelope) | **theorems unconditional; higher-dim arithmetic past the horizon open** |

Machine-checked: Lean 4/Mathlib certificates in `lean/with_mathlib/` (no `sorry`);
Rust certificates to depth 42; ~40 reproduction scripts under `code/zeta_probe/`.

## Main results

1. **Sharp universality, then refutation.** For every right triangle with
   positive unequal rational legs, the orbit-growth sequence agrees with the
   common sequence `u_d` *through depth 32*, and this is **sharp**: the `(1,2)`
   triangle deviates at depth 33. The natural conjecture that the agreement
   persists at all depths is **false** — for every rational (indeed every
   *algebraic*) shape we construct an explicit nontrivial element of `ker ρ_T`,
   a conjugated product of glide-reflection squares, so each shape deviates at a
   first depth `n_T` with `max(33, c_T) ≤ n_T ≤ 24·c_T + 8`, linear in the
   arithmetic complexity `c_T` of the shape. More sharply, `n_T` equals exactly
   half the length of the shortest kernel element — a shortest-vector problem in
   the ideal `2(t−1)μ_T·ℤ[t^±]` under the lamplighter word metric — which is a
   decidable finite computation (`lem:finite-svp`, the travel bound), and yields
   a **closed-form three-regime law** `n_T = 6c+e`, `9c−3e`, or `3(c+e)`
   according to the triangle's angle (boundaries at `tan β = √(11/5)` and
   `β = 60°`, both machine-checked in `DeviationLattice.lean`): a theorem as an
   upper bound, certified at `(1,2)`, and matched by exhaustive search on
   thirteen shapes (sharp prediction: the `(3,4,5)` triangle first deviates at
   depth 164). The agreement through depth 30 is re-proved uniformly by an
   arithmetic certificate (Gauss's lemma + rank-0 elliptic descent), and through
   depth 38 by a Rust certificate that also confirms the published terms
   `a(31)…a(38)` are the generic ones.

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
   `deg_x ≤ 14` (all exact, positive-control validated). The lamplighter
   transfer yields an explicit **q-difference functional equation** (the
   catalytic variable enters by dilation `t → q²t`), so the kernel method
   does not apply. Unfolding the equation pins the asymptotic ratio
   **exactly**: **β₂ = 1.49161778…** (true growth rate, `= 1/√q*`,
   `Σ₁(q*)=1`). This is unconditional: the travel block carries the
   dominant singularity and is **connectivity-invariant** (every pure-travel
   run is a single Euler trail, so true length = relaxed length there), so
   the true series shares the relaxed travel denominator `1−Σ₁` verbatim and
   the squeeze `tₙ ≤ uₙ ≤ vₙ` pins the rate. This **excludes 3/2** — the
   earlier `≈1.4995` was a finite-depth overshoot. The relaxed series is
   **transcendental** (Theorem; modulo
   one explicit analytic lemma — the cosine asymptotic for `S_1` near
   `q=1`): the bulk and travel blocks each have infinitely many poles in
   (0,1) accumulating at q=1 — argument-principle pole counts inside
   `|q|≤R` diverge as 0, 1, 5, 46, 92 for R=0.50…0.95. **The constituent
   blocks `Σ₁,Σ₀,S₁,S₀` are transcendental _unconditionally_**: each is an
   integer power series of radius 1 and non-rational (super-polynomial
   diagonal `|c_{(j+1)(j+2)}| ≥ 2^{j+1}`; Hankel ≠ 0 thru order 11), so by
   **Pólya–Carlson** the unit circle is a natural boundary — no cosine lemma
   needed. (This does _not_ transfer to `V = Σ₀/(1−Σ₁)`: the boundary
   singularities cancel in the ratio, and `rad(V)≠1`, so `V`/`U` still need
   the lemma.) The lemma is now
   **reduced** (monotone-domination Abel identity, verified to 110 digits)
   to a single oscillatory-average bound `Σ μ_j R_j(w) = O(√τ)`, and its
   leading term is derived in **closed form** (bulk block):
   `S_1 = 1 − cos w − (17√2/36)·√τ·sin w + O(τ)`, the constant
   `−17√2/36 = −0.6678230711…` confirmed to 15 digits (the dominant **travel**
   block `Σ₁` has the analogous `+√2/36`). **Half of the bulk
   constant is unconditional and uniform**: the geometric-collapse split
   `E = T1 + T2` with `T1 = cos w − cos(w·e^{−τ/2})` (exact) obeys
   `|T1| ≤ √(τ/2)` for all τ with no hypothesis, isolating the whole gap in
   the structurally-smaller residue `T2`. Equivalently lem:cos reduces to
   one self-contained bound `sup_{[0,w]}|K'| ≤ Cτ` on an explicit entire
   function. That bound is a knife-edge — but **model subtraction dissolves
   it**: subtracting the closed-form geometric kernel
   `K'_model = −(1−e^{−τ})cos(u·e^{−τ/2})` leaves a residual with the
   knife-edge gone (`sup|corr|/τ → 1/6`), and the **exact resummation engine**
   `Σ_j j^p e^{−jτ}(−1)^j u^{2j}/(2j)! = (−∂_τ)^p cos(u·e^{−τ/2})` expands `K'`
   into closed-form layers; the crux layer `L₁` is rigorous (`sup|L₁| ≤
   τ/6 + …`; its fatal `W³sinW` term cancels to `O(τ³)`). The **tail
   cancellation** is captured exactly by a **Touchard/Poisson identity** —
   *not* a uniform constant (in fact `sup|D_p|/(w/2)^p ∼ 2^{−p}·Bell(p)`
   blows up): `D_p(W) = 2^{−p}Re[e^{iW}T_p(iW)]`, `T_p(w) = E[N^p]` for
   `N∼Poisson(w)`, so `Σ_p[j^p]Q·2^{−p}T_p(w) = E[Q(N/2)]`. With the **proved**
   R-control `0 ≤ Rⱼ ≤ τ²C(j)` (from `0 ≤ log(sinh(y/2)/(y/2)) ≤ y²/24` via
   Mittag–Leffler), this gives `Σ_{m≥2}sup|L_m| = O(τ)` and hence
   `sup|corr| ≤ 0.20τ` ⟹ `|T₂| = O(√τ)`, i.e. **lem:cos** (end-to-end check
   `sup|corr|/τ = 0.167` at τ=1e-4). **No open mathematical obstruction
   remains** — the only outstanding item is the symbol-for-symbol write-up of
   one elementary, numerically-corroborated assembly bridge (a Tonelli
   interchange + Chernoff tail). So `V` is transcendental *modulo a write-up
   step, not a math gap* — we don't stamp it unconditional until that's
   written out. *(An earlier "uniform `D_p` bound" route was found false and
   replaced by Touchard/Poisson — adversarial verification caught it.)* For the
   **true** series `U`: a multi-agent derivation (adversarially verified)
   showed `U` shares `V`'s travel denominator `1−Σ₁` *verbatim* (R1, Euler),
   so `U` inherits the same infinitely many poles accumulating at `q=1`, and
   `U`-transcendence reduces — conditionally on the same lemma — to a single
   numerator non-cancellation `N_U(q_m) ≠ 0`. This is strictly harder than
   `V`'s analog: no closed-form `N_U` is validated (the naive "+2-per-cycle"
   kernel miscounts `u_n` from `n=9`, where the defect is a distance-2
   *bridge* costing `+2j`, not a unit cycle) and positivity can't settle it.
   So `U`-transcendence stays **open** (≥1 of `U`, defect transcendental,
   rigorously); only the growth **rate** `β₂` is now pinned exactly.

> **Update (v1.2.0, June 2026) — current honest status.** The results above are
> consolidated, with full proofs, in the standalone
> [`code/zeta_probe/route_b/transcendence_paper.pdf`](code/zeta_probe/route_b/transcendence_paper.pdf).
> Net status:
> - **Blocks `Σ₁,Σ₀,S₁,S₀` — transcendental, unconditional** (Pólya–Carlson; no lemma).
> - **`V` — transcendental, modulo one closed-form lemma** (`lem:T2abs`, a clean
>   absolute-contour bound) plus Stirling. The lem:cos leading constant is now
>   derived in closed form, `√2/36 = (1/24)·∑ k³` (Euler–Maclaurin discretisation).
> - **`U` — transcendental, _conditional_ on a single turning-point
>   amplitude-normalisation estimate** `R = P₁₂ − E = O(τ^{5/2})`. The new
>   `amplitude_bound` section (Morita `q`-Bessel connection formula + a conserved
>   Casoratian envelope) **reduces** the gate to exactly this one bound; it is
>   numerically certain (`R/(τ^{5/2} sin w) → 1891√2/10368`, 21 digits, ~4×
>   margin) but **not proved**. We do **not** claim `U` proved.
> - **`mod p` evidence (unconditional):** `(uₙ mod p)` is maximally non-automatic
>   at `p = 3, 5`; proving non-automaticity for a single `p` would make `U`
>   transcendental unconditionally (Christol). This route is open.

> **Update (v1.3.0, June 2026).** The corpus is now split into publication-ready
> papers under `paper/journal/` (see `PAPER_PLAN.md`). **Paper 1 (`paper1.pdf`) is
> fully unconditional:** the metric theorem's lower bound, previously resting on a
> computational covering certificate, is now established by an explicit four-state
> transducer whose transition table is displayed and certified — bit-for-bit equal
> to the true connectivity defect on all 275,823 group elements through depth 24
> and on 200,000 further random profiles (`code/zeta_probe/route_b/fsm_verify.py`).
> Paper 1b (`paper1b.pdf`) collects the unconditional `n`-dimensional family; the
> transcendence study is now included as **Paper 2** (`paper2.pdf`), summarized in
> the next section. `U` remains conditional throughout.

> **Update (v1.7.0, July 2026) — honest status of the U-gate.** The numerator
> amplitude gate is **derived to leading order**: the amplitude series and the
> pole equation both collapse exactly to sinh-product families, their phase
> expansions share the identical `√τ` term (the universal curvature `c₃ = −τ²/9`,
> constant `√2/36`), and the pole–zero offset comes out exactly
> `δw = (√2/8)τ^{3/2}`, giving `|P₁₂|/τ^{3/2} → 1/(4√2) < 1/√2` (a fourfold
> margin, verified at the first 70 poles). This is the estimate `(⋆)`. Its
> **residual `O(τ)` term is verified numerically but not proved** — so
> **`U` is transcendental over ℚ(x) *conditional on* `(⋆)`**, on the same
> analytic footing as `V`. This is the single remaining gap, stated as such in
> `thm:U` and Remark `rem:Ugap`. See `paper2.pdf`; scripts `elemY3_verify.py`,
> `phase_match_verify.py`.

## Transcendence (Paper 2)

`paper2.pdf` (~10 pp) asks whether these growth series are algebraic or
transcendental, and reports the answer in **honest tiers**:

- **Building blocks — unconditional.** The catalytic q-series Σ₀, Σ₁, S₀, S₁ are
  transcendental over ℚ(q): integer coefficients, radius exactly 1, and
  super-polynomial growth along the squares (`|[q^{(j+1)²}]| ≥ 2^{j+1}`), so by
  Pólya–Carlson the unit circle is a natural boundary
  (`lean/with_mathlib/PolyaCarlson.lean`).
- **Relaxed series V — transcendental over ℚ(x).** Its one analytic input, a
  simple-saddle steepest-descent estimate, is proved *self-contained* (Cauchy +
  Stirling + Gaussian integration + an explicit bounded-variation bound; saddles
  `z* = ±iW/2`), not cited.
- **True series U = A396406 — transcendental over ℚ(x), *conditional on one
  explicit amplitude estimate* `(⋆)`.** Via the exact identity
  `P₁₂ = (2q³/(1−q³))·Σ dₖ`, the one remaining input — the numerator amplitude at
  the travel poles — is **derived to leading order in elementary closed form**:
  the terms collapse exactly to sinh-products, every expansion constant is an
  exact rational (`y* = (2/τ)e^{−τ−23τ²/36}`, `c₂ = −5τ²/12`, `c₃ = −τ²/9`,
  `c₅ = τ⁴/450`), and the phase-matching of the travel-pole equation (which
  collapses to the *same* sinh family) against the amplitude's zero gives the
  pole–zero offset `δw = (√2/8)·τ^{3/2}` exactly — hence
  `|P₁₂|/τ^{3/2} → 1/(4√2) < 1/√2`: the numerator gate, with a fourfold margin
  (verified at the first 70 poles). The √τ phases of pole and zero agree
  identically — both produced by the universal cubic curvature `c₃ = −τ²/9`,
  whose constant `√2/36` is the lem:cos constant — which is *why* the travel
  poles track the zeros of `Y₃(1)`. (`elemY3_verify.py`, `phase_match_verify.py`.)
  **Honest gap:** this establishes `(⋆)` to leading order and numerically at 70
  poles, but its `O(τ)` residual (the amplitude drift from turning point to pole)
  is **not proved**. So `U`'s transcendence is stated *conditional on `(⋆)`* —
  the single remaining gap — on the same simple-saddle footing as `V` otherwise;
  not formalized analysis.
- **Orthogonal mod-p evidence.** The p-kernel of `(u_n mod p)` is the full
  ternary tree through the accessible depth (`SigmaKernel.lean`, `UKernel.lean`)
  — maximal finite-data evidence of non-automaticity, not a proof.

Six Paper-2 atoms are machine-checked in `lean/with_mathlib/` (`GaussHS`,
`AtomN`, `PolyaCarlson`, `SigmaKernel`, `UKernel`, `DiscreteConserved`); the
numerical verification scripts are in `code/zeta_probe/route_b/`.

## Repository contents

| Path | Contents |
|---|---|
| `paper/journal/paper1.{tex,pdf}` | **Paper 1 (publication draft, ~41 pp)** — the planar A396406 result: word-length metric `ℓ_T=ℓ_R+2c` (now **fully unconditional**, the connectivity defect computed by an explicit finite-state transducer certified on 275,823 elements), sharp depth-32 effective universality, the virtually-`ℤ≀ℤ` structure, and the exact growth rate `β₂`. Journal-style, no process narration; targets the Journal of Integer Sequences. |
| `paper/journal/paper1b.{tex,pdf}` | **Paper 1b (publication draft, ~9 pp)** — the `n`-dimensional orthoscheme family: closed-form rate `r_n=1+2cos(2π/(n+3))`, unconditional Class C faithfulness via a uniform Gram determinant and rank-0 Mordell descent, the collision-depth invariant, and the OEIS Class C family. |
| `paper/journal/PAPER_PLAN.md` | The three-paper publication plan with the closed/open ledger and routes-to-finish. |
| `paper/paper.tex`, `paper.pdf` | Original combined manuscript (~22 pp): universality threshold, virtually-`ℤ≀ℤ` structure, metric formula, growth-series analysis. |
| `paper/paper_extra.tex`, `paper_ndim.tex` | Companion documents (conjectural material; the `n`-dimensional family). |
| `paper/OEIS/` | OEIS submission drafts and b-files; `paper/OEIS/submit/` holds paste-ready blocks for the `n`-dim family. |
| `code/zeta_probe/route_b/transcendence_paper.tex`, `.pdf` | **Standalone transcendence paper** (~58 pp): blocks transcendental unconditionally (Pólya–Carlson); `V` transcendental modulo one closed-form lemma; `U` transcendental conditional on one turning-point amplitude bound; `mod p` non-automaticity. With sections `lifting_U`, `metric_theorem`, `amplitude_bound`, `route_modp` and the assembled `bundle.pdf`. |
| `code/zeta_probe/tools/` | Consolidated verification suite: Rust high-precision tools (`u5b`, `u5b_gate`, `u_modp_rust`, `t1series`) and the Python checks in `verify_scripts/` (Casoratian, amplitude, q-Bessel, θ-Poisson, uniformity). See `tools/README.md`. |
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
| [A397437](https://oeis.org/A397437) | 4D orthoscheme, distinct legs | In review |
| [A397438](https://oeis.org/A397438) | 6D orthoscheme, distinct legs | In review |
| [A397439](https://oeis.org/A397439) | 3D orthoscheme, distinct legs | In review |
| `7D_classC` | 7D orthoscheme, distinct legs (growth `φ²`) | Prepared (`paper/OEIS/submit/`) |
| `3D_classB` | 3D tetrahedron `(1,1,2)` | Prepared (no closed form) |
| `V_relaxed`, `bulk_block` | relaxed companion of A396406; bulk catalytic block | Prepared (`paper/OEIS/submit/`) |
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
