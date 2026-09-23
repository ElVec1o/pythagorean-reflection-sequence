# The Universal Right-Triangle Reflection Sequence

[![DOI](https://zenodo.org/badge/1235839920.svg)](https://doi.org/10.5281/zenodo.20370090)
[![OEIS A396406](https://img.shields.io/badge/OEIS-A396406-blue)](https://oeis.org/A396406)
[![OEIS A396927](https://img.shields.io/badge/OEIS-A396927-blue)](https://oeis.org/A396927)

Take a right triangle in the plane with positive unequal legs and reflect it
repeatedly across its three sides. The number of distinct images at each word
length is the same sequence for every such triangle through depth 32, and this
is sharp: the `(1,2)` triangle deviates at depth 33. That common sequence is
OEIS [A396406](https://oeis.org/A396406). This repository holds the six papers,
the Lean 4 formalisation and the computational certificates behind its word
metric, its group-theoretic origin, its growth rate, and the arithmetic nature
of its generating function.

Author: Vico Bonfioli, independent researcher, `vicobonfioli@gmail.com`.


## The sequence

A396406, offset 0. The 43 terms held here are `code/data/u_terms_43.txt`:

```
1, 3, 5, 8, 13, 21, 34, 55, 89, 144, 225, 351, 554, 875, 1345, 2066,
3203, 4971, 7574, 11543, 17683, 27108, 41067, 62263, 94622, 143881,
217101, 327832, 495443, 749195, 1127236, 1697179, 2554961, 3848384,
5777651, 8679441, 13031206, 19574659, 29338781, 43997388, 65932461,
98849591, 147969934
```

For `1 <= n <= 9`, `u_n = F(n+3)` (Fibonacci); the first deviation is at
`n = 10`, where `u_10 = 225 = F(13) - 8`. The isosceles case `a = b` is a
different sequence, `1, 3, 5, 8, 11, 13, 16, ...`.

**Provenance of the last four terms.** `u_0 ... u_38` are the published terms.
`u_39 ... u_42` were recovered from stored double-precision logarithms of an
earlier run by exponentiating and rounding. The recovery reproduces all 39
published values exactly on the overlap, and every recovered value lies within
`9e-08` of an integer, so the rounding is unambiguous. The source log file is
not part of this release. Since then two of them have been checked: a modular
breadth-first search of the `(2,7)` triangle, whose group agrees with the
universal one through depth 52, returns `u_39 = 43997388` and
`u_40 = 65932461` as lower bounds (`rem:WT-numerics`(c) of `paper1.tex`,
`code/zeta_probe/wt_growth/`), a consistency check and not a certificate; and a
fresh run of the exploration-stage disk BFS, which does not ship, reproduces
`u_39` exactly. `u_41` and `u_42` are unchecked. The recovered terms are used
only by the finite-horizon exclusion searches (`prop:no-dfinite`,
`prop:no-recurrence-strong`, `prop:height-gap` in `paper1.tex`). The full note
is at the head of `code/data/u_terms_43.txt`.

`paper/OEIS/b396406.txt` is the b-file for `n = 0..38`;
`paper/OEIS/b396406_depth42.txt` extends it to `n = 42` and therefore carries
the four recovered terms.


## Repository layout

```
paper/
  journal/    the six release papers, .tex and .pdf
  OEIS/       b-files and the published-sequence index
lean/         Lean 4, Mathlib-free project (6 targets)
  with_mathlib/   Lean 4, Mathlib project (130 targets)
code/
  data/       u_terms_43.txt
  zeta_probe/     symbolic group model, word metric, certificates, Rust tools
    rj_certificates/  interval certificates for (R-J) and the pole count, model BFS (paper 2)
  rust_bfs/       disk-streaming exact-rational orbit BFS
  rust_christol_bfs/  mod-p kernel census
  triangle_relations/ shortest-relation and stratum scripts (paper 4)
  g_modules/, mordell/, ideal/   symbolic and rank-0 descent scripts
data/         raw JSON output consumed by the scripts
code/reproduce/  standalone reproduction scripts
```

`private/` is in `.gitignore` and never ships, as is
`code/zeta_probe/route_b/`, which is exploration scratch.


## The papers

All six are in `paper/journal/`, source and PDF.

| File | Pages | Title |
|---|---|---|
| `paper1` | 68 | The Universal Right-Triangle Reflection Sequence: a word-length metric, effective universality, and the lamplighter structure of A396406 |
| `paper2` | 102 | Transcendence of a planar reflection-group growth series and its relaxed companion |
| `paper4` | 34 | The shortest relations of planar triangle reflection groups |
| `paper_orthoscheme` | 32 | Universality for orthoscheme reflection groups: the right-angled Coxeter envelope and the collision depth |
| `merged_novel_paper` | 36 | Growth, collisions and lamplighter structure of generic triangle and orthoscheme reflection groups |
| `hahn_exton_qcosine` | 25 | Differential transcendence of the Hahn-Exton q-cosine and the arithmetic of its zeros |

The set was consolidated from seven documents on 2026-08-10. The former
supplement `paper_extra` is now Appendices C to K of `paper1`; the former
`paper1b` and `paper3` are merged into `paper_orthoscheme`. Superseded drafts
are kept locally in `paper/old/`, which does not ship.


## What is proved, and what is conditional

Claims below are stated at the strength the papers state them at. Where two
papers state the same fact at different strengths, the weaker is used here.

### Universality and its refutation (paper 1)

- `u_d^T` is independent of the shape `T` through depth 32, and this is sharp:
  the `(1,2)` triangle deviates at depth 33.
- The natural conjecture that universality holds at all depths is **false**.
  For every algebraic shape an explicit element of `ker rho_T` is exhibited, a
  product of conjugated glide-reflection squares, so each shape deviates at a
  first depth `n_T` with `max(33, c_T) <= n_T <= 24 c_T + 8`, linear in the
  arithmetic complexity `c_T`.
- `n_T` equals half the length of a shortest kernel element, a shortest-vector
  problem in the ideal `2(t-1) mu_T Z[t^{+-1}]` under the lamplighter metric.
  The closed-form three-regime law `n_T = 6c_T + e_T`, `9c_T - 3e_T` or
  `3(c_T + e_T)` is a theorem at `(1,2)` only; for the other twelve searched
  shapes it is an exhaustive-within-window verification against multipliers of
  bounded degree, and its exactness for all shapes is **conjectural**.

### Structure of the generic group (paper 1)

- The common sequence is the orbit growth of the generic right triangle,
  realised by transcendental leg ratios.
- The subgroup of `W` on which the linear part is a rotation is `Z wr Z` of
  index 4, so the generic group is virtually the lamplighter group. The
  translation lattice is computed exactly as `T = 2(t-1) Z[t^{+-1}]` by a
  Mayer-Vietoris/Crowell identification with a cyclic `Z[Q]`-ideal.
- The word metric: `l_T = l_R + 2c`, a relaxed length plus twice an explicit
  connectivity penalty. **Both bounds are proved**: with `l_R` and `c` the
  site-local closed forms, `wordLength = l_R + 2c` holds for every element
  (Lean theorem `metricAll`, via `PhiLipschitz.lean`). `conj:lowerbound` was
  verified with 0 exceptions on all 275,823 elements to depth 24 before it was
  proved; a previous version deduced it from a finite-state argument that was
  circular, retracted in `rem:lowerbound-open`. Still verified, not proved:
  that the closed form `l_R` is also the minimum over relaxed realisations.
- Growth rate `beta_2 = 1.4916177871...`, and `3/2` is excluded. Paper 1 proves
  this by squeezing `u_d` between the pure-travel subcount and the relaxed
  count. Paper 2's `cor:beta` records the dependency more finely: the lower
  bound `beta_2` for both `u_n` and `v_n` is free of the transfer model (M);
  identifying the rate of `v_n` with `beta_2` uses (M), now a theorem
  (`thm:model`); the same rate for `u_n` additionally uses (T), now
  `prop:travelinv`, and the positivity of the junction pairing at `q_1`.

### The rational triangle groups `W_T` (paper 1, Section 8)

- Structure (`prop:WT-structure`): the rotation subgroup is
  `Z[zeta_T^{+-1}] x| Z`, of index 4; `W_T` is dense in `Isom(R^2)`, solvable
  of derived length exactly 3, not finitely presented, and quasi-isometric to
  `R^2` times a horocyclic product of Bruhat-Tits trees (for `(1,2)`,
  `R^2 x DL(5,5)`).
- The stable norm on the translation lattice is round, `||v||_T = kappa_T |v|`
  (`prop:round-norm`), with explicit bounds on `kappa_T`
  (`kappa_(2,1) <= 12/5`); the exact value is open for every shape.
- Some translation has irrational stable norm, and its translation-length series
  has `|z| = 1` as a natural boundary (`thm:WT-R`, existential form). This says
  nothing about the growth series.
- The growth series `F_T` is not rational, algebraic or P-recursive in explicit
  low-complexity boxes, for every `T` at once (`thm:WT-lowcomplexity`,
  computer-assisted), and, given paper 2's `thm:nonDfinite`, only finitely many
  `T` admit such a relation of any fixed complexity (`thm:WT-blowup`). That
  `F_T` is not D-finite is **conjectural** (`conj:WT-nonDfinite`).
- New data (`rem:WT-numerics`): modular lower bounds for `u_d^(1,2)` to depth
  41 and for the `(1,3)` and `(2,7)` triangles, and exact spheres of two toy
  groups (`code/zeta_probe/wt_growth/`, `code/zeta_probe/zeta_toy_growth/`).

### Arithmetic of the growth series (paper 2)

`U` and `V` are the growth series of the universal group `W_univ`: `U` counts
by word length (`U = A396406`), and `V` counts by relaxed length. Three inputs
were carried as hypotheses by earlier versions. All three are now theorems:

- **(M)**, the strand-walk transfer model, is `thm:model`. The metric identity
  `wordLength = l_R + 2c` for every element (`metricAll`) and the faithfulness
  of the model to `W_univ` (`RJPhi.lean`) are formalised in Lean. The assembly
  step (M3'), in corrected form, has a hand proof in Appendix `app:M3prime` and
  is not formalised.
- **(T)**, invariance of the travel block, is `prop:travelinv`.
- **(R-J)**, the junction pairing, is `thm:RJ`. `<lambda,R>` has an exact
  closed form in `t_1` at `y = 1` and at `y = q`. It is positive at every
  travel pole: analytically, from the gate, for `tau_m <= 5e-3` (all
  `m >= 7`), and by MPFR interval certificate at `q_1, ..., q_12`
  (`code/zeta_probe/rj_certificates/`).

The results:

- **`thm:blocks` splits.** For each catalytic block `Sigma_0, Sigma_1, S_0, S_1`
  the Polya-Carlson dichotomy is **unconditional**: each is rational with poles
  at roots of unity, or has `|q| = 1` as a natural boundary and is
  transcendental over `Q(q)`. The exclusion of the rational alternative is
  unconditional for the two denominators `Sigma_1, S_1`, by a pole-path
  argument (`cor:polepath`). For the two numerators `Sigma_0, S_0` it rests on
  a coefficient-growth hypothesis that is verified by exact integer arithmetic
  out to degree 1156 and **not proved**; what the pole route reaches for them is
  only the joint statement that they are not both rational.
- **`thm:travelres` is unconditional.** The travel resolvent
  `Sigma_0/(1 - Sigma_1)` is transcendental over `Q(x)`. It uses no growth
  hypothesis, no asymptotic theorem and no statement about the model. Its one
  numerical input is `lem:T2abs`, of which it consumes only `|T_2(m pi)| < 1`
  against a computed worst value of 0.027; that bound is a verified enclosure
  over the parameter region, not a sampled one.
- **`thm:V` and `thm:U` carry no hypotheses.** `V` and `U` are transcendental
  over `Q(x)`. The proofs are computer-assisted in two finite ranges: the
  interval certificates for (R-J) at the first twelve poles, and the six poles
  above `tau = 5e-3` in the gate `thm:star`, checked at 120-digit precision. The
  hand proof of (M3') is the one unformalised combinatorial step. Only
  infinitely many poles are needed, and the analytic range supplies them, so
  the pole certificate is needed only for the statement "at every travel pole".
- **`thm:nonDfinite` and `thm:natboundary`.** `U` and `V` are not D-finite,
  even allowing coefficients holomorphic near the closed unit disc, so `u_n` and
  `v_n` are not P-recursive, and `|x| = 1` is a natural boundary of both
  (standing inputs `thm:model` and `thm:RJ`, both theorems). For the travel
  resolvent both statements are unconditional. The mechanism is the infinite
  pole set in the disc (`lem:mero`, `lem:odeposes`) and the Polya-Bertrandias
  theorem. The bivariate series `W(x,y)` is not D-finite either, and `U`, `V`
  satisfy no q-difference equation with `Q` not a root of unity and no Mahler
  equation (`sec:beyond`).
- **`thm:fredholm`.** The travel pole equation is a Fredholm determinant:
  `det(I - lambda T)` is the q-cosine `cos(sqrt(lambda) Z; q^2)`, a multiple of
  the Hahn-Exton function `J^(3)_{-1/2}`, so the travel poles are its zeros; the
  eigenvalues are simple, and infinitely many poles follow without the `T_2`
  input (`sec:fredholmdet`).
- The gate: the amplitude estimate `(star)` holds at every travel pole
  (`thm:star`), as does the denominator bound `|S_e| >= 0.63 sqrt(tau)`.
  `thm:L` gives the bulk dictionary and the finiteness of
  `B_0 = 1/(1 - g t_1)` at every travel pole. The false positivity claim that
  earlier versions attached to `thm:L`, and the identity `eq:liftident`, are
  removed.
- **Evidence for the assembly.** Earlier versions cited agreement "to `v_14`".
  That check was a sweep of the bridge `l_T = l_R + 2c`, not of the assembled
  blocks, and it is withdrawn. It is replaced by a breadth-first enumeration of
  `W_univ`: exact series agreement to `x^26` at `y = q` in all three sectors, and
  to `x^22` at `y = q^2`. At symbolic `y` all 816 coefficients with `l_T <= 31`
  agree (`5.03e6` elements), and a deliberately corrupted model is detected.
  `v_0 .. v_19` are certified.
- The site-cost law of the model is a theorem inside the crossing optimisation
  (`lem:transport`, `cor:localcost`), and its marker clause is corrected: the
  junction cost is `max(|d_L - 1|, |d_R|)`, not the `max(|d_L| - 1, |d_R|)`
  carried by earlier versions, which is false on every cell with `d_L <= -2`
  and `|d_R| <= |d_L|`. The shield law is half proved: `c >= |Z|` (`prop:cut`).
  The reverse inequality `c <= |Z|` is verified and not proved
  (`rem:shieldowes`). `thm:model` no longer needs it, because `metricAll`
  proves the metric identity directly. That the closed form `l_R` is also the
  minimum over relaxed realisations is paper 1's metric formula. It bears only
  on reading `V` as a relaxed count.
- Open: whether the **number** `beta_2` is transcendental.
- An orthogonal route via Christol's theorem, independent of all the above,
  would give a second proof for `U`. The `p`-kernel of `(u_n mod p)` is computed to be maximally
  non-automatic at `p = 3, 5` and machine-checked at `p = 3`; a proof for
  dense-support series is open.

### Shortest relations (paper 4)

- For every Euclidean triangle there are exactly 33 shortest relations, each
  equating two reduced words of length 11, and for all shapes outside a proper
  Zariski-closed set they are the only coincidences in the ball of radius 11.
  The associated growth sequence begins `1,3,6,12,24,48,96,192,384,768,1536,3039,6012`.
- The translation subgroup is identified with the finitely supported integer
  flows on the honeycomb Cayley graph of the point group `Z^2 x| C_2`, and outside countably many
  proper subvarieties the word length equals the `l^1` norm of the flow plus
  twice the least number of edges joining its support to the base vertex. **That
  length formula is not new**: it is the formula of Droms, Lewin and Servatius
  and of Myasnikov, Roman'kov, Ushakov and Vershik for the groups `F/N'`. What
  is established here is the identification placing `G_tau` in their setting,
  plus the difference caused by the generators being involutions.
- On the strata where one angle is `pi/m`, each divisor `d` of `m` with
  `2 <= d <= m/2` contributes `d^2 - 1` relations at depth `m + m/d`, which for
  even `m` gives `(m/2)^2 - 1` relations at depth `m + 2`.

### Orthoscheme reflection groups (paper_orthoscheme)

Four statements are proved unconditionally: a dimension-free quotient
dichotomy; rationality of the right-angled Coxeter envelope with growth rate
`r_n = 1 + 2 cos(2 pi/(n+3))`; that for `n >= 3` every kernel element of word
length 6 is `(R_i R_{i+1})^{+-3}` at a `pi/3` pair (`thm:len6`); and a complete
classification of the rank-two relations, whose Diophantine input is that three
quartics have only trivial rational points, their Jacobians being the rank-zero
curves `24a1`, `72a2` and `y^2 = x^3 - x`.

Together these give the collision depth from two positional statistics of the
leg sequence: `cd_n = 3` when three consecutive legs are equal and `cd_n = 4`
when only an endpoint pair is equal, both **unconditional**. On the remaining
stratum `cd_n = infinity` exactly when the affine representation is injective.
The envelope `W_n` itself embeds in `O(n)`, hence in `Isom(R^n)`, for every
`n >= 3` (`thm:alln` in `merged_novel_paper.tex`), and `n = 2` is the proved
exception. Injectivity of the affine representation at a given shape is a
separate question. Its arithmetic form ("Class C faithfulness") is **false**
(`thm:masterCfalse`). Its generic form is **true for every `n >= 3`**
(`thm:generic` in `merged_novel_paper.tex`, via `lem:Kplus`, the orthoscheme
Gram matrices being exactly the positive continuant locus): the affine
representation is injective on a co-null, comeagre set of leg tuples containing
every tuple with algebraically independent ratios, so the generic
`n`-orthoscheme group is the Coxeter group `W_n`, finitely presented, with
rational growth series `W_n(t)`. In the plane the representation is not
injective, and the generic series `U` is not D-finite; so the plane is the only
dimension in which the generic growth series is not rational
(`cor:dimcontrast`). Still open: rationality at non-generic shapes, and
faithfulness at a given Class C tuple for `n >= 4`.

`thm:barrier` shows the planar amenability argument cannot be run in any
dimension `n >= 3`: `O(n)` contains a free subgroup of rank two for `n >= 3`, so
`Isom(R^n)` is not amenable as an abstract group.

**Retraction.** An earlier version of this material argued unconditional
faithfulness for `n >= 3` from `det Q_n = -prod a_i^2 != 0`. That is a non
sequitur and is withdrawn; see `rem:detQ-nonsequitur` in
`paper_orthoscheme.tex`. Earlier releases of this README repeated the withdrawn
claim.

### Hahn-Exton q-cosine (hahn_exton_qcosine)

For every `0 < q < 1` the difference Galois group over `C(z)` of the
second-order q-difference equation satisfied by the Hahn-Exton q-cosine
contains `SL_2`, and the equation admits no sigma-delta integrability relation.
Via Hardouin-Singer and Dreyfus-Hardouin-Roques these give a second route to
differential transcendence over `C(z)`. **That transcendence is already known**,
and in stronger form, from Adamczewski-Dreyfus-Hardouin and Nishioka; what is
offered here is the explicit Galois-theoretic computation, valid also at
algebraic `q`. The paper also records the regularized product of the positive
zeros and proves an unconditional effective non-rationality bound for `beta_2`.
Transcendence of the number `beta_2` is open.


## Formalisation in Lean 4

Two projects, no `sorry` in either.

| | Toolchain | Targets | Contents |
|---|---|---|---|
| `lean/` | `v4.13.0` | 6 | Mathlib-free. The eight length-10 affine relations on `(3,4,5)`, the Coxeter relations, a first-principles BFS of A396406 to depth 17, the Fibonacci coincidence, the Schur-complement determinant identity on concrete leg sequences, Euler's theorem for finite directed multigraphs, the combinatorial core of the metric bounds, the rotation-relation classification, and the finite content of paper 1's appendices. |
| `lean/with_mathlib/` | `v4.30.0` | 130 | Requires Mathlib. Symbolic universality over `Q(a,b)` through `u_22`; the site-cost chain of paper 2's model; Mobius/Riccati factorisation at `l^1`; the Polya-Carlson coefficient bound; the mod-3 kernel censuses; the orthoscheme normals, rank-two exclusion and length-6 triple; the orthoscheme Gram continuant locus (`OrthoschemeGram`); the Fredholm minors of the travel kernel (`FredholmMinor`); the pole lemma for linear ODEs and the non-D-finiteness argument (`ODEPoles`, `NonDFinite`); the round stable norm (`RoundNorm`); the gap-run count of `cTrue` (`GapRuns`); the honeycomb distance and its graph realisation; the census identities and stratum censuses of paper 4; the Hahn-Exton exponent, ledger, exclusion and zero-series files; the corrected metric identity (`CorrectedSpan`, `PhiLipschitz`); and paper 2's junction pairing and model (`RJ*`, `Tstar*`, `RoomB34`, see below). |

Every target is registered both as a `[[lean_lib]]` and in `defaultTargets`, so
a clean `lake build` builds and checks all of them and all are covered by the
axiom audit. Certification is by exit status of a cold elaboration, then by
`#print axioms`; an empty axiom line is not evidence of success, because it also
appears for a failed constant.

Nine files (`CensusUniversal`, `CensusWitness`, `ComputableUniversality`,
`CylCensus`, `PolyaCarlson`, `QZeroSeries`, `SigmaKernel`, `SymbolicUniversality`,
`UKernel`) use `native_decide` and so trust the Lean compiler in addition to
the kernel, each such declaration carrying its own reflection axiom. This is
declared in the papers. `CylCensus.lean` is the slowest target at about 21
minutes; `SymbolicVerification.lean` needs about 9.6 GB to elaborate and is
cited by paper 1 as a tier-(i) result. The remaining files use only Lean's standard axioms.

**What is not formalised.** Paper 2's combinatorial layer is formalised and its
analytic layer is not. The paper lists, per analytic statement, the missing
Mathlib object that blocks it (`sec:leanboundary`). For `thm:V` and `thm:U` the
unformalised inputs are the assembly (M3') (a hand proof), the gate
`thm:star` and every analytic estimate behind it, the identification of the
Lean eigen-recursion hypotheses with the operators at an actual travel pole,
and the interval certificates. The analytic atoms are blocked
by Mathlib's current contents, which has no q-Pochhammer, no Jacobi triple
product, no Hahn-Exton q-Bessel, no q-difference equations and no steepest
descent. Each remaining star carries a recorded blocker in the paper. Absence of
a statement from a paper's Lean index table means there is no certificate for it.

Build:

```bash
# Mathlib-free project, about 20 seconds
(cd lean && lake build)

# Mathlib project; the first run downloads the prebuilt Mathlib cache
(cd lean/with_mathlib && lake update && lake exe cache get && lake build)
```


## Reproducing the computations

Python 3.10+ and Rust 1.70+.

```bash
# Word-metric solver self-check against BFS.  The cost roughly doubles per
# radius: measured 45 s, 87 s and 160 s at radii 9, 10 and 11, so the full
# radius-14 check quoted in the paper is on the order of tens of minutes.
python3 code/zeta_probe/lamp_profile.py 11

# Regenerate A396406 from the normal form and the metric formula, no BFS
cd code/zeta_probe/fire_rust && cargo run --release -- fire 16

# Uniform universality certificate through depth 30 (a few minutes)
python3 code/zeta_probe/certify.py 30

# Depth-38 certificate (Rust)
cd code/zeta_probe/certify38_rust && cargo run --release

# Orbit BFS (Rust, disk-streaming frontier; see its README for depth budgets)
cd code/rust_bfs && cargo build --release && ./target/release/bonfioli_bfs 32 4 1
```

Selected certificates for paper 2:

```bash
# Verified enclosure of the rectangle bound of lem:T2abs (branch and bound, MPFR,
# outward directed rounding on every operation)
cd code/zeta_probe/tools/t2abs_iv && cargo run --release -- scan <wmax>

# Exact site-cost law and gap-run cycle count of the transfer model (M)
cd code/zeta_probe/tools/sitecost && cargo run --release

# Block coefficient growth, exact integer arithmetic, two independent routes
python3 code/zeta_probe/blocks_growth.py

# Length-6 kernel exclusion for orthoschemes, exact integer matrices,
# over primitive integer leg tuples in dimension n with legs bounded by L
cd code/zeta_probe/tools/ortho_len6 && cargo run --release -- 3 200

# (R-J) positivity at q_1..q_12, MPFR interval arithmetic (thm:RJ)
cd code/zeta_probe/rj_certificates/r35rust && cargo build --release && \
  ./target/release/r54b ../models/poles_40.json 8,200 1 2 3 4 5 6 7 8 9 10 11 12

# Certified zero count of 1 - Sigma_1: 13 zeros on [0, 0.9988]
cd code/zeta_probe/rj_certificates/r39pole && cargo build --release && \
  ./target/release/r39pole 0.985 0.9988 256 40 8
```

`code/zeta_probe/rj_certificates/README.md` lists every certificate there, with
its arguments and trust base (MPFR plus hand-written interval code).

`code/zeta_probe/README.md` indexes that directory. `code/reproduce/` holds
standalone scripts that do not depend on it.


## OEIS

| Sequence | What it counts | Status |
|---|---|---|
| [A396406](https://oeis.org/A396406) | 2D right triangle, unequal legs | Published |
| [A397439](https://oeis.org/A397439) | 3D orthoscheme, pairwise distinct legs | Published |
| [A397437](https://oeis.org/A397437) | 4D orthoscheme, pairwise distinct legs | Published |
| [A396927](https://oeis.org/A396927) | 5D orthoscheme, pairwise distinct legs | Published |
| [A397438](https://oeis.org/A397438) | 6D orthoscheme, pairwise distinct legs | Published |
| [A396953](https://oeis.org/A396953) | 7D orthoscheme, pairwise distinct legs | Published |

Each of the orthoscheme entries is the
coefficient sequence of the rational function `W_n(t)` with dominant pole
`1/r_n`; A396406 is of a different nature, agreeing with `W_2(t)` only to
degree 9. See `rem:oeis` in `paper_orthoscheme.tex`.


## Citing

Concept DOI [10.5281/zenodo.20370090](https://doi.org/10.5281/zenodo.20370090),
which always resolves to the latest archived release. Metadata in
`CITATION.cff`.


## Status of the formalisation (v10.5.0)

The Lean development is in `lean/with_mathlib/` (Mathlib project) and `lean/`
(Mathlib-free). The whole build is clean with **0 `sorry`** and every
declaration carries a `#print axioms` line. Nine files use `native_decide`
(named and scoped below); the rest use only Lean's standard axioms. The
v10.3.0 content (`BlockAdditivity`, `BlockAdditivityGeneral`,
`DihedralGeodesic`, `DmLength`, `PhiLipschitz`, `CorrectedSpan`) uses neither
`native_decide` nor `ofReduceBool`. Claims below are machine-checked unless
marked otherwise.

**New in v10.5.0.** Four files in `lean/with_mathlib/`, all in `defaultTargets`
(130 targets). None uses `sorry` or `native_decide`; the recorded axiom output
lists only the standard axioms.

| File | Theorems | Contents |
|---|---|---|
| `OrthoschemeGram.lean` | 18 | `lem:Kplus` of `merged_novel_paper.tex`: the continuants of the orthoscheme Gram data in product form and positive, `D_{n+1} = 0`, the explicit inverse map, and injectivity up to scale. |
| `FredholmMinor.lean` | 18 | Paper 2's `thm:fredholm`(iii): `det[y_max(i,j)]` for every `k`, the principal minors of the travel kernel, the gap sums, and the closed form `(2(1-q))^k q^{k^2}/(q;q)_{2k}` as a `HasSum`. |
| `ODEPoles.lean` | 9 | `lem:odeposes`: a meromorphic solution of a linear ODE has no pole where the leading coefficient is nonzero. |
| `NonDFinite.lean` | 22 | `thm:nonDfinite` in abstract and disc form: a meromorphic function on the unit disc with infinitely many poles satisfies no linear ODE (homogeneous or inhomogeneous) with coefficients holomorphic near the closed disc, in particular none with polynomial coefficients, and no contracting linear q-difference equation. Pole existence enters as a hypothesis. |
| `RoundNorm.lean` | 13 | Abstract part of paper 1's `prop:round-norm`: a homogeneous function on C that is invariant under an irrational rotation and bounded on the unit circle equals `s(1)|v|`. |
| `GapRuns.lean` | 22 | For `k* != 0`, `cTrue` is the sum over maximal gap runs of `(L - shield)`, with the shield matched to the junction cuts of Lemma J (the combinatorial core of paper 2's (M3'), outside the `k* = 0` sector). |

**New in v10.4.0 (paper 2's (M) and (R-J)).** Ten files in `lean/with_mathlib/`,
all in `defaultTargets`. None uses `sorry` or `native_decide`, and the recorded
`#print axioms` output lists only the standard axioms. Counts are `#print axioms`
lines per file, 104 in all:

| File | `#print axioms` | Contents |
|---|---|---|
| `RJMain.lean` | 24 | The `X`, `Y` shift identities and their solutions (`X_shift`, `Y_shift`, `X_closed`, `Y_closed`), including the double-sum interchange (`summable_swap`). |
| `RJShift.lean` | 7 | Shift-identity support for `RJMain`. |
| `RJClosedForm.lean` | 11 | The closed forms of `Pi_1`, `Pi_q` (`closed_form`, `closed_form_yq`) and the positivity step from the gate bound (`gate_bound`, `bracket_pos`, `bracket_yq_pos`). |
| `RJIdentities.lean` | 15 | Auxiliary finite identities for the travel recursion (Casoratian telescoping). |
| `RJLemmaJ.lean` | 10 | The junction cut criterion used in `app:M3prime`, against `SiteCost.PathData.cut`. |
| `RJPhi.lean` | 15 | Faithfulness of the model: the affine realisation intertwines the three generators and is injective. |
| `RJMetricAll.lean` | 1 | `metricAll`: `wordLength = lRTrue + 2 cTrue` for every element. |
| `TstarCore.lean` | 2 | The leapfrog drift identity behind the gate amplitude. |
| `TstarAmplitude.lean` | 8 | Amplitude bounds for the leapfrog invariant `G_s` (AM-GM step, per-step ratio, telescoped max/min bound). |
| `RoomB34.lean` | 11 | A parallel development of the same leapfrog amplitude bounds. |

In these files the gate, the analytic estimates and the eigen-relations of `R`
enter as hypotheses.

**Closed.**

- The free-product block-reduction step of paper4's `cor:onset`: for `W_m =
  D_m * C_2`, any list of blocks that are each nontrivial in `D_m` and
  individually geodesic concatenates geodesically across all three
  generators, unconditionally (`BlockAdditivity.block_additivity`,
  `BlockAdditivityGeneral.lean`), combined with the per-block dihedral
  geodesic bound (`ev_ne_rotation_of_short`, `DihedralGeodesic.lean`) and the
  general `D_m` word-length function (`DmLength.lean`). Together these give
  the full geometric-translation argument `rem:onset-lean` cites.
- `RunStrandsConnected` (the Eulerian-existence input to the shield law), at
  arbitrary even, non-constant widths, by explicit construction — `EltBridge`
  (`zzTurn`/`zzData`) and `VZigzag` for the widths a real group element has.
  This had been recorded for several releases as "confirmed hard, needs
  new-to-Mathlib graph theory"; that verdict is **withdrawn**.
- Hypothesis `(T)` (travel-block invariance) is a theorem and is no longer a
  standing hypothesis.
- `Elt.c = ConfigLoop.defect` for every group element.
- `prop:transtrick` unconditionally for Euclidean isometries; `prop:reduce`
  modulo `lem:noab` alone.
- The three-regime deviation law as a computable, verified shape lookup
  (`DeviationLaw`): `c_T`, `e_T` are closed forms in `(a,b)`, regime selection
  is two integer comparisons, and `n_(1,2) = 33` verifies by `decide`.
- `cut s ↔ siteCost s = 0` (`PhiLipschitz`): a cut site is exactly a zero-cost
  site, so the `Φ = 0` conjunct in `PathData.cut` is redundant.
- **The full corrected metric identity, unconditionally, for every reachable
  `g`**: `wordLength g = lRTrue g + 2 * cTrue g` (`PhiLipschitz.wordLength_eq_lRTrue_add_two_cTrue`).
  v10.3.0 closed both directions left open at v10.0.0. The lower bound
  (`wordLength_ge_lRTrue_add_two_cTrue`) follows from the 1-Lipschitz property
  of `Φ = lRTrue + 2·cTrue` over all three generators. The upper bound
  (`wordLength_le_lRTrue_add_two_cTrue`) follows from a fully unconditional
  descent lemma (`exists_descent_unconditional`: for any `g` not the identity,
  at least one of the three generators strictly decreases `Φ`, with no
  restriction on the cursor position `kstar`) and a strong induction on `Φ`
  that builds an explicit reaching word of length `Φ(g)` (`reaches_of_phiZ`),
  using that all three generators are involutions to run the chain backward
  from `g` to the identity.

**Retracted or corrected in v10.3.0** — anyone citing v9.x should re-check.

- The metric identity `l_T = l_R + 2c` is **false as formalised**, for the Lean
  development's own `c`; it fails at the identity element. Two definitional
  causes (the formal span forces edge 0 into every configuration; the formal cut
  set omits the boundary-shield site). Repaired additively in `CorrectedSpan`;
  the repaired identity is now proved, both directions, unconditionally, for
  every reachable `g` (`PhiLipschitz.wordLength_eq_lRTrue_add_two_cTrue`, see
  above).
- `(M3)`/`eq:assembly` is **vacuous as stated**: satisfiable for arbitrary `W`,
  and de-truncating does not help. A proof in that form would establish nothing.
  Named, non-vacuous replacement with a uniqueness theorem in
  `AssemblyContract`.
- The single-chain zigzag described in `EltBridge`'s own docstring is **false**
  at even multiplicities; the correct construction is spine+zigzag. The counting
  core is kernel-checked in `ZigzagParity`.

**Open.** `(M2)`'s reverse shield inequality, which `thm:model` no longer needs;
a Lean formalisation of the assembly (M3'), which has a hand proof in paper 2's
Appendix `app:M3prime`; and `lem:noab`. (The formalised metric identity's own
lower bound, listed as open in v10.0.0, was closed in v10.3.0.)

## On the use of AI

This work was produced through extended human-AI collaboration. The
mathematical development was AI-led under human direction: the principal model
was Anthropic's Claude, cross-checked against other large language models in an
adversarial review process. The AI derived and wrote the proofs and the paper
text, wrote the exact-rational BFS and the Rust tools, produced the SymPy and
SageMath symbolic and rank-0 descent verifications, and carried out the Lean 4
formalisation. The author, an independent researcher and not a professional
mathematician, directed the investigation, ran the cross-checking, verified that
the computational artifacts run and reproduce, and is responsible for the final
text and any remaining errors. The Lean 4 certificates are provided so that the
machine-verifiable claims need not rest on trust in either the human or the AI
contributors; the papers state, per statement, which claims those are.


## License

- Text and papers: CC-BY-4.0.
- Code: MIT.
