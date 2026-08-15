# Symbolic verification (with Mathlib)

A separate Lean 4 project requiring Mathlib, pinned to `leanprover/lean4:v4.30.0`
(matching Mathlib `v4.30.0`). It has **60 build targets**: 59 source files in
this directory plus `RotationRelations`, which is compiled in place from
`../RotationRelations.lean` through a `srcDir` entry so that there is exactly
one copy of it. Every target is registered both as a `[[lean_lib]]` and in
`defaultTargets`, so a clean `lake build` builds and checks all of them and all
are covered by the axiom audit. No file contains a `sorry`.

Certification discipline: a file counts as checked only when a cold elaboration
exits 0, and the axiom list is read afterwards. An empty `#print axioms` line is
not evidence of success. It is the legitimate output for a `decide`-proved
theorem, and it has also been observed printing for a constant that failed to
elaborate while the `sorryAx` surfaced elsewhere in the same file.

The statement-to-declaration tables live in the papers, not here. Absence of a
statement from a paper's Lean index means there is no certificate for it. The
files backing paper 4 and the rotation-relation chain are tabulated separately
in `../README_triangle.md`.

Some file headers still name the retired document titles `paper 3`, `paper 1b`
and `paper "extra"`; those documents were merged on 2026-08-10 into
`paper_orthoscheme.tex` (the first two) and into the appendices of `paper1.tex`
(the third). Headers naming `route_b/` refer to working notes that are not part
of the release; the statements they cite are reproduced in full in `paper2.tex`.


## Paper 1: universality, the metric, and the finite-horizon exclusions

| File | Contents |
|---|---|
| `SymbolicVerification.lean` | The eight relations of Table 1 hold symbolically over `Q(a,b)`, that is simultaneously for every right triangle with positive unequal legs, by `ring` over `MvPolynomial (Fin 2) Q`. Not cited by paper 2; it needs about 9.6 GB to elaborate. |
| `SymbolicUniversality.lean` | Canonical Coxeter-word enumeration and the Fibonacci-phase counts `F(n+3)` for `n = 0..10`, including the depth-10 count 233. |
| `ComputableUniversality.lean` | `universal_layers_through_22`: the BFS layer counts `a(0)..a(22)` of A396406 are the universal sequence for every right triangle with positive unequal legs. A hand-rolled computable bivariate polynomial type and a tracked-denominator affine isometry type, deduplicated over `Q(a,b)` relative to the common denominator `(a^2+b^2)^22`. One `native_decide`, about 22 minutes. |
| `SchurGeneral.lean` | The four uniform polynomial identities capturing the algebraic skeleton of the general-`n` Schur-complement determinant identity `det Q_n = -prod a_i^2`. |
| `DeviationLattice.lean` | Algebraic facts under the deviation-depth law: the palindromic quadratic `mu_T`, `lem:finite-svp`, and `rem:l1-insufficient`. |
| `MooreCriterion.lean` | The finite-state principle behind paper 1's metric lower bound, **and its refutation**: Moore's criterion needs both state sets, so the withdrawn argument does not run. |
| `ShapeArith.lean` | The four numerical claims of paper 1 that an audit found wrong, restated correctly and proved rather than searched. |
| `NoRecurrence.lean` | `prop:no-recurrence`: `u_0..u_38` satisfy no linear recurrence over `Q` of order at most 19, by Farkas witnesses. Kernel evaluation, no `native_decide`. |
| `ModularRankCertificate.lean` | The bridge turning a modular left inverse into a statement about rational solutions, which is the missing step of `prop:no-dfinite`. |
| `NoDFiniteData.lean` | Generated certificate data; regenerate with `code/zeta_probe/tools/nodfinite/gen_lean_data.sh`. Regenerates byte-identically. |
| `NoDFiniteCertificates.lean` | `prop:no-dfinite` and the narrowed holonomic box of `prop:finite-horizon`(ii), closed by the kernel with no `native_decide`. |
| `DFiniteReduction.lean` | Reduction of the 52-pair search grid to its six maximal pairs. |
| `OverDetermination.lean` | The guard lemma for finite-horizon exclusion searches: what makes a negative search result meaningful. |
| `ModPStateInfinite.lean` | `prop:modp-state-infinite`: for every prime `p` the mod-`p` state space is infinite. |

`../PaperExtraMod2.lean` and `../PaperExtraCounts.lean`, in the Mathlib-free
project, carry the rest of the appendix propositions.


## Paper 2: the transcendence proof

### The site-cost chain of the transfer model (M)

| File | Contents |
|---|---|
| `SiteCost.lean` | `lem:transport`: the exact closed form for the four-class transportation minimum, `max(\|alpha\|, \|beta\|, \|Phi\|)`, stated as `IsLeast` so the lower bound (six explicit LP dual certificates) and the attainment are separate obligations. Also `marker_forms_differ`, which exhibits by `decide` the refutation of the earlier marker clause. Imports only `Mathlib.Order.Bounds.Basic`, so it elaborates in about 14 seconds. |
| `MarkedSite.lean` | `cor:localcost` in full: the site cost law at every site of a realisation, virtual events included, in all eight site types at once. |
| `PairingMatrix.lean` | Reconciles the paper's bijection definition of a pairing with the matrix representation `SiteCost.lean` works in; both directions proved cost-preserving. |
| `Realisation.lean` | `def:pairing` over a whole edge path, and with it `cor:lRclosed`, `cor:marker` and the realisation-quantified parts of `prop:cut`. Faithfulness is checked in both directions, so the rigidity `m_j >= max(\|d_j\|, \|f_j\|)` and the parity `m_j = d_j mod 2` are consequences of the encoding rather than assumptions built into it. |
| `CutCross.lean` | The middle sentence of `prop:cut`, closed at cross mass `P = 2` exactly as the paper closes it. |
| `CutComponents.lean` | The counting half of `prop:cut`, over an abstract graph, stated as injections rather than cardinality facts so no finiteness hypothesis appears. The component count itself is **not** verified; its blocker is recorded in the paper. |
| `Mobius.lean` | `prop:mobius`, the Sherman-Morrison factorisation, for an arbitrary module over an arbitrary field. |
| `MobiusL1.lean` | The `l^1` instantiation of `prop:mobius` at the concrete data of `eq:rankone`, which is what the paper's statement is actually about. |
| `Reciprocity.lean` | The kernel-symmetry proof of `prop:recip`, `t_0 = b_1`. |

### Blocks, kernels and the analytic skeletons

| File | Contents |
|---|---|
| `PolyaCarlson.lean` | The coefficient-growth input to `thm:blocks`: `2^{j+1} <= \|[q^{(j+1)^2}] Sigma_1\|` for `j = 0..9`, from the `A/C` recursion. `native_decide`. |
| `SigmaKernel.lean` | The 3-kernel of `Sigma_1 mod 3` through level 3 is the full ternary tree, all 40 decimation words pairwise distinct. Evidence against 3-automaticity. `native_decide`. |
| `UKernel.lean` | The same certificate for the true series `u_n = A396406`, from `(u_n mod 3)` for `n <= 270` produced by `code/zeta_probe/tools/u_modp_rust`. `native_decide`. |
| `QTrigIdentities.lean` | The per-term algebraic identities of the q-trigonometric layer, and the Casoratian constancy giving the half-step invariant. |
| `GaussHS.lean` | The Gaussian moment identity behind the Hubbard-Stratonovich representation of the denominator block `S_e`, from Mathlib's `GaussianFourier`. |
| `DiscreteConserved.lean` | The two conserved quantities of the symmetric three-term recurrence: the discrete Casoratian is constant, and the discrete energy drifts by an exact amount. |
| `GramCasoratian.lean` | The Gram-Casoratian identity for the same recurrence, which both gate blocks satisfy. |
| `AtomN.lean` | `cross_term`, the half-integer cross-term identity from `sin^2 + cos^2 = 1`, and `h_bounds`, `1 <= h(X) <= 3/2` for `X > 0`. This covers the rational inequality, not the confluence argument around it. |
| `BboundedSkeleton.lean` | The algebraic skeleton of `lem:Bbounded`; its analytic inputs are not formalised. |
| `SelowerSkeleton.lean` | The algebraic skeleton of `prop:selower`; the annulus representation, the Poisson envelope and the mean value theorem are not formalised. |
| `GateInputs.lean` | The algebraic core of the four inputs G1 to G4, chosen because they are where the derivation went wrong in practice. |
| `SDAssembly.lean` | `lem:infpoles`, infinitude and accumulation of the travel poles, machine-checked from its analytic input. |
| `UAssembly.lean` | The assembly of `thm:U`. Each analytic lemma enters as an explicit named hypothesis, so what is certified is that they compose into the conclusion, not that they hold. |

**What is not formalised.** Paper 2 prints its own formalisation debt against a
reproducible criterion: of 67 statements, 53 carry a complete written proof that
has not been formalised, and each carries a recorded blocker. Eighteen analytic
atoms are blocked by Mathlib's current contents, which has no q-Pochhammer, no
q-binomial, no Bessel functions, no Jacobi triple product, no q-difference
equations and no steepest descent or stationary phase. Mathlib does carry
`jacobiTheta2` with summability, analyticity and the modular functional
equation, but not the triple product that would connect it to the q-world.


## Paper 4: shortest relations and the honeycomb metric

| File | Contents |
|---|---|
| `CensusWitness.lean` | The growth of a rational witness triangle to radius 12: `1,3,6,...,1536,3039,6012`, so deficit 33 at radius 11 and 132 at radius 12. `native_decide`. |
| `CensusUniversal.lean` | Part (i) of the census theorem: each of the 33 pairs is an identity in `Z[X,Y]`, so it holds at every triangle. `native_decide`. |
| `CylCensus.lean` | The stratum translation census `census_m3 .. census_m9`, generic on the stratum rather than at a witness, the third side's direction being an indeterminate. `native_decide`, about 21 minutes. The row `m = 11` is left open. |
| `StratumGeneric.lean` | Why the tabulated stratum census is the generic value: a readout of the vanishing pattern of finitely many polynomials is constant off a finite set. |
| `HexDistance.lean` | `lem:krows`, the closed form for the lamp distance, proved. |
| `HexGraph.lean` | The geometry `HexDistance.lean` left outside Lean: the honeycomb as a concrete `SimpleGraph`, with its adjacency *proved* equal to the share-two-sites relation rather than transcribed. |
| `GraphLocalDistance.lean` | The local criterion for a graph distance function, in the generality in which it is true: no finiteness, connectedness or decidability assumed. |
| `AntipairRows.lean` | `cor:antipair` and `rem:krows-shape`, including the refutation of the withdrawn valley argument on row 3. |
| `CoxeterTorsion.lean` | The free-product torsion criterion in `W_m = D_m * C_2`. Mathlib supplies the free product, its normal form and `DihedralGroup`, but no torsion theorem for free products, so both directions are proved here. `code/triangle_relations/torsion_count.rs` checks the same statement independently for `3 <= m <= 60`. |
| `Bridge.lean` | Part (iii) of the rotation-relations theorem: exactly one admissible pair gives an element of finite order. |
| `LinearPart.lean` | The linear part of a product of reflections, and the rotation by `2 pi c_1/m` when `c_2 = 0`. |
| `PlaneGroup.lean` | The plane group itself, with its `Group` instance, `refl`, `refl_sq`, and `linCoeff_prod` identifying the abstract invariant with the actual linear coefficient. |


## paper_orthoscheme

| File | Contents |
|---|---|
| `EnvelopeDichotomy.lean` | The arithmetic of `thm:dichotomy` and the root identity of `thm:envelope`. |
| `NdimRate.lean` | `r_n = 1 + 2 cos(2 pi/(n+3))` and the corollary `3 - r_n = 4 sin^2(pi/(n+3))`. |
| `OrthoschemeNormals.lean` | `lem:normals`: the facet normals and their orthogonality pattern, proved for every `n`. The paper previously asserted this with "verified symbolically for `n <= 5`". |
| `OrthoschemeDet.lean` | The uniform Schur-complement determinant identity `det Q_n = -prod a_i^2`. Note that this does **not** imply faithfulness; see `rem:detQ-nonsequitur`. |
| `RankTwoExclusion.lean` | The exclusion feeding `thm:rank2` and the two finite branches of `thm:cd-general`. Its docstring states the narrower scope at length three, and the citation to it in the paper was narrowed to match. |
| `ReflectionTriple.lean` | Step (2) of `thm:len6`, the linear-algebra heart of the length-six exclusion. |


## hahn_exton_qcosine

| File | Contents |
|---|---|
| `QCosineExponents.lean` | The Section 3 exponent gap that replaced a one-point numerical check in `thm:sl2`, the Newton-polygon exponents and their strict convexity, the ledger sum, the triangular law, and the Farey separation. |
| `QCosineLattice.lean` | The Section 4 and 5 exponent and order bookkeeping, including `qPochhammer_isUnit` and the `prop:stablelaw` depth arithmetic. |
| `QSiegelLedger.lean` | `prop:secondkind`'s degree bookkeeping and `prop:reduction` in full, denominator clearing included, with no `MvPolynomial`. |
| `QEffectiveExclusion.lean` | The Diophantine half of `prop:effective`: the Farey gap, interval uniqueness and the width comparison. The certified interval arithmetic locating `q*` enters as hypotheses. |
| `QZeroSeries.lean` | A truncated `Z`-power-series engine running the Newton recursion for the zero series entirely over `Z`, to order `q^80`. `native_decide`. |

The paper's "Machine verification" section carries the full
statement-to-declaration table and the list of what is not formalised.


## Requirements and build

- Disk: about 10 GB for the Mathlib cache, persistent.
- RAM: several GB. `SymbolicVerification.lean` alone peaks near 9.6 GB; a
  memory cap below that will kill the build mid-write, and Lake deletes a
  target's output before rebuilding, so the cap must be set high enough.
- First-time install: 15 to 45 minutes, mostly downloading and unpacking the
  prebuilt Mathlib cache.

```bash
lake update           # fetches the Mathlib source
lake exe cache get    # downloads prebuilt Mathlib .olean files
lake build            # builds all 60 targets
```

A warm `lake build` over all 60 targets replays unchanged traces in seconds.


## Why is this a separate project?

The parent directory holds a Mathlib-free Lean project that builds in about 20
seconds and needs about 500 MB of disk. Keeping it free of Mathlib means anyone
can check the concrete rational-arithmetic certificates on a fresh machine with
no heavyweight dependencies. Everything that needs real analysis, group rings,
`MvPolynomial`, free products or q-series lives here instead.
