# Lean files for the triangle reflection paper

> **BUILD STATUS (2026-08-10).** Every file listed below is now registered in
> `lean/with_mathlib/lakefile.toml`, both as a `[[lean_lib]]` and in
> `defaultTargets`, so a clean `lake build` builds and checks all of them and
> all are covered by the axiom audit.
>
> The cross-package import that used to make `Bridge.lean`, `LinearPart.lean`
> and `PlaneGroup.lean` unbuildable is repaired. They import
> `RotationRelations`, which lives in the Mathlib-free `lean/` package; the
> with_mathlib lakefile now carries
>
> ```toml
> [[lean_lib]]
> name = "RotationRelations"
> srcDir = ".."
> ```
>
> so that module is compiled in place from `lean/RotationRelations.lean` without
> being duplicated and without a cross-package `require`. It is import-free and
> compiles under Lean 4.30 as well as 4.13. Measured build times, single
> threaded on a cold `lake build`: `RotationRelations` 5 s, `LinearPart` 10 s,
> `PlaneGroup` 6 s, `Bridge` 4 s, `CensusWitness` 10 s, `CensusUniversal` 9 s,
> `CylCensus` 1256 s.
>
> `CensusWitness.lean`, `CensusUniversal.lean` and `CylCensus.lean` are proved
> by `native_decide` and so trust the Lean compiler in addition to the kernel;
> each declaration carries its own reflection axiom
> `<thm>._native.native_decide.ax_1_1`. This is declared in the Declarations
> section of the paper. `CylCensus.lean` is the slowest target in the whole
> project at about twenty-one minutes.

The first three files import nothing and are checked with `lean <file>` on Lean
4.13 or 4.30; no Mathlib build is required. The rest are under `with_mathlib/`
and import Mathlib, and `Bridge.lean`, `LinearPart.lean` and `PlaneGroup.lean`
also import `RotationRelations` through the `srcDir` entry described above.

| file | proved | left open |
|---|---|---|
| `TriangleFlowMetric.lean` | the combinatorial core of both bounds of the metric theorem: per-edge domination and parity, doubling of connectors, the summation (`lower_bound`), vertex balance, and the length and flow of the word read off a circuit (`upper_bound`) | nothing; the graph inputs enter as hypotheses `hst` and the circuit |
| `EulerCircuit.lean` | **Euler's theorem for finite directed multigraphs** (`euler_circuit`): a balanced multigraph whose edges are reachable from a base vertex carries a circuit using every edge once. Complete, no `sorry`. Mathlib has only the necessary degree condition, not this sufficiency | nothing |
| `RotationRelations.lean` | the letter invariants; block peeling and the two bounds; **the classification** (`classify_normal_forms`), **the converse** (`markBoth_valid`) and **the count** (`admissible_count`: `(n-1)^2` admissible index pairs, that is `c^2`) | nothing |
| `with_mathlib/CoxeterTorsion.lean` | **the free-product torsion criterion** (`finite_order_iff`): in `W_m = D_m * C_2`, the word `u₀ x₂ u₁ x₂ u₂` with `u₁ ≠ 1` has finite order exactly when `u₂u₀ = 1` | nothing |
| `with_mathlib/LinearPart.lean` | **the linear part of a product of reflections** (`linOf_eq`): `exp (2i Σ_i c_i(w) θ_i)`, and `linOf_of_cvec_two_eq_zero`, the rotation by `2πc₁/m` when `c₂ = 0` | nothing |
| `with_mathlib/PlaneGroup.lean` | **the plane group itself**: `Aff` (`z ↦ a z + b` or `a conj z + b`, `a` a unit) with its `Group` instance via `act_injective`, `refl` and `refl_sq`, and `linCoeff_prod` identifying the abstract invariant with the actual linear coefficient | nothing |
| `with_mathlib/CensusWitness.lean` | **the growth of a rational witness triangle to radius 12** (`census_witness`): `1,3,6,…,1536,3039,6012`, so deficit `33` at radius 11 and `132` at radius 12. Proved by `native_decide` | nothing here; the matching universal identities are `CensusUniversal.lean` below |
| `with_mathlib/CylCensus.lean` | **the stratum translation census** (`census_m3`…`census_m9`): the number of translations of each even length up to 18 on the strata `α = π/m`, for `m = 3,4,5,6,7,9`, matching the paper's table row for row. Generic on the stratum, not a witness: the third side's direction is an indeterminate `V` in `Z[ω][V, V⁻¹]`. Proved by `native_decide`; checking it takes about twenty-one minutes | the row `m = 11` |
| `with_mathlib/CensusUniversal.lean` | **part (i) of the census theorem** (`universal_identities`): each of the 33 pairs is an identity in `ℤ[X,Y]`, so it holds at every triangle, not only at the witness. Proved by `native_decide` | nothing |
| `with_mathlib/AntipairRows.lean` | **the antipair corollary** (`antipair_min_kClosed`): `min over (n,j) of max{k(n,j), k(n+h,j)} = h-1` for `h ≥ 2`, as an `IsLeast` over `HexDistance.kClosed`, plus the `h = 1` case (`antipair_min_kClosed_one`) and the refutation of the withdrawn valley argument on row 3 (`row3_eq_kClosed`, `row3_counterexample_kClosed`) | the closed form itself, which is `HexDistance.lean` |
| `with_mathlib/StratumGeneric.lean` | **the finiteness principle behind the stratum census** (`badSet_finite`, `eval_eq_zero_iff_of_not_mem`, `count_eq_of_not_mem`, `exists_generic`): a readout of the vanishing pattern of finitely many polynomials is constant off a finite set of parameters | that any particular rational leg sample lies outside that set |
| `with_mathlib/Bridge.lean` | **part (iii) of the rotation-relations theorem** (`unique_finite_order`): evaluating the letter-list model in the free product, exactly one admissible pair gives an element of finite order, namely `a = 0`, `j = n-1` | nothing |

The files backing the closed form of the lamp distance itself
(`with_mathlib/HexDistance.lean` and the graph files built on it) are not
tabulated here; their declaration names are given at the statements in the
paper.

No file contains a `sorry`. Every file but `CensusWitness.lean`,
`CensusUniversal.lean` and `CylCensus.lean` uses only Lean's standard axioms;
those three are proved by `native_decide` and so trust the compiler as well.
`CylCensus.lean` alone takes about twenty-one minutes to check (measured 1256 s,
peak RSS 1383 MB, single threaded).

 Declarations in `TriangleFlowMetric.lean` and
`EulerCircuit.lean` have axioms `[propext, Quot.sound]`; the classification
theorems in `RotationRelations.lean` and everything in `CoxeterTorsion.lean`
and `Bridge.lean` additionally use `Classical.choice`, the third of Lean's standard axioms.

`euler_circuit` avoids decomposing the multigraph into connected components,
which is what makes the usual presentation heavy. The circuit is grown one
closed trail at a time: while some unused edge leaves a vertex of the current
circuit, a greedy walk from that vertex is closed (balance), is cut into the
circuit (`trail_split_at`, `splice`), and the induction proceeds on the number
of unused edges. When no unused edge leaves the circuit, connectivity forces
the remainder to be empty.

## The Mathlib file

`with_mathlib/CoxeterTorsion.lean` models `W_m = D_m * C_2` as
`Monoid.CoprodI` of a two-element family of dihedral groups (`DihedralGroup 1`
is the group of order two generated by the third reflection). Mathlib supplies
the free product, its normal form `Monoid.CoprodI.Word.equiv`, reduced words
`Monoid.CoprodI.NeWord`, and `DihedralGroup`, but **no torsion theorem for free
products**, so both directions are proved here:

* `finite_order_of_cancel` — if `u₂u₀ = 1` the word is a conjugate of `u₁`,
  which lies in the finite factor `D_m`, so it has finite order.
* `infinite_order_of_noncancel` — conjugating by `u₀⁻¹` turns the word into the
  cyclically reduced `x₂ u₁ x₂ (u₂u₀)`, whose letters alternate between the two
  factors; `blkPow` exhibits every power as a `NeWord`, and
  `neword_prod_ne_one` (from injectivity of `Word.prod`, the inverse half of
  `Word.equiv`) shows no power is `1`.

This closes the step that `RotationRelations.lean` left open.

`with_mathlib/Bridge.lean` then joins the two models. `ev` evaluates a letter
list in `W m`, sending the apex reflections `r₀ = sr 1`, `r₁ = sr 0` into the
dihedral factor so that `r₁r₀` is the rotation by one step, and `r₂` into the
other factor. `markBoth_lt` and `markBoth_gt` rewrite the marked pattern as an
explicit concatenation of plain runs, `ev_markBoth_lt` and `ev_markBoth_gt`
evaluate it as a `blockWord`, and `unique_finite_order` reads off part (iii):
for `n ≤ m`, which is the range `c ≤ m-1` of the paper,

```
IsOfFinOrder (ev m (markBoth n a j))  ↔  a = 0 ∧ j = n - 1
```

so the count `exactly one` is proved, not merely checked. The two marks in
decreasing order never give finite order, because both the middle block and
the join stay strictly between `0` and `m`.

`code/triangle_relations/torsion_count.rs` remains as an independent check of
the same statement for `3 ≤ m ≤ 60`, `1 ≤ c ≤ m-1`.

`build.sh` builds everything. Point it at the `.lake/packages` directory of any
Lean 4.30 project with Mathlib built:

```sh
MATHLIB_PACKAGES=<project>/.lake/packages ./build.sh
```

Without that variable it builds the three import-free files and stops.
