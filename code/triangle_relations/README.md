# Triangle reflection groups: verification scripts

Regenerates every computational statement of *The shortest relations of planar
triangle reflection groups* (`paper/journal/paper4.tex`). Python scripts need
`sympy`; Rust directories build with `cargo build --release`. Data lives in
`data/triangle_relations/`.

| Paper statement | Script |
|---|---|
| Theorem 2.1, the 33 universal relations and the 132 depth-12 coincidences, as identities in `Z[p,q]` | `verify_universal_relations.py` |
| Theorem 2.1(ii), coincidences at the rational witnesses; growth to depth 12 | `rust_cost/` (exact BFS, witness as argv) |
| Section 5, flow model: faces, sharing, separation, the metric `ell = ||phi||_1 + 2 st`, the census by word length | `honeycomb_metric_and_census.py` |
| Section 5, the four length-18 collisions at the witness `(1/3,1/2)` | `witness_collisions.py` |
| Section 5, element-level census at the witness `(2/7,3/5)`, giving 3684 | `witness_second.py` |
| Theorem 6.x(i)-(ii), cylinder faces, wrapped sites, wrapping cycles, level sums | `cylinder_structure.py` |
| Theorem 6.x(iii), the stratum metric, checked against exact BFS | `cylinder_metric_check.py` |
| Theorem 6.y(ii), the `c^2` normal forms, against brute force | `halfturn_normal_form_count.py` |
| Theorem 6.y(iii), exactly one word of finite order in `W_m = D_m * C_2` | `free_product_involutions.py` |
| Section 6 table, onset and deficit on the strata `m = 8,9,10,11,12` | `stratum_probe.py` |
| Section 6, whole-stratum certificates for `m = 4, 6` and for `m = 8` | `stratum_certificate_m4_m6.py`, `stratum_certificate_m8.py` |
| Section 6, the `m = 2` row | `stratum_m2.py` |
| Proposition 6.z, stratum translation census | `emit_generators.py` then `rust_strat/`; cross-checked by `stratum_bfs_census.py` |
| Theorem 5.x(iii), the unique word of finite order | `torsion_count.rs` |

`torsion_count.rs` applies the criterion proved in
`lean/with_mathlib/CoxeterTorsion.lean` -- the word `u0 x2 u1 x2 u2` has finite
order in `W_m = D_m * C_2` exactly when `u1 = 1` or `u2 u0 = 1` -- to all `c^2`
words `w_{a,b}`, and confirms that exactly one of them has finite order for
every `3 <= m <= 60` and `1 <= c <= m-1`. The same statement is proved in
`lean/with_mathlib/Bridge.lean` as `unique_finite_order`, so this is an
independent check rather than the only evidence. Build with
`rustc -O -o torsion_count torsion_count.rs`.

`stratum_fields.py` holds the exact number fields `Q(2cos(pi/m))(sin(pi/m))`
and the stratum generators used by several of the above.

## Run order

Three scripts read files that another step writes, by relative path, and print
`skipped` if run first in a cold clone. The order is:

1. `cd rust_cost && cargo build --release` and run it at each witness; it writes
   `rust_cost/translations_d<d>.txt` and `rust_cost/translations_w2_7_3_5_d<d>.txt`.
2. `python3 honeycomb_metric_and_census.py`; it writes `census_configs.json` in
   the current directory and reads the `rust_cost/translations_d<d>.txt` of
   step 1.
3. `python3 witness_collisions.py` and `python3 witness_second.py`; both read
   `census_configs.json` from step 2, and `witness_second.py` also reads the
   `translations_w2_7_3_5_d<d>.txt` of step 1.

Everything else is standalone.

## Companion Rust tools

Four tools cited by paper 4 live under `code/zeta_probe/tools/` rather than
here, and are documented in that directory's `README.md`: `hexdist` (the local
criterion and the closed form of `lem:krows`), `rust_torsion` (the unique word
of finite order), `paper4_ball12` (the depth-12 census, the `66 + 66` split and
the 6078) and `paper4_strata` (the `d*`/`delta` table, the stratum translation
census to depth 18, and the leg scan that locates non-generic leg samples).

## Sampling

Rational leg samples that look generic need not be: for `m = 3` the legs
`(1,2)` give the right triangle with angles `pi/6, pi/3, pi/2`, and for `m = 5`
the legs `(2,3)` produce 22 coincidences at length 14 that other samples do
not. Every stratum computation reported in the paper was repeated at three leg
samples.

## Scope

The configuration enumeration on the cylinder is exhaustive only in the range
stated in the paper (word length at most 14, cross-checked against exact
breadth-first search). It undercounts at greater lengths and is not used for
any claim beyond that range; the census values come from `rust_strat/`.
