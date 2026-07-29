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

`stratum_fields.py` holds the exact number fields `Q(2cos(pi/m))(sin(pi/m))`
and the stratum generators used by several of the above.

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
