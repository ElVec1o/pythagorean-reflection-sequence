# `zeta_toy_growth/`: the toy groups `Z[zeta^{+-1}] x| Z` (paper 1, Section 8)

Sphere sizes of the toy group `H = M x|_zeta Z`, `M = Z[t, 1/t]/(c t^2 - e t + c)`,
in the generators `a` (translation by 1) and `r` (the shift, multiplication by
`zeta`). These are the toy groups of `rem:WT-numerics`(d) and the Baumslag-Solitar
calibration of `rem:BS-calibration` in `paper/journal/paper1.tex`. `(c,e) = (5,6)`
is the rotation number of the `(1,2)` triangle; `(2,1)` is the laboratory shape.

| File | What it is |
|---|---|
| `src/main.rs` | The breadth-first search. Exact integer arithmetic in two independent encodings (`basis`: `(A + B zeta)/c^s`; `gauss`: `(u + v i)/5^m`, only for `c = 5`), `i128` with an overflow check that aborts rather than wraps; memory guard inside the tool. A `fast` mode uses the Klein-orbit symmetry; mode `lin` is a control family, `Z[1/ce] x|_{e/c} Z` (for `c = 1` this is `BS(1,e)`). |
| `analysis.py` | Post-processing: the growth series of `Z wr Z` in the same generators from its length formula, the first deviation of each toy sequence from it, and the calibration against `BS(1,2)` (rational growth, Collins-Edjvet-Gill). Small arithmetic only. |
| `runs/` | Output. `seq_c5e6.txt`, `fast_c5e6*.txt` and `seq_c2e1.txt`, `fast_c2e1*.txt` are the two sequences printed in `rem:WT-numerics`(d); `lin_*.txt` are the linear calibration runs, `lin_c1e2.txt` being `BS(1,2)`; `zwrz.txt` is the `Z wr Z` series; `test_*.txt`, `ctrl_*.txt` and `v1_*.txt` are encoding cross-checks and controls. |

Unlike `../wt_growth`, these counts are exact, not modular lower bounds.

Build and run:

```bash
cargo build --release
./target/release/zeta_toy_growth <c> <e> <dmax> <cap_mb> <outfile> [basis|gauss|lin] [fast [passes]]
(cd runs && python3 ../analysis.py)   # needs sympy; imports ../../wt_growth/guess.py
```
