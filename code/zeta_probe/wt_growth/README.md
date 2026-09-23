# `wt_growth/`: the rational triangle groups `W_T` (paper 1, Section 8)

Computations behind `sec:rational-WT` of `paper/journal/paper1.tex`. A right
triangle `T` with rational legs is encoded by `(c, e)`, the minimal polynomial
`mu_T = c t^2 - e t + c` of its rotation number; the `(1,2)` triangle is
`(5,-6)`, the `(2,7)` triangle is `(53,-90)`, and `c = 2, 3, 4` give laboratory
shapes with the same algebraic structure.

| File | What it is |
|---|---|
| `src/main.rs` (`wt_growth`) | Sphere sizes `u_d^T`. The linear part is stored exactly, the translation modulo a prime `p < 2^58`. Reduction mod `p` can identify distinct elements but never separate equal ones, so every printed value is a **lower bound** for the true count. Run at two primes. Memory guard inside the tool. |
| `src/bin/wt_carry.rs` (`wt_carry`) | The carry-window computation in the obstruction paragraph after `conj:WT-nonDfinite` (carry width `floor((d-12)/2)` for `d <= 32` at `(c,e) = (2,1)`): BFS of the universal ball in the lamp model, then the optimal carry `f` in `A_{h*} = A_h + 2 mu_T f` for every element. Exact (`i128` in `Z[1/c][zeta]`). |
| `kcheck/` | Builds the explicit out-and-back word of `rem:kappa`(b) with edge profile `2 sign cos(j theta)` and evaluates it geometrically (floating point); reports length over displacement. |
| `guess.py` | The modular rank computations of `thm:WT-lowcomplexity`: full rank modulo `2^61 - 1` implies full rank over `Q`, so an `EXCLUDED` verdict is a proof about the terms given. A `FIT` is only a candidate. |
| `analyze.py` | Summary of the runs: first deviation depth, deficits, ratios, and the `guess.py` exclusions. |
| `univ33.txt`, `univ39.txt`, `univ43.txt` | The universal terms `u_0 ..` used as reference (the last four of `univ43.txt` are the recovered terms, see `code/data/u_terms_43.txt`). |
| `ctrl_rat.txt`, `ctrl_alg.txt` | Positive controls for `guess.py` (a rational and an algebraic series). |
| `runs/` | Output, one file per `(c, e, prime)`; `runs/carry/` holds the `wt_carry` summaries. `runs/c53e-90_p0.txt` is `rem:WT-numerics`(c): the `(2,7)` triangle to depth 40, which reproduces `u_0 .. u_38` and gives `u_39 = 43997388`, `u_40 = 65932461` as lower bounds. `runs/c5e-6_p*.txt` is `rem:WT-numerics`(a). |
| `lab.sh`, `lab2.sh` | Sequential batch runners under `../runcap.sh` (RSS cap 3000 MB, 285 s wall). |

Status: the `W_T` layer values beyond the certified depth are lower bounds, not
certificates, and the exclusion searches run on them certify nothing about
`W_T` (paper 1 says so at each use). The carry-window law is verified, not
proved.

Build and run:

```bash
cargo build --release
./target/release/wt_growth <c> <e> <dmax> <prime_index> <cap_mb> <outfile>
./target/release/wt_carry  <c> <e> <D> <cap_mb> <outprefix>
(cd kcheck && cargo run --release -- <c> <e> <N>)
python3 analyze.py
```
