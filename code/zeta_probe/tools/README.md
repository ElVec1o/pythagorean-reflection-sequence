# Computational tools — zeta_probe / route-B (A396406 transcendence)

Rust (rug/MPFR) and Python backends for the U/V transcendence work in
`../route_b/`. Source only — the `target/` build dirs are regenerable and are
**not** stored here. Builds work in place despite the space in the project path
(tested: `rug` 1.24 / GMP / MPFR compile fine):

```
cd <tool> && cargo build --release && ./target/release/<tool> ...
```

## Rust tools

| dir | what it computes |
|---|---|
| `u5b_gate/` | The U-gate verifier (rug). Per travel pole `m`: `tau`, `t1/tau`→¼, `gatemargin/tau`→¾, `boundC`→3.714, `R/tau^{5/2}`, `\|sin w\|`, and the in-Rust Neville extraction of the bedrock series `c2 = R/(tau^{5/2} sin w) = C + s1 tau + ...` to `gate.csv.scoeffs.txt`. Run: `./target/release/u5b_gate --max 200 --out gate.csv`. Python: `hunt_coeffs.py` (PSLQ / holonomic-recurrence / Borel attacks on the s_k), `hunt_s1.py`. |
| `u_modp_rust/` | `u_n mod p` via the validated catalytic transfer (1-D collapse, std-only, parallel). Run: `./target/release/u_modp N P WORKDIR`. Data in `work130/`, `work180/` (p=3), `work130p5/` (p=5). Python analyses: `structure_probe.py` (p-kernel / subword complexity / square-gap), `mahler_algebraicity.py` (Frobenius/Mahler test), `bulk_modp.py` (bulk block mod p), `theta_telescope.py` (verified θ-telescoping), `reduction_verify.py` (F(q,1)=Ψ/(1−Ψ_odd)). |
| `u5b/` | Earlier reflection-constant / McMahon-phase tool (rug) + the full confluence-grind Python history (`d32_*`, `d33_*`, `borel_*`, `derive_ck.py`, …) and Borel/Gevrey JSON coefficient data. |
| `t1series/` | t1 = P12/Se gate-series rational-coefficient extractor (rug + rug::rational). |

## Paper 4 (triangle reflection groups)

Cited by name in `paper/journal/paper4.tex`. The statement-to-script index for
the rest of that paper is `code/triangle_relations/README.md`.

| dir | what it computes |
|---|---|
| `hexdist/` | The local criterion behind `lem:krows`: builds `X` from the site lattice, checks `|dhat(v)-dhat(w)| <= 1` across all 47526 directed vertex-neighbour incidences of the window `|n|,|j| <= 44`, checks that every vertex but `e` has a descending neighbour, and compares the closed form of `k` against breadth-first search at all 14641 sites with `|n|,|j| <= 60`. |
| `rust_torsion/` | The unique word of finite order in `W_m = D_m * C_2` among the `c^2` words `w_{a,b}`, for `3 <= m <= 60` and `1 <= c <= m-1`. Independent check of `Bridge.unique_finite_order`. |
| `paper4_ball12/` | `thm:census` and `rem:twelve` at depth 12: the growth `1,3,...,3039,6012`, the 33 coincidences at length 11, the 132 at length 12 split `66 + 66`, and the 6078 distinct images of the 6144 reduced words of length 12. Three witnesses `(1/3,1/2)`, `(2/7,3/5)`, `(-1/3,1/2)`, two primes. Run: `./target/release/paper4_ball12 [prime_seed ...]`. |
| `paper4_strata/` | (A) the table of `d*(m)` and `delta(m)` against the Coxeter series `W_m(t)` for `2 <= m <= 12`, with the depth-12 deficits; (B) the stratum translation census by word length to depth 18, at six leg samples. Run: `./target/release/paper4_strata [prime_seed ...]`. The leg scan of `rem:cylcensus-status` is `./target/release/paper4_strata scan <m> 18 8`. |

Both `paper4_*` tools are exact in `F_p` with `p = 1 mod 55440`, so `F_p` holds a
square root of `-1` and a primitive `2m`-th root of unity for every `m <= 12`.
Reduction mod `p` can only identify elements distinct in characteristic zero, so
printed counts of distinct images are lower bounds for the characteristic-zero
counts; see the Reproducibility paragraph of paper 4. Both run at two primes and
must agree.

## verify_scripts/

The `mpmath` verification scripts cited in `../route_b/amplitude_bound.tex`
`[checked]` remarks and elsewhere:
`theta_poisson.py` (Lemma kappa Poisson, 25-digit), `casoratian.py` /
`casoratian2.py` / `amplitude_elem.py` (Lemma caso: conserved Casoratian +
exact G-identity + envelope), `qbessel_order.py` / `qbessel_order2.py` /
`uniformity.py` / `uniformity2.py` (q-Bessel → classical confluence, O(τ)),
`qlaplace_correct.py` (correct q-Laplace convolution vs the discredited "T6c"),
`phi11_order.py`. (Illustrative runs use nome `q`; the gate object has nome `q²`
— see the amplitude-bound section's note.)
