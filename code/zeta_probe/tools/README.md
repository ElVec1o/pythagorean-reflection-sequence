# Computational tools

Rust (rug/MPFR) and Python backends for the five papers. Source only: the
`target/` build directories are regenerable and are not stored here. Builds work
in place even when the project path contains a space (`rug` 1.24, GMP and MPFR
all compile there).

```
cd <tool> && cargo build --release && ./target/release/<tool> ...
```

`runcap.sh` runs a command under a hard RSS ceiling and a wall-clock timeout.
macOS supplies no working address-space rlimit, so this wrapper supplies the
missing ceiling from outside. Use it for anything with a memory risk.

## Paper 2: certificates cited by name

| dir | what it computes |
|---|---|
| `t2abs_iv/` | The verified enclosure of the rectangle bound of `lem:T2abs`. Branch and bound over boxes in `(w, X)` with rug/MPFR and outward directed rounding on every operation; contour integrals are enclosed cellwise, so the output bounds the integral rather than estimating it. Initial boxes are cut at the half-integer steps of `sigma*` so no box straddles a contour jump. `./target/release/t2abs_iv scan <wmax> [prec] [threads]`, or `point <w>`. This tool covers `tau` in `[2/wmax^2, 0.02]`; the smaller range is the analytic lemma in `../t2abs_smalltau.py`. See its own `README.md`. |
| `sitecost/` | Exact verification of the local site-cost law (M1) and of the gap-run cycle count (M2, the shield law) of paper 2 section 5. All integer arithmetic, no floating point. Also the certificate that refutes the earlier marker clause. See its own `README.md`. |
| `u_modp_rust/` | `u_n mod p` via the validated catalytic transfer (1-D collapse, std-only, parallel). `./target/release/u_modp N P WORKDIR`. Data in `work130/`, `work180/` (p=3) and `work130p5/` (p=5). Python analyses: `structure_probe.py` (p-kernel, subword complexity, square gap), `mahler_algebraicity.py` (Frobenius/Mahler test), `bulk_modp.py`, `theta_telescope.py`, `reduction_verify.py`. |
| `pkernel/` | `p`-kernel census of a mod-`p` sequence with an explicit support threshold. By Eilenberg's theorem the sequence is `p`-automatic iff the kernel is finite, so kernel growth is the evidence against automaticity. |

## Paper 1: finite-horizon exclusions

| dir | what it computes |
|---|---|
| `norec/` | Farkas certificates that `u_0..u_38` satisfies no linear recurrence of order at most 19 (`prop:no-recurrence`). |
| `nodfinite/` | Rank certificates for `prop:no-dfinite`. `gen_lean_data.sh` and `emit_lean.sh` generate `lean/with_mathlib/NoDFiniteData.lean`, which regenerates byte-identically. |
| `shape_arith/` | The four numerical claims of paper 1 that an audit found wrong, checked exactly. The corrected statements are also proved in `lean/with_mathlib/ShapeArith.lean`, so they do not rest on this search. |

## paper_orthoscheme

| dir | what it computes |
|---|---|
| `ortho_len6/` | Exhaustive census of the short kernel elements of `rho_a`, the certificate for `thm:len6`. Exact integer homogeneous matrices, no floating point. `./target/release/ortho_len6 <n> <L> [--quiet]`. `sweep.sh` runs the published sweep. |
| `ortho_cd/` | Orbit growth of the orthoscheme reflection group against the right-angled Coxeter envelope, in `F_p`. Independently written from `ortho_len6` and cross-checked element for element against it. |
| `racg_envelope/` | Certification of the rationality of the envelope and of the growth rate `r_n = 1 + 2 cos(2 pi/(n+3))`. |

## Other Rust tools

| dir | what it computes |
|---|---|
| `u5b_gate/` | The U-gate verifier (rug). Per travel pole `m`: `tau`, `t1/tau`, `gatemargin/tau`, `boundC`, `R/tau^{5/2}`, `\|sin w\|`, and the in-Rust Neville extraction of the bedrock series to `gate.csv.scoeffs.txt`. `./target/release/u5b_gate --max 200 --out gate.csv`. Python: `hunt_coeffs.py`, `hunt_s1.py`. |
| `u5b/` | Earlier reflection-constant and McMahon-phase tool (rug), plus the confluence-grind Python history (`d32_*`, `d33_*`, `borel_*`, `derive_ck.py`) and the Borel/Gevrey JSON coefficient data. That route is closed; the files are kept as the record of what was tried. |
| `t1series/` | `t1 = P12/S_e` gate-series rational-coefficient extractor (rug and `rug::rational`). |

## Paper 4 (triangle reflection groups)

Cited by name in `paper/journal/paper4.tex`. The statement-to-script index for
the rest of that paper is `code/triangle_relations/README.md`.

| dir | what it computes |
|---|---|
| `hexdist/` | The local criterion behind `lem:krows`: builds `X` from the site lattice, checks `|dhat(v)-dhat(w)| <= 1` across all 47526 directed vertex-neighbour incidences of the window `|n|,|j| <= 44`, checks that every vertex but `e` has a descending neighbour, and compares the closed form of `k` against breadth-first search at all 14641 sites with `|n|,|j| <= 60`. |
| `rust_torsion/` | The unique word of finite order in `W_m = D_m * C_2` among the `c^2` words `w_{a,b}`, for `3 <= m <= 60` and `1 <= c <= m-1`. Independent check of `Bridge.unique_finite_order`. |
| `paper4_ball12/` | `thm:census` and `rem:twelve` at depth 12: the growth `1,3,...,3039,6012`, the 33 coincidences at length 11, the 132 at length 12 split `66 + 66`, and the 6078 distinct images of the 6144 reduced words of length 12. Three witnesses `(1/3,1/2)`, `(2/7,3/5)`, `(-1/3,1/2)`, two primes. Run: `./target/release/paper4_ball12 [prime_seed ...]`. |
| `paper4_strata/` | (A) the table of `d*(m)` and `delta(m)` against the Coxeter series `W_m(t)` for `2 <= m <= 12`, with the depth-12 deficits; (B) the stratum translation census by word length to depth 18, at six leg samples. Run: `./target/release/paper4_strata [prime_seed ...]`. The leg scan of `rem:cylcensus-status` is `./target/release/paper4_strata scan <m> 18 8`. |
| `strat_ident/` | The identification counts of the stratum section, recomputed from the geometry. Those counts are leg-sample dependent rather than stratum invariants, which is what this tool establishes. |

Both `paper4_*` tools are exact in `F_p` with `p = 1 mod 55440`, so `F_p` holds a
square root of `-1` and a primitive `2m`-th root of unity for every `m <= 12`.
Reduction mod `p` can only identify elements distinct in characteristic zero, so
printed counts of distinct images are lower bounds for the characteristic-zero
counts; see the Reproducibility paragraph of paper 4. Both run at two primes and
must agree.

## verify_scripts/

The `mpmath` verification scripts for the amplitude and confluence work. That
route is closed and superseded by the gate of `app:star`; the scripts are kept
because the identities they check are still used.

`theta_poisson.py` (the modular Poisson lemma, 25-digit), `casoratian.py`,
`casoratian2.py` and `amplitude_elem.py` (the conserved Casoratian, the exact
G-identity and the envelope), `qbessel_order.py`, `qbessel_order2.py`,
`uniformity.py` and `uniformity2.py` (q-Bessel to classical confluence at
order tau), `qlaplace_correct.py` (the correct q-Laplace convolution against a
discredited earlier form), `phi11_order.py`.

Illustrative runs use nome `q`; the gate object has nome `q^2`.
