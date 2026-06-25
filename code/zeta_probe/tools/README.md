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
