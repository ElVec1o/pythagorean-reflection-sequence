# `rj_certificates/`: interval certificates for the junction pairing (R-J)

This directory holds the computer-assisted parts of paper 2's Theorem `thm:RJ`
(closed form and positivity of the junction pairing `<lambda,R>`, i.e. `Pi_1` and
`Pi_q`, at the travel poles), the pole count that indexes those poles, and the
enumerators used to check the transfer model (M) (`thm:model`, Appendix
`app:M3prime`) against the group.

How they fit into `paper/journal/paper2.tex`: positivity of `Pi_1(q_m)` and
`Pi_q(q_m)` is **analytic** for every pole with `tau_m <= 5e-3` (from the gate
`|g_V t_1| <= 0.983`, `thm:star`), which covers all `m >= 7`. The poles
`q_1, ..., q_12` are covered by the interval certificate `r54b`. The two ranges
overlap on `m = 7..12`. Only infinitely many poles are needed for `thm:V` and
`thm:U`, and the analytic range supplies them. The certificate is needed only
for the statement "at every travel pole".

**Load-bearing in paper 2:** `r35rust/src/bin/r54b.rs` and `r39pole`. The other
Rust tools are supporting certificates from the (B-sharp) / `rho_1, rho_2` route
that `thm:RJ`'s closed form superseded. They are kept because they check the
same objects independently.

## Trust base

Every certificate below is **MPFR (through the `rug` crate) plus hand-written
interval code**. The interval type `I = [lo, hi]` and its operations use directed
rounding (lower endpoint rounded down, upper rounded up) and are written in each
tool's `main.rs`. The tools share the same core, copied between crates, not a
library. Series tails are bounded by explicit ratio or majorant estimates, stated
in the doc comments next to the code. Nothing here is formally verified.
Correctness rests on MPFR and on that interval code. The pole-count tiling in
`r39pole` was repaired after a first review found gaps of order `1e-77` between
cells. The repaired code was then rebuilt and re-run from current source by a
second reviewer.

The **`models/` scripts are power-series arithmetic only**: truncated
integer-coefficient series in `x` (and `Y` for symbolic `y`), built from the
model's block formulas. They do no enumeration and carry no interval bounds.
They are not certificates. Their output is compared against the Rust
enumerators.

## Build

Each tool is its own Cargo crate:

```bash
cd <crate> && cargo build --release
```

The crates using MPFR need `rug` (GMP/MPFR are built by `gmp-mpfr-sys` on first
build). `target/` is regenerable and is not stored.

The logs do not record the command lines. The arguments given below are
reconstructed from the working precision and truncation lengths the logs print.
They reproduce the logged `bits=` and `N=` values exactly.

## The certificates

### `r35rust/src/bin/r54b.rs`: positivity of `<lambda,R>` at `q_1..q_12` (load-bearing)

**What it proves.** At each pole `q_m` it first certifies the pole: `B(q)` has
opposite certified signs at the ends of a tiny enclosure of `q_m`. It then
encloses `t_1 = v^T (I - M_0)^{-1} u` by affine shooting in `beta`, with a
rigorous tail. From `t_1` it evaluates the closed form

`<lambda,R> = 2q(1+x)/(1-q) * (t_1 + (1+x)/(2x)) / (1 - g t_1)`, `x = sqrt(q)`,

at `y = 1` (`g = g_V = q/(1-q)`) and `y = q` (`g = g_U = q/(1-q^2)`). It
certifies `Q = t_1 + (1+x)/(2x) > 0` (`CERT_Q`), `1 - g t_1 > 0` (`CERT_D`) and
`<lambda,R> > 0` (`CERT_L`), for both `y`.

**Run** (binary `r54b` of package `r35cert`). The arguments are the pole file,
then `cfac,extra` with precision `bits = ceil(cfac/(1-q_m) + extra)`, then the
pole indices:

```bash
cd r35rust && cargo build --release
./target/release/r54b ../models/poles_40.json 8,200 1 2 3 4 5 8 9 10 11   # cert_b.log
./target/release/r54b ../models/poles_40.json 8,200 12 6 7                # cert_c.log
```

**Result.** `cert_b.log` and `cert_c.log` together cover `m = 1..12`. Every line
has `CERT_Q>0:true CERT_D>0:true CERT_L>0:true`. The largest case is `m = 12`:
5425 bits, about 106 s.

### `r39pole/`: the pole index (load-bearing)

**What it proves.** A certified zero count of
`B(q) = 1 - Sigma_1 = sum_k (-2(1-q))^k q^{k^2} / (q;q)_{2k}` on an interval. The
interval is tiled by dyadic cells. On each cell, `B` is a degree-`n` interval
Taylor polynomial plus Cauchy remainder bounds, with a majorant tail. The code
either excludes a zero or shows strict monotonicity together with a sign change.
Across the four runs, `[0, 0.9988]` holds **exactly 13 zeros**, each isolated in
its own cell. The right endpoint is taken as its binary64 value. This is what
makes `q_1, ..., q_12` the first twelve travel poles.

**Run.** The arguments are `lo hi prec_bits n div`, where `div` sets the initial
cell width `(1-a)/div`, rounded down to a power of 2:

```bash
cd r39pole && cargo build --release
./target/release/r39pole 0     0.1    256 40 8
./target/release/r39pole 0.1   0.5    256 40 8
./target/release/r39pole 0.5   0.985  256 40 8
./target/release/r39pole 0.985 0.9988 256 40 8
```

**Result.** `r39M_rerun.log` (the second reviewer's re-run) reports
`ROOTS: 0, 1, 3, 9`, for 13 in total.

### `r35rust/` (`src/main.rs`, binary `r35cert`): the (B-sharp) certificate (supporting)

**What it proves.** At the certified poles `q_m`, and for `y = 1` and `y = q`, it
encloses the ratios `rho_1, rho_2` of the (B-sharp) route and certifies
`1 + rho_1 > 0` and `1 + rho_2 > 0`. It also prints the inner products
`<L,R>`, `alpha` and their relative widths.

**Run.** The arguments are the pole file, then `cfac,extra` as above, then
`d0,d1` (the truncation `N` is chosen so that `q^N` is below
`10^-(d0 + d1/(1-q))`), then the pole indices:

```bash
cd r35rust && cargo build --release
./target/release/r35cert ../models/poles_40.json 10,400 60,0.6 2 3 4 5 6 7 8 9 10 11 12   # run2.log
```

**Result.** `run2.log` covers `m = 2..12`, with `1+rho1>0:true 1+rho2>0:true`
throughout. The run at `m = 12` takes 494 s and 1.9 GB RSS.

### `r43kneg/`: the `k < 0` sector pairing (supporting)

The same pipeline and arguments as `r35cert`, with the extra inner products
`Q_A = <R,w_A>` and `Q_D = <R,w_D>`, the ratios `rho_A, rho_D`, and the total
`Pi_tot = B(A+X) + AD/2`, certified positive (`CERTIFIED_POSITIVE`). Setting the
environment variable `YONLY=1` or `YONLY=q` restricts the run to one `y`.

```bash
cd r43kneg && cargo build --release
./target/release/r43kneg ../models/poles_40.json 10,400 60,0.6 <m ...>
```

### `r40/`: uniform bound and direct pole checks (supporting)

- `uniform <E0> <ncell> <which>` certifies the uniform lower bound `Z > 0` (and
  the companion bounds `A_S`, `Y`) on `eps = 1-q` in `(0, E0]`, split into
  `ncell` cells.
- `poles <m_lo> <m_hi>` certifies `Z > 0`, `D != 0`, `1 - g t_1 > 0` and
  `S != 0` directly at the poles `m = 1..13`. The certified count cells are taken
  from `r39pole`.

The precision in bits is the second argument:
`./target/release/r40cert <mode> <prec> ...`.

### `r47/`: constants of the auxiliary mode sum (supporting)

`r47cert c0 <m1> <m2>` encloses `C0'(m) = sum_{n != m} |mu_mn|` with a rigorous
tail for `n > N`, and checks the maximum against `0.063512`. `r47cert eta4 <M...>`
evaluates the `eta4` constant `c(M)` against `5.95`. `r47cert xcheck`
cross-checks the `Cin` series against its asymptotic envelope. The precision is
fixed at 256 bits.

### `r50/`: uniform bounds on `|rho_1|` and `eps * Gammahat` (supporting)

`r50cert [m1]` (default `m1 = 200`) certifies by adaptive box bisection that
`B < 0.265` for `m = 7..m1` and `eps*Gammahat < 0.01548` for `m = 10..m1`. It also
certifies a continuous tail box covering every `m > m1`. The precision is fixed
at 128 bits.

## The model enumerators (exact integer arithmetic, no MPFR)

### `mnk/`: group BFS and defect census

This is a genuine geodesic BFS of `W_univ` on the normal form, with the defect
`c_true = (l_T - l_R)/2` computed from two independent minimisations, never from
`l_T = l_R + 2c`. Its modes are `selftest`, `validate <depth> [lam_max]`,
`enum`, `ucount <d> [full]`, `ctrue`, `ksplit` and `mn`. `ucount` prints the
sector-split counts `U n` and the check of `l_T - l_R - 2 c_pred`. This is the
enumeration behind paper 2's BFS evidence (`sec:bridge`): exact agreement to
`x^26` at `y = q`, to `x^22` at `y = q^2`, 816 coefficients at symbolic `y`
(`l_T <= 31`, `5.03e6` elements), and `v_0..v_19` certified.

```bash
cd mnk && cargo build --release && ./target/release/mnk ucount <depth> full
```

### `revO/`: direct tuple enumerator

`revo <n>` enumerates the normal-form tuples `(k, eps, delta, d)` directly from
the Lean definitions (`CorrectedSpan.lRTrue`, `cTrue`), not through the BFS. It
prints `E sign l_R c count`, an independent check on `mnk` and on the model
series.

```bash
cd revO && cargo build --release && ./target/release/revo <n>
```

### `models/`

| File | What it is |
|---|---|
| `model55.py` | The `k != 0` sectors of the corrected model: truncated integer power series in `x`. |
| `w0.py` | The `k = 0` sector block model, in `q = x^2`. |
| `biv.py` | The bivariate model at symbolic `y = x^2 Y`, truncated exactly at `x^D`. |
| `cmp.py` | Compares a model series (`.npy`) against the `BIV` lines of an enumerator log. |
| `chk.py` | An mpmath sanity check at the poles. It imports `jp_lib` from the parent directory and reads `../r35rust/poles_40.json`, so fix that path to `models/poles_40.json` before running it. |
| `poles_40.json` | The first 40 travel poles `q_m` to high precision, as `[m, "q_m", error]`. It is the input of `r35cert`, `r43kneg` and `r54b`. |

## Logs

| Log | Tool | Content |
|---|---|---|
| `cert_b.log` | `r54b` | `m = 1..5, 8..11` |
| `cert_c.log` | `r54b` | `m = 12, 6, 7` |
| `r39M_rerun.log` | `r39pole` | the four-interval zero count, 13 zeros on `[0, 0.9988]` |
| `run2.log` | `r35cert` | `rho_1, rho_2` at `m = 2..12` |
