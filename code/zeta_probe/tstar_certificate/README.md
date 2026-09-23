# tstar_certificate: interval certificate for (T*_poles)

This folder holds the computer-assisted step of paper2b, Theorem `thm:Tstar`
(`paper/journal/paper2b.tex`, section `sec:spectral`).

## Statement

Let `1/2 < q < 1` and `alpha = 2q(1-q)`. Let `R != 0` be a real `l^1` vector with `T(q) R = R`, and
put `u = K R`. Define `e1` and `e2` as in Lemma `lem:HF`. Then

    e1 + e2 >= (5/4) (2q-1)/(1-q).

The paper proves this in four steps:

- Step 0: the leapfrog recursion.
- Step 1: the flux identity `e1 + e2 = 2 <s>_f`.
- Step 2: the amplitude bound `max F / min F <= R(q)`.
- Step 3: the mean bound `e1 + e2 >= Phi_K(q)`.

Here

    c      = q sqrt((1-q)/2)
    dbar   = (1-q) c / (1-c)
    R(q)   = exp(c/((1-c)(1-dbar))) (1+c) / (q (1-c))
    g(s)   = q^s / (R - (R-1) q^s)
    Phi_K  = 2 sum_{s=1..K} g(s) + 2 log(R / (R - (R-1) q^(K+1))) / ((R-1) log(1/q))

This folder does Step 4. It checks, in interval arithmetic, that the explicit bound beats the
right-hand side.

- `tstar_certificate.py` checks `Phi_30(q) - 1.25 (2q-1)/(1-q) > 0` on `[1/2, 1 - 1e-6]`. It uses 770
  consecutive boxes, from 0.5 to 0.9999990026, with a geometric mesh of width
  `min(0.002, (1-x)/50)`. A box that fails is bisected up to 8 times. The result is 0 failures.
  This is the script written in room 32 (Tao seat, file `cert2.py`), copied verbatim. Its first
  output line is a plain floating-point grid scan, not part of the certificate. It prints the
  minimum of `Phi_30 / RHS`, which is 1.336 near `q = 0.781`. Against `1.25 * RHS` that minimum is
  1.069, so the margin is about 6.9%.
- `tstar_endpoint.py` covers `[1 - 1e-6, 1)`. It uses the cruder bound `g(s) >= q^s / R` (valid
  since `R >= 1`), which gives `e1 + e2 >= 2q / (R (1-q))`. It checks `2q/R - 1.25 (2q-1) > 0` on
  the closed box `[0.999999, 1]`. The enclosures are `R` in `[1, 1.0021251]` and margin
  `>= 0.745756`. This is Reviewer C's repair 3 from room 32.

## Trust base

The trust base is `mpmath.iv` interval arithmetic: 30 digits, outward rounding. Nothing here is
formally verified. The derivation of `Phi_K` (Steps 0-3) is in the paper. The following Lean 4 files
under `lean/with_mathlib/` machine-check the algebraic and amplitude pieces:

- `TstarCore.lean`: `sbp` and `drift`.
- `TstarAmplitude.lean`: `amgm`, `G_bounds`, `drift`, `step`, `log_step`, `log_tele` and
  `log_ratio`.
- `RoomB34.lean`: `leapfrog_ne`, `G_F'_compare` and `G_pos`.

All of them use only the axioms `propext`, `Classical.choice` and `Quot.sound`, with no `sorry` and
no `native_decide` (re-checked 2026-09-23 with `lake env lean`, toolchain v4.30.0). Steps 0 and 3,
the `N -> infinity` limits, and this interval step are not formalised.

Tested with Python 3.12 and mpmath 1.3.0.

## Run

Wrap every run in a time limit and an RSS cap:

```bash
cd code/zeta_probe/tstar_certificate
../tools/runcap.sh 3000 290 perl -e 'alarm 290; exec @ARGV' python3 tstar_certificate.py   # ~7 s
../tools/runcap.sh 3000 290 perl -e 'alarm 290; exec @ARGV' python3 tstar_endpoint.py      # <1 s
```

Expected output, recorded in `run.log` and `run_endpoint.log` (2026-09-23; peak RSS 27 MB):

```
min ratio on grid (mpf('1.336008760127757...'), mpf('0.78115'))
intervals 770 failures 0 [] last 0.999999002614282811097149180736
...
endpoint [1-1e-6, 1]: PASS (margin lower end 0.745756865554677...)
```

## Numerical cross-check (not part of the certificate)

At the second travel pole `q_2 = 0.913486638731...`, the leapfrog recursion from `u_0 = 1` gives the
following values (60 digits, 4000 terms):

- `e1 + e2 = 20.5072`;
- `(2q-1)/(1-q) = 9.5589`, so the ratio is 2.145;
- `sum q^s p^2 / (alpha sum q^s u^2) = 1` to all digits.

At the negative control `q = 0.9`, which is not a pole, that last quotient is 0.865. The flux identity
fails there, as it must, because `u_s` does not tend to 0.
