# beta2 certificate: certified finite algebraic exclusion for q* and beta2

This folder holds the certificate for paper2, Proposition `prop:finiteexcl`
(`paper/journal/paper2.tex`).

- `q*` is the least positive zero of
  `S(q) = sum_k (-1)^k q^{k(k-1)} (2q(1-q))^k / (q;q)_{2k}`, so `q* = 0.4494536305...`.
- `beta2 = 1/sqrt(q*) = 1.4916177871...`.

## Statement

Let `P` be a nonzero integer polynomial with height `H(P) = max |coefficient|`.

- If `P(q*) = 0`:
  - `deg P <= 8` forces `H(P) >= 10^230`;
  - `deg P <= 16` forces `H(P) >= 10^120`;
  - `deg P <= 24` forces `H(P) >= 10^80`;
  - `deg P <= 64` forces `H(P) >= 10^28`.
- If `P(beta2) = 0`:
  - `deg P <= 8` forces `H(P) >= 10^228`;
  - `deg P <= 16` forces `H(P) >= 10^118`.

The result is computer-assisted and finite. It proves nothing about irrationality or transcendence.
A PSLQ "no relation" output is heuristic. It is not a certificate, and it is not used here.

## Method

**Step 1 (`step1_bracket.py`): certified bracket.** Interval arithmetic
(`mpmath.iv`, outward rounding) re-derives steps (i)-(iii) of paper2 `prop:effective`:

- (i) `S > 0` on `[0, 0.40]` (400 chunks);
- (ii) `S' <= -1` on `[0.40, 0.46]` (600 chunks), so `S` has at most one zero there;
- (iii) `S(a) > 0 > S(b)` for `a = (A-2)/10^2090` and `b = (A+2)/10^2090`, where `A` is the
  2090-digit truncation of `q*`. The working precision is 2130 digits and the series tail is enclosed
  in `+-1e-2125`.

Together these give `q* in [a, b]`, of width `4e-2090`. The script then outward-rounds a bracket for
`beta2` to `[m_lo, m_hi] / 10^2080` with `m_hi - m_lo = 5`. It checks the bracket exactly, as the
integer inequalities `m_lo^2 (A+2) <= 10^(2*2080+2090) <= m_hi^2 (A-2)`. The output is
`bracket.txt`, six integers: `A-2`, `A+2`, `2090`, `m_lo`, `m_hi`, `2080`.

The Newton bootstrap that locates `q*` is plain floating point. It only chooses `A`, and nothing
depends on it being accurate: step (iii) certifies the bracket.

The functions `S_iv_wide` and `Sp_iv` are vendored verbatim from
`code/zeta_probe/beta2_effective_irrationality.py`, so the script is self-contained.

**Step 2 (`step2_lattice.py`): lattice exclusion.** Let `x*` lie in the bracket `[c, c+w]`. Let `R`
bound `|x|` on the bracket (`R = 1` for `q*`, `R = 3/2` for `beta2`), and let `M = floor(1/w)`.

1. `L_d` is the lattice in `Z^{d+2}` with basis rows `e_i + floor(M c^i) e_{d+1}`, for `0 <= i <= d`.
2. A polynomial `P` of degree at most `d` with `P(x*) = 0` gives a nonzero lattice vector of norm at
   most `H(P) * K_d`, where `K_d^2 = (d+1) + (s_d + d + 1)^2` and `s_d = sum_{i=1..d} i R^{i-1}`.
3. The script LLL-reduces the basis (`python-flint`, `delta = 0.99`). LLL is used only to find a good
   basis. The script verifies exactly that the output equals `T * B` with `|det T| = 1`, so it is a
   basis of the same lattice.
4. It computes the Gram-Schmidt norms exactly, as `||b_k*||^2 = Delta_k / Delta_{k-1}`, where
   `Delta_k` are the leading principal minors of the integer Gram matrix (exact rationals).
5. Every nonzero lattice vector has norm at least `min_k ||b_k*||`. So no such `P` exists with
   `H(P) < min_k ||b_k*|| / K_d`. The script prints `log10` of that quantity as
   `certified log10 H_max`.

## Trust base

- `mpmath.iv` interval arithmetic with outward rounding (step 1).
- Exact integer arithmetic in `python-flint` (`fmpz_mat`: product, determinant) and Python
  integers and `fractions.Fraction` (step 2, and the integer checks at the end of step 1).

LLL itself is not trusted: its output is checked. There are no floating-point decisions in step 2.
The only floating point there is the `log10` used to print the result.

Tested with Python 3.12, mpmath 1.3.0 and python-flint 0.8.0.

## Run

Run from this folder, because `bracket.txt` is read from and written to the current directory. Wrap
every run in a time limit.

```
perl -e 'alarm 290; exec @ARGV' python3 step1_bracket.py        # about 10 s; rewrites bracket.txt
perl -e 'alarm 290; exec @ARGV' python3 step2_lattice.py q 8
perl -e 'alarm 290; exec @ARGV' python3 step2_lattice.py q 16
perl -e 'alarm 290; exec @ARGV' python3 step2_lattice.py q 24
perl -e 'alarm 290; exec @ARGV' python3 step2_lattice.py q 64   # about 30 s
perl -e 'alarm 290; exec @ARGV' python3 step2_lattice.py beta 8
perl -e 'alarm 290; exec @ARGV' python3 step2_lattice.py beta 16
perl -e 'alarm 290; exec @ARGV' python3 step2_lattice.py ctl 2  # negative control
```

To check that `bracket.txt` reproduces without overwriting the shipped copy, run step 1 from an
empty directory, then compare with `cmp`.

The first argument of step 2 is `q`, `beta` or `ctl`. The second is the degree bound `d`.

## Results (reproduced 2026-09-23)

`step1_bracket.py`: (i) True, (ii) True, (iii) True, and the Newton residual is `3.5e-2112`. The
`beta2` bracket width is 5 units of `1e-2080`. The regenerated `bracket.txt` is byte-identical to
the shipped one (sha256 `01cd1686...6569cd2`).

| target | d  | certified log10 H_max | stated bound (height below) | LLL + GS time |
|--------|----|-----------------------|-----------------------------|---------------|
| q*     | 8  | 230.45                | 10^230                      | < 1 s         |
| q*     | 16 | 120.63                | 10^120                      | < 1 s         |
| q*     | 24 | 80.90                 | 10^80                       | about 1 s     |
| q*     | 64 | 28.29                 | 10^28                       | about 27 s    |
| beta2  | 8  | 228.66                | 10^228                      | < 1 s         |
| beta2  | 16 | 118.15                | 10^118                      | < 1 s         |
| sqrt2-1 (control) | 2 | -0.30      | none (correctly fails)      | < 1 s         |

- **Control.** `sqrt(2) - 1` is a root of `x^2 + 2x - 1`, which has height 2. The certified bound is
  below 1, so the control excludes nothing, as it must.
- **Consistency.** At `d = 1` the procedure gives `log10 H_max = 1043.99` for `q*`. This agrees with
  paper2 `prop:effective`, which shows that `q*` is not `s/t` for any `t <= 10^1044`, by the
  Stern-Brocot argument on the same bracket.
- **Unrun degrees.** An earlier session ran degrees 96 and 128 before the unimodularity check was
  added. Those runs are not part of this certificate and are not claimed.
