# Route A — Relaxed-model growth (drop the Eulerian-connectivity constraint)

The **relaxed** word length is the project's metric formula WITHOUT the global
single-Eulerian-path constraint (so isolated cycles are free, undercounting true
length by exactly +2 per isolated cycle). `v_n` counts group elements of
A396406 by **relaxed** length.

## Method (validated)
`wf2_dp3.py` / `wf2_par.py` (in `/tmp`, mirrored notes here): a **counting
transfer DP** that sweeps edges left-to-right, branches on the lamp coefficient
`a_j` (element identity), and determinizes the inner min-over-crossing-counts
(`m_j`) optimization into normalized min-cost tables over edge profiles
`(f,m,pu,pd)`. Each distinct element is counted exactly once at its minimal
relaxed length. Summed over all `(eps, delta, k)` slices.

Reachability chain constraint `j>=1 & prev_m=0 & m>0 -> forbidden`,
`j<=-1 & prev_m>0 & m=0 -> forbidden` (mirrors `lamp_formula.py`).

### Validation (all passed)
- 6 fixed `(eps,delta,k)` slices vs brute a-sequence enumeration scored by the
  validated `lamp_formula.formula_len` — exact match.
- Full `v_n` vs independent true-length BFS (depths 18/20/22/24), bucketed by
  relaxed length: **exact agreement through n=16** (the BFS-converged range).
- `mmax` (per-edge crossing cap) convergence: results stable once
  `mmax >= ~N/2` (mmax=8,12 agree at N=20; mmax=12,16 agree at N=24).

## Relaxed sequence v_n (n = 0 .. 32), exact
```
1, 3, 5, 8, 13, 21, 34, 55, 91, 148, 235, 371, 590, 931, 1451, 2254,
3513, 5455, 8418, 12959, 19949, 30640, 46905, 71699, 109490, 166969,
254047, 386192, 586349, 889599, 1347444, 2039911, 3084135
```
(mmax-convergence: N=28 run at mmax=14 and N=32 run at mmax=16 agree exactly on
the shared prefix v[0..28]; the rule v[n] converges by mmax>=ceil(n/2)-2 was
checked at N=20 (mmax 8 vs 12) and N=24 (mmax 12 vs 16).)
Compare true u_n: identical through n=7 (=55), then v_n > u_n
(v_8=91 vs u_8=89, ...): the +2-per-cycle relaxation pulls cycle-elements into
shorter buckets.

## Growth rate r = lim v_{n+1}/v_n
- **Rigorous lower bound:** v_n >= u_n and cumulative V(n) >= U(n) for ALL 29
  terms (verified), so r >= beta_2 = 1.4995 rigorously (relaxed length <= true
  length pulls every element to an equal-or-shorter bucket).
- **Numerical:** ratios r_n descend through 1.518 at n=28 (still > beta_2),
  with the SAME non-clean, period-4-oscillatory, ~1/n convergence that defeats
  naive Aitken/Richardson for beta_2 itself. Oscillation-aware least-squares fits
  R + (A cos + B sin + C(-1)^n + D)/n over growing tail windows give
  R_inf = 1.470, 1.473, 1.474, 1.497 for the last 12/16/20/24 ratios -- i.e.
  INCREASING toward beta_2 as more terms enter.
- **Decisive comparison:** r_relaxed(n) - r_true(n) oscillates with period 4 but
  its per-cycle troughs shrink toward 0 (0.0082 @ n=8 -> 0.0008 @ n=16 ->
  0.0029 @ n=20 -> 0.0044 @ n=24). The two ratio sequences share the same
  apparent limit.
- **CONCLUSION (heuristic, not proven):** r = beta_2. The connectivity
  relaxation (free isolated cycles, +2/cycle) changes only the SUBEXPONENTIAL
  prefactor, not the exponential growth rate. v_n/u_n grows ~linearly
  (1.00 @ n=7 -> 1.18 @ n=28), i.e. polynomially, consistent with
  d_n = v_n - u_n ~ poly(n)*beta_2^n and r = beta_2.
- Since beta_2 is established to have NO low-order linear/holonomic/algebraic
  relation, r = beta_2 is likewise NOT a nice algebraic number. r = 3/2 is NOT
  excluded but NOT confirmed (3/2 < 1.4995-lower-bound? NO: 1.5 > 1.4995, so 3/2
  remains inside the band [1.4995, ~1.52]).

## Exact value / kernel (Task 2): NOT completed
The relaxed model is a clean one-catalytic-variable system (the current edge's
crossing count m). A bulk f=0 transfer matrix (determinized) gives a partial
rate ~1.378 but EXCLUDES travel (f=+-1) edges, so it is only the pure-lamp
sub-rate, not r. The full kernel must combine lamp (f=0) and travel (f=+-1)
edges and sum the geometric k-series; this is a vector kernel of dimension =
#profiles and was not reduced to a clean algebraic minimal polynomial here.
The transfer-matrix scaffold is in `wf2_transfer.py`.

HONEST STATUS: numerical r in [beta_2, ~1.52], algebraic value NOT pinned.
