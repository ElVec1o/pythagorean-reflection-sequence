# mod-p crossing engine + CRT reconstruction (v2.12.35)

## Why
The exact-rational engine (`beta2_crossing_engine.py`) scales as **NEPS^7** in time and, worse,
its coefficients become thousand-digit rationals, so it is **OOM-killed** above ~order 25.
Measured: NEPS=48 -> 12s, 64 -> 56s, 80 -> ~90s, 92 -> 709s; extrapolating, order 40 (NEPS=160)
would need ~9.5 h and far more RAM than available. Three launch attempts at order 40 died
(twice from my own launcher errors -- `ulimit -v` kills python on macOS, and `nohup &` detaches
from the harness -- and once silently from memory).

## What
`engine_modp.py p order` runs the **entire three-stage crossing calculus over F_p** (stage 1
Faulhaber/c_n, stage 2 exp + D-actions, stage 3 weight-graded Newton + m-solve + reversion) and
prints A_1..A_order mod p. All coefficients are machine integers, so there is no rational blowup.

**Validated**: reproduces the known exact A_1..A_8 mod p = 2^61-1 exactly.

**Timing** (single prime): order 10 -> 1.7s, 14 -> 7.8s, 18 -> 25.4s, 22 -> 67.4s.
Fitted **t ~ order^4.66**; extrapolated order 30 -> 4.8 min, order 40 -> 18.2 min, order 50 -> 52 min.
That is a large improvement over the exact engine and, crucially, it does not OOM.

`crt_driver.py order kmax` runs the engine over successive 62-bit primes, CRTs the residues, and
**rationally reconstructs** each A_n (half-gcd style), accepting only when the reconstruction is
**stable** against dropping one prime.

## Note on the float variant
`engine_float.py` (mpmath) was also built and is *not* trustworthy: the graded-ring cleanup relies
on exact zero detection (`if r[k]==0: del r[k]`), which never fires in floating point, so roundoff
terms accumulate. It agrees with the exact A_1..A_9 to 1e-26 and then fails identically at A_10
regardless of the order computed -- a systematic bug, not a weight-cutoff effect. Use mod-p + CRT.

## Purpose
The only remaining compute-bound front is the **Gevrey class / Borel singularity** of the crossing
series (v2.12.29 showed the sequence is pre-asymptotic at n=22 and the singularity is undetermined).
More exact coefficients is the one thing that could decide it without a new idea.
