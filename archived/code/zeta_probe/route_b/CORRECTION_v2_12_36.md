# CORRECTION (v2.12.36): corrupted coefficient cache, and the corrected order-30 analysis

## The bug
The capping experiments used for the order-2n dependence test (`engine2_cap.py`/`engine2_bump.py`
with `CMAX`, which ZERO OUT c_m above a cutoff) invoke `engine3.py`, which **overwrites
`engine_result.pkl`**. A capped run therefore poisoned the coefficient cache. Every analysis that
subsequently read that pickle used A_10..A_22 that were wrong (A_10 off by exactly 1; A_11 onward
off by ~100%).

## What was and was not affected
- **The PUBLISHED coefficients are CORRECT.** The v2.12.16 values (e.g. A_10 =
  -20282885490082104937825859655435316307/37819675051478554374858217500000000) match the new
  independent mod-p reconstruction EXACTLY. Papers quoting A_1..A_4 are unaffected.
- **The ONSET LAW survives and is now better verified.** It is a statement about denominators;
  re-checked on the corrected A_1..A_30 it holds for every odd prime through **p = 59**
  (onset n = 29), extending the previous verification range of p <= 43. Theorem intact.
- **v2.12.29 (Gevrey / Borel geometry) was run on the corrupted cache** and its numbers are
  superseded by the corrected analysis below.
- The symmetric-branch tower (v2.12.32), denominator-radius identity (v2.12.33) and Hermite-Pade
  work (v2.12.34) use the u_k lattice, not the A_n, and are unaffected.

## Ground truth
The corrected values were confirmed against the 105-digit root data by extracting A_n directly
from the accumulation law: A_10 extracts to -536.33 -> -536.305 (new) vs -535.305 (corrupt);
A_11 to -706.19 -> -706.384 (new) vs -20008.6 (corrupt); A_12 to 5709.9 -> 5708.43 (new) vs
3.5e7 (corrupt).

## Corrected order-30 analysis (A_1..A_30, mod-p CRT, root-verified)
- **Gevrey class: still undetermined.** log|A_n|/(n log n) rises 0.313 (n=14) -> 0.411 (n=30),
  monotone but far from 1 (Gevrey-1) or 2 (Gevrey-2).
- **Borel singularity: now coherent but not converged.** With corrupted data the Pade estimate
  wandered chaotically (|t| = 2.28, 0.0067, 0.034, 0.083, ...). With correct data it is monotone:
  |t| = 2.61, 2.56, 2.96, 3.09, 3.33 for Pade[6/6]..[14/14]. A 3-term (conjugate-pair) recurrence
  gives |t0| = 3.285, 3.394, 3.493, 3.558 and arg(t0) = 60.8, 61.7, 62.4, 62.3 degrees at
  n0 = 22, 25, 28, 30 -- both still drifting upward.
- **Sign pattern:** approximately period-6 (three +, three -) from n ~ 12 onward, consistent with a
  complex conjugate pair near arg 60-62 degrees, but NOT exactly periodic over the whole range
  (there is a run of four -1 at n = 8..11), so arg = pi/3 exactly is NOT established.

## Net
The corrected data gives a coherent singularity picture (conjugate pair, |t0| ~ 3.3-3.6,
arg ~ 62 deg) where the corrupted data gave noise -- but nothing is converged at n=30, so the
Gevrey class and hence Borel summability remain OPEN, as v2.12.29 concluded. Deciding them needs
order ~50+, which the mod-p engine now makes reachable (~52 min/prime, parallelizable).
