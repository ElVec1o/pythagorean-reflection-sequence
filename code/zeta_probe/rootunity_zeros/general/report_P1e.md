# P1e (2026-09-24). Persisted by the orchestrator. UNREVIEWED.

## Theorem M
PROVED, computer-assisted, resting on P1d's lemmas dec and lap.
- Statement: Z_N != 0 for all N and every a/N in [1/5, 4/5] (l >= 0.855), with |Z_N| >= 0.02 e^{-0.005N}.
- Method: hazard induction.
- Supporting lemmas:
  - Lemma A: direct bound.
  - Lemma H: handover.
  - Lemma B, B': deep and middle seeds.
- Certified pieces:
  - 18 low seeds.
  - Case A covering: 22,546 intervals.
  - Base case: N <= 150.
- Lemma B tail beyond n = 3000: analytic bound, written out but not machine-checked.

## Renormalisation
- Lemma R: PROVED. Seed amplitude = level-q Z_q.

## Obstruction
- Triangle-inequality Laplace bounds lose a factor Lambda ~ e^{0.008q} near drifted seeds.
- Theorem M therefore closes only for l > ~0.48.
- Below that, a "moment" induction hypothesis is needed (OPEN).

## Seed 1/11
- CERTIFIED, both sides, via a new outer-contour Lemma O.

## Still open for P1
- l in [0.05, 0.855).
- The zeros-of-B step near a general zeta.
- The transfer to U and V.
