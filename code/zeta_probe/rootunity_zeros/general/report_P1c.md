# P1c (2026-09-24). Report saved by the orchestrator.

## Results
- The 1/12 band is CERTIFIED with Arb ball arithmetic: all 2224 cases pass, 0 failures (P1c_band_arb.py).
- T_{r+N} = T_r: PROVED. Sigma_N is an exact cyclic sum.
- The error is err ≈ K(x)|x - p/q|. It does not depend on N, and K is bounded in q (VERIFIED in floating point).
- Seeds with q <= 12 cover l >= 0.107, with relative error <= 0.42 (VERIFIED in floating point).

## Reduction
The q <= 150 induction is no longer needed. It is enough to prove Lemma (1''):
- For each seed there is an explicit radius r and a bound B < 1 with |Sigma_N/Main - (±1)| <= B on the neighbourhood.
- This must hold for all N >= 151 and every residue class.

## Open
- Lemma (1'').
- The case of even N.
- The arc edge l < 0.107.
- Transferring the pole conclusion to U and V at a general zeta, i.e. the analogues of prop:minusone and prop:t1minusone.
