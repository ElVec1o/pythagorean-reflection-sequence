# P1d (2026-09-24). Report persisted by the orchestrator.

## Lemma (1'') is FALSE (Prop 6)
Deep rationals near the seed drift Sigma_N/Main to 0 or to infinity.
- (i) PROVED, computer-assisted, at 2/21 and at 18/53.
- (iii) The general statement is HEURISTIC.
- The P1c reduction therefore FAILS, and the continued-fraction induction is needed after all.

## PROVED
- **Theorem 1:** exact factorisation Sigma_N = G*_N e^{-Phi(eps)} Z_N, with |G*| = sqrt N (odd N) or sqrt 2N (even N). This covers N ≡ 2 mod 4.
- **Conjugation symmetry.**
- **Theorem 2:** a single-saddle main term with error K|d|, where K does not depend on N.
- **Theorem 5 (corrected Lemma 1''-Delta):** holds under a deep-rational tail hypothesis, which is automatic for N <= N* >= 1e10.
  - Certified for 21 of the 22 seeds with q <= 12.
  - Radii are small, between 1.7e-5 and 8e-3.
  - 1/11 fails.

## OPEN
- The induction over deeper seeds. It needs:
  - error bounds uniform in q;
  - level-n nonvanishing S_amp(j/n) != 0;
  - a handover between the p/q and j/n descriptions.
- The covering itself.
