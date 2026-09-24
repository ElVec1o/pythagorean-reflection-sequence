# P1b (2026-09-24). Saved by the orchestrator because the seat's own file write was blocked.

## PROVED
- The phase law W_m = W_0 e(-inv(4p) m^2/q) for odd q, plus its even-q analogue. The proof uses a C-shift lemma and a periodicity lemma.
- The masks: odd m cancels when 4|q; even m cancels when q ≡ 2 mod 4.
- gcd(Y, theta) = 1, so |G| = sqrt(#live saddles), times sqrt2 for even N. G never vanishes.
- Re g0 = Im F/q^2, and Im F = 0 for even q.
- A drift lemma, which reduces the good-arc requirement (5) to a finite check.
- A characterisation of the degenerate points: 4|N and N l <= log 4.

## VERIFIED
- For N ≡ 2 mod 4 the asymptotic needs a twist factor. The sign of that factor is fixed by the numerics.
- For q <= 150: |Sigma_q| >= 0.9848 sqrt q, D1 <= 2.77, D2 <= 6.23.
- Interval certificate for l >= 0.02 at N <= 150, excluding the degenerate case 1/12.
- The 1/12 band: 2224 cases, checked in floating point only.
- Empirical error law for the asymptotic: c(p/q)|theta|/N.

## FALSE
- "|Sigma_N| >= c sqrt N uniformly in N". Near odd q there is exponential drift.
- The uniqueness claim for w in S0_lemma when 4|N and N l <= log 4.

## OPEN
- (1) A rigorous, uniform error bound for the multi-saddle asymptotic.
- (2) The inductive log-derivative step above level 150.
- The 1/12 band as an interval certificate rather than floating point.
