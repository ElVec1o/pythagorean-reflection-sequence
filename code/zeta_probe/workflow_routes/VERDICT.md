# beta2 / rationality assault — multi-agent verdict (2026-06-13)

Four independent routes (workflow beta2-rationality-assault), all over the 43 exact terms.

## Rigorous negatives (exact, positive-control-validated on Fibonacci/Catalan)
- NO constant-coefficient linear recurrence of order <= 21.
- NO holonomic recurrence within (order+1)(deg+1) <= 32.
- NO algebraic P(x,F)=0 with deg_F <= 6, deg_x <= 14 (29 cells, margins 7..34, all full rank).

## beta_2
- beta_2 = 1.4995 +/- 0.001 (~3 sig figs). Error is NOT a single geometric term
  (convergence rate oscillates in sign) -> naive Aitken/Shanks/Wynn lock onto a
  spurious 1.5208 and must be DISCARDED; robust windowed estimators cluster at 1.4993.
- 3/2 lies ~0.0007 from the median, inside the bar: consistent but NOT confirmed.
  PSLQ/identify (deg<=4, height 1e6) and 1+2cos(2pi/k) find nothing at this precision.
- Closing the gap needs MORE exact terms (convergence ~O(1/n)), not better accelerators.

## Proof route (the only one that could prove, not just fail to refute)
- Catalytic-variable functional equation: transfer operator over bounded interface
  profiles with the current edge's crossing count as the single catalytic variable t;
  eliminate profiles -> Pol(x,t,F(x,t),F_1..F_k)=0 -> algebraic by Bousquet-Melou--Jehanne.
- SHAKIEST STEP: the no-isolated-cycle (Eulerian connectivity) constraint is GLOBAL,
  not per-site; a bounded local encoding is supported by the census (components<=7)
  but not proven. This is exactly the term the relaxed DP undercounts (+2/cycle).

## Code caveat (FIXED/ANNOTATED)
- closure mode in fire_rust used an UNSOUND alphabet bound |a|<=2C+6: drops reachable
  within-cap states (deposits up to 30-32 survive), so it would match early terms then
  silently print a false "RATIONAL" verdict. NO paper result uses it. Now annotated
  unsound in the source; conclusions rest only on the exact-term guessers.
