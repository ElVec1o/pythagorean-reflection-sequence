# kernel-and-breakthrough — multi-agent verdict (2026-06-13, round 2)

## Route A — relaxed (drop-connectivity) lamp model
- Relaxed sequence v_0..v_32 computed (determinized counting DP, validated vs BFS).
  v_n = u_n through n=7, then v_n > u_n (+2-per-isolated-cycle relaxation).
- RIGOROUS: v_n >= u_n termwise => relaxed growth rate r >= beta_2.
- r = beta_2 HEURISTICALLY (ratio sequences share limit; connectivity changes only
  the subexponential prefactor). r is NOT a nice algebraic number; 3/2 in band, unconfirmed.
- Kernel NOT completed: bulk f=0 sub-rate determinized (rho=0.7255, sub-rate 1.378) but
  travel edges f=+-1 and the geometric k-sum not folded in.

## Route B — connectivity lemma  (MAJOR: corrected a false paper claim)
- REFUTED the literal "components <= 7": family g_n=(deposit 2n at edge 0) has geodesic
  (R_y R_h R_x)^{2n} length 6n forcing n+1 open components (linear growth). The census
  bound was a radius-14 artifact.
- CORRECTED LEMMA (true, near-proof): each interface component carries <=1 up-crossing,
  <=1 down-crossing per edge => 8-shape alphabet; catalytic variable = bulk multiplicity.
  Strand-bounded DP matches metric with 0 mismatches to radius 12; local-exchange check
  0 violations / 14,658 interfaces (inductive step via Euler-trail reversal surgery).
  => the BMJ algebraicity route SURVIVES with the correct bounded encoding.

## Route C — literature
- Parry 1992 (Growth series of some wreath products): wreath products in TSP/tour-cost
  generating sets have IRRATIONAL ALGEBRAIC growth series. Our metric IS such a tour-cost.
  => literature PREDICTS our F is algebraic-not-rational; our negatives are the expected
  signature, not evidence against algebraicity.
- Rationality is generating-set-dependent (Stoll 1996 Heisenberg; standard lamplighter
  rate is phi=1.618, NOT 3/2). 3/2 is a genuinely new constant, likely a nontrivial
  algebraic number near 3/2.

## Route D — holistic breakthrough
- THE REFRAME: map zeta -> generic group / <<w_zeta>>; kernel = principal ideal
  2(t-1)mu_zeta Z[t]; n_zeta = ceil(L_zeta/2) = lamplighter shortest-vector length.
  Extends to ANY algebraic leg ratio, graded by height/Mahler measure of mu_zeta.
  A height-graded FAMILY theorem, bigger than one sequence. (Outlook remark added.)
- n_T is NOT linear in (c,e) (fails (2,3):174 vs 138, (3,4):328 vs 234) => genuine
  shortest-vector problem with cancellation, ~ Mahler measure not naive height.
- beta_2: data-limited; do not pursue without ~100+ more exact terms (needs the grammar).

## PAPER ACTIONS TAKEN
- Removed false "components <= 7"; replaced with refutation witness + corrected 8-shape lemma.
- Added Parry/Stoll backing: algebraic-not-rational is the EXPECTED literature verdict.
- Conjecture retitled "Algebraic growth"; BMJ route stated with the corrected encoding.
- Added height-graded-family outlook remark (Route D), flagged as direction not theorem.
- Strengthened Prop already had order<=21, algebraic deg_F<=6/deg_x<=14, beta_2=1.4995+-0.001.
