# Zeros of B near roots of unity (paper2a, prop:minusone)

`certify_landscape.py` is the interval-arithmetic certificate (mpmath.iv). It certifies the landscape inequalities on the box theta1 ± 0.001, |x_A| in [0.0495, 0.0505]. It runs in about 7 s.

`certify_landscape_alt.py` is the interval-arithmetic certificate for the alternating sums S_e, S_- (prop:t1minusone): it certifies the landscape on the same box. It runs in about 3 s.

Floating-point checks (not certified):
- `t1_minusone.py`: t1 -> phi at the zeros q*_j, S_e against its saddle asymptotic, the pairings Pi_q, Pi_1 (cor:Uminusone); `generic` checks P12 = -(S_e+S_-)/2 off the zeros.
- `pairing_complex_check.py`: <lambda,R> from truncated operators against the closed forms of thm:RJ at q*_3, q*_4.
- `z1.py`: zeros at zeta = -1 compared with the prediction.
- `zeros_rate.py`: the 80-digit zero rate.
- `chk.py`: the asymptotic formula across angles.
- `z2*.py`: the second ray.
- `zi.py`, `vi*.py`: the zeta = i case. This is heuristic.
- `rho*.py`: residue ratios for the rem:rootunity route.

Caution: evaluating B's series near q = -1 cancels badly. Below |t| of about 0.015 it needs more than 40 digits.

## zeta = i (Room I, 2026-09-24): partial result only
- The proof at q = -1 does NOT carry over to q = i. The dominant exponent on the ray is T = -0.0707 < 0, but the first term of B is b_0 = 1, so the bound on the initial terms of the sum fails whatever cutoff is used. B is small here only through massive cancellation.
- Two-saddle prediction: VERIFIED against root-finding, with error decaying like 1/j. Amplitude factors are 1 + phi i and 1 - i/phi. Script: `zi_twosaddle.py`.
- Obstruction demo: `zi_growth_obstruction.py`.
- Correction to the earlier heuristic: e^{-4x*} = +i(4 - sqrt15).
- A proof would need a closed contour crossing the negative s-axis, together with a reflection formula. This is open.
- Room J (2026-09-24): `ident.py` (contour identity, matches the series to 15 digits at r=0.2, 0.1), `sad.py` (the two saddles, height -0.0706856), `land_i.py` (finite-t landscape) were copied here from the scratchpad. `t1_i.py` is HEURISTIC: at the true zeros for j=5..40, t1 -> about 0.07-0.57i at rate O(t); 1-g_U t1, 1-g_V t1 and both pairing factors at both roots stay near 0.72, 0.75-0.31i, 0.92-0.92i / 0.21-0.21i, 0.37-0.52i / -0.24-0.61i. Nothing here is certified yet: steps (b), (L), (c), (R) and (T) are still open.
- Room J, steps (b) and (c) (2026-09-24): `qi_bounds.tex` contains Lemma lem:qi-bounds. It gives an Euler-Maclaurin formula for Re x >= 0 with an explicit O(|t|) constant, a theta-reflection upper bound for Re x <= 0, a tail bound and a kernel bound. `certify_landscape_i.py` (mpmath.iv, about 30 s, 31 MB) prints ALL CERTIFIED: every competing piece is <= T_LO - 0.1002, with T_LO = -0.072274. It uses the exact split B = J_0 + J_- + R_- + R_+ (VERIFIED to 14 digits at r = 0.2 and 0.1), and r0 = 1.56e-3. Steps (L), (R) and (T) are still open.
- Room J, steps (L), (R), (T) (2026-09-24), now in paper2a as §sec:qi (lem:qi-bounds condensed, prop:qi, cor:Ui; rem:polesdensity updated).
  PROVED: saddles x0, xm = x0 - i pi/2, y0 = x0 - i pi/4 in closed form, Phi_i'' = -sqrt15/2 at all three; dV = pi^2/8 - (3 pi i/4) log 2;
  A0 = (2/sqrt15)^{1/2} e^{i pi/8} e^{h+(x0)} (1+i phi), A- = ... (1 - i/phi), A-/A0 = e^{(1-i)pi/4} exactly; zeros predicted at
  t0_j = (6 log2 + i pi)/(16 j + 6 - 2i); Rouche gives exactly one simple zero in D_j = {|1/t - 1/t0_j| < 1/|dV|}, t*_j = t0_j + O(j^-3)
  (landscape hypotheses hold on D_j for j >= 285; the Laplace O(t) constant is from Olver, so j0 is NOT explicit).
  S_pm dominated by the single saddle y0 (nu = -1/2), amplitude factor 1 -+ e^{2 pi i/3}; t1 -> t1* = ((sqrt15-3) - (sqrt15+3) i)/12;
  1 - gU t1 -> ((21-sqrt15) - (sqrt15-3) i)/24, 1 - gV t1 -> 3/4 - (sqrt15/12) i; all pairing factors non-zero at x = +-e^{i pi/4}.
  CERTIFIED: `certify_landscape_i.py` (rerun, ALL CERTIFIED, 30 s) and new `certify_landscape_S_i.py` (ALL CERTIFIED, 21 s, margin 0.1066,
  r0 = 1.557e-3); `factors_i.py` (mpmath.iv: every limit factor non-zero; closed-form constants to 1e-50).
  VERIFIED (floating point): `amp_i.py` (B / two-saddle sum - 1 = O(t), 0.0064+0.0043i at r = 0.01), `t1lim_i.py` (S_pm asymptotics O(t)),
  `zeros_i.py` (|t*_j - t0_j| j^3 ~ 0.0065 for j = 1..80; t1 -> t1*), `ident_S_i.py` (sin-kernel contour identity, r = 0.2, 1e-41),
  `pairing_check_i.py` (closed forms thm:RJ at q*_1, q*_2 near i, rel <= 1.3e-33). Conclusion (standing thm:model, thm:RJ): poles of U, V
  accumulate at x = +-e^{+-i pi/4}.
