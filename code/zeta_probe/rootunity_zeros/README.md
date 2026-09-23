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
