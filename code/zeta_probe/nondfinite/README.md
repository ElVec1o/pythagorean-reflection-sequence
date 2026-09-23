# Scripts behind paper2 §8, "Beyond transcendence"

These scripts back the numerical remarks in §8: the non-D-finite theorem, the natural boundary, and the poles of U and V at -x_m.
They are floating-point checks at mpmath 40-90 digits. None of them is an interval certificate.

| File | What it computes |
|---|---|
| `A1_probe_minus_x.py` | t_1 and the junction brackets at x = ±sqrt(q_m) for m = 1..12. This is the data behind rem:Vminusx. |
| `ev.py` | Evaluates B and S_e. |
| `argcount*.py` | Zero counts by the argument principle. |
| `roots*.py` | Zeros of B, S_e and D_U. |
| `pi.py` | Pi_q, t_1, Sigma_0 and S_e at the complex zeros of B. |
| `anal.py` | Angular gaps and the directions in which the zeros approach roots of unity (rem:polesdensity). |
| `gate*.py` | Zeros of D_U, D_V and S_e. |
| `rootunity_check.py` | Root-of-unity case of prop:noqdiff (rem:rootunity). At m = 1..20 it computes the residue ratios rho_m for U and V at -x_m against x_m, and g, S_e, D_U, D_V at w*q_m for w a primitive cube or fifth root of unity. |
| `rootunity_minus.py` | S_e, D_U and D_V at -q_m, at up to 1550 digits. The cancellation there is about 2*log10 g(-q_m) digits. |
| `rootunity_fit.py` | Degree-bounded test of the Q=-1 relation. It gives the smallest singular value of the system A0(x_m) = rho_m A1(x_m), m <= 20, for deg <= 9. |
