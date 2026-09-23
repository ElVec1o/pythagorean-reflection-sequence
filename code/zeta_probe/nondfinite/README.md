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
