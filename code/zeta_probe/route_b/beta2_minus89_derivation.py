#!/usr/bin/env python3
"""v2.12.15: THE -8/9 LAW DERIVED (uniform confluent asymptotics) + error #20.

DERIVATION. eps = 1-q. The log-ratio of term_k of G(1-eps, eps^2 y) to (-1)^k y^k/(2k)!
is (k/2) eps + c2(k) eps^2 + O(eps^3), with the EXACT quadratic coefficient
    c2(k) = -k^3/9 - k^2/12 + 23k/72
[from q^{k(k-1)} = (1-eps)^{k(k-1)} and (q;q)_{2k} = eps^{2k}(2k)! exp(Sum log(1-(i-1)eps/2 + ...))].

REGIME 1 (fixed j, eps -> 0): first order is the pure rescaling y -> y e^{eps/2}:
G ~ cos sqrt(y e^{eps/2}), so z_j = eps^2 mu_j (1 - eps/2 + O(eps^2)): fixed-j confluent
correction = -1/2. VERIFIED: c1_est = -0.5039, -0.5019, -0.5010, -0.5004 at
eps = 0.02, 0.01, 0.005, 0.002 (linear convergence to -1/2).

REGIME 2 (the crossing, mu*eps ~ 2 = O(1), k ~ sqrt(2/eps)): the k^3 term acts as the
operator -(eps^2/9) D^3, D = (u/2) d/du on cos u; at the zeros D^3 cos = (u^3/8) sin u
+ O(u^2), and EVEN powers of D are cos-weighted and vanish at the zeros -- parity
protects the order (this is why k^4 eps^3, formally the same size, does not contribute).
Crossing equation: 2(1-eps)e^{eps/2} = eps*mu*(1 - eps^2 mu/36): with m = eps*mu,
   m = 2 - eps + eps m^2/36 + O(eps^2)  =>  m = 2 - (8/9) eps:
   A = -1 + 1/9 = -8/9   [matches the 12-digit measurement].
Sine family: same -k^3/9 leading coefficient => same A = -8/9 (matches).

ERROR #20 (self-caught): v2.12.14 claimed A = -8/9 is "equivalent" to a fixed-j
confluent correction c1 = -5/9 via A = -2(1+c1). FALSE: that transfer is only valid
when the expansion is used at fixed j, but the crossing sits in the uniform regime
mu*eps = O(1) where the k^3-corrections contribute at the SAME order. The two regimes
carry DIFFERENT constants: -1/2 (fixed j, now derived AND verified) vs -8/9 (crossing,
now derived AND verified). Caught by carrying out the derivation the banked sentence
had skipped.

B = 0.3232098733 is within reach of the same operator calculus (one more order:
k^2-terms of c2, eps^3-terms c3(k), and the D-subleading corrections).
"""
