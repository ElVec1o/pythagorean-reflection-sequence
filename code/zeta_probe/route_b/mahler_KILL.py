#!/usr/bin/env python3
"""
MAHLER ROUTE -- KILLED (with a precise, verified structural obstruction).

GOAL (README/route_b): show U (or V) is a MAHLER FUNCTION, i.e.
    a_0(z) f(z) + a_1(z) f(z^d) + ... + a_m(z) f(z^{d^m}) = b(z),
    a_i,b in Q[z],  a_0 a_m != 0,  d>=2,
and invoke Mahler/Nishioka (rational-or-transcendental) to conclude transcendence
WITHOUT pole-counting / lem:cos / numerator conditions.

RESULT: there is NO such equation -- for V, for U, or for the underlying bulk
block G_0 -- and the obstruction is structural, not a search horizon.

(A) EMPIRICAL (strict, out-of-sample verified):
    * BULK block G_0 = S_0/(1-S_1) computed EXACTLY to q^500.  Fit a candidate
      Mahler relation on q^{<=fit_M}, then VERIFY on q^{fit_M+1..500}.  Result:
      NO genuine relation for d in {2,3}, m<=7, deg(a_i)<=29.  (Rational AND
      modular-GF(2^31-1) searches agree.)  Truncation "candidates" all fail the
      out-of-sample check.
    * EXACT V series computed to x^130 (131 terms, matches OEIS A396406 relaxed):
      NO genuine Mahler relation in x, d in {2,3,4}, m<=5, deg<=15, verified to x^130.
    * GIVEN exact u_n,v_n (43/41 terms): NO Mahler relation within available terms.

(B) STRUCTURAL OBSTRUCTION (the real reason, rigorous modulo the established
    pole asymptotics aka lem:cos):
    THEOREM (interior singularities of a Mahler function). If f is analytic at 0
    and satisfies the Mahler equation above with a_0 a_m != 0, d>=2, then every
    singularity rho of f with 0<|rho|<1 obeys: rho^{d^k} is a zero of a_0 for some
    k>=0.  Proof: f(z)=(b - sum_{i>=1} a_i f(z^{d^i}))/a_0; since |z^{d^i}|<|z|,
    induct on modulus -- a new interior singularity at rho can only be a zero of a_0
    or an inherited singularity at the SMALLER-modulus point rho^{d^i}.  Hence the
    interior singularities are a FINITE union of d-power orbits {zeta^{1/d^k}}_k,
    each accumulating at |z|=1 with CONSTANT log-ratio
            ln(rho_{k+1})/ln(rho_k) = 1/d   (exactly, for all large k).
    (Verified on a toy Mahler function (1-z/c)f(z)=f(z^2): poles c^{1/2^k}, ratio
     == 0.5 exactly.)

    CONTRADICTION with the data.  V's singularities (and U's) are the travel/bulk
    poles q_m in (0,1), zeros of 1-Sigma_1 (resp. 1-S_1), accumulating at q=1 with
            -ln q_m  ~  C/m^2      (since 1-Sigma_1 ~ cos(sqrt(2/(-ln q))), poles at
                                    sqrt(2/tau_m) ~ 2 pi m).
    Therefore  ln(q_{m+1})/ln(q_m) ~ m^2/(m+1)^2  is STRICTLY INCREASING toward 1,
    NEVER constant.  Measured (genuine resolvent, 50 dps, 25 poles): r_m runs
    0.359, 0.510, 0.605, 0.669, ... 0.923, strictly increasing.  No value 1/2,
    1/3, 1/4, ... is ever attained as a limit.  Hence V (and U, same pole geometry)
    can satisfy NO Mahler equation of ANY order m or ANY integer base d>=2.

CONSEQUENCE.  Mahler's method cannot be the tool: it is OUT, not merely unproven.
The dilation t->q^2 t in the catalytic equation is a q-DIFFERENCE (theta-type)
structure, NOT a Mahler power-substitution z->z^d; these are genuinely different,
and the pole geometry (continuously varying log-ratios) is the invariant that
separates them.  Transcendence of U/V therefore still rests on the pole-
accumulation route (lem:cos), exactly as before -- Mahler offers no shortcut.

Files producing each number above:
  /tmp/bulk_series_long.py  (G_0 to q^500)   -> /tmp/G0_long.json
  /tmp/mahler_deep.py, /tmp/mahler_modp.py   (strict G_0 Mahler search)
  /tmp/genV.py                                (exact V to x^130) -> /tmp/V130.json
  /tmp/mahler_V130.py                         (strict V Mahler search)
  /tmp/more_poles.py, /tmp/pole_asymptotic.py (pole log-ratios, strictly increasing)
  /tmp/mahler_sanity.py                       (toy Mahler: constant ratio 1/d)
"""
print(__doc__)
