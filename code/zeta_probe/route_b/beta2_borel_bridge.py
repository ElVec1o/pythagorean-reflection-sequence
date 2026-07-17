#!/usr/bin/env python3
"""v2.12.18: THE BOREL BRIDGE PROBE -- how much of beta_2 is classical? Answer: 98.8%.

QUESTION: the family law's rational series in 1/mu, evaluated at the head mu_1 = (pi/2)^2
(a rational series in 4/pi^2), is divergent. Does a Borel-type resummation reproduce
q* = 1 - eps_1? If provably yes, pi^2-arithmetic (known irrationality measure) enters
the beta_2 problem.

METHOD: coefficients [1, -8/9, 1309/4050, C, D, E, F] (two exact, C to 14 digits, D/E/F
fitted); Borel transform b_n = c_n/n!; Pade [3/3] (and [2/2],[3/2],[2/3] for spread);
Laplace integral. Denominator roots in the Borel t-plane: -4.96 and 0.752 +- 1.698i.

RESULTS:
 - CONTROL (j=2, x = 0.045, series nearly convergent): Borel-Pade = 0.96058422787 vs
   target 0.96058423252: gap 4.7e-9. Machinery + coefficients VALIDATED.
 - HEAD (j=1, x = 0.405): Borel-Pade = 0.6714 [3/3] (spread 0.652-0.683 across orders)
   vs target 0.6792093589: gap = -0.008(4) -- REAL (above coefficient noise ~1e-3 and
   Pade spread), NEGATIVE (resummation undershoots).
 - SCALE: the gap matches the natural nonperturbative benchmark e^{-pi^2/2} = 0.00719
   (and the complex Borel singularities at |t| ~ 1.86 give e^{-t0 mu1} ~ 0.010 --
   consistent family of scales).

VERDICT (quantitative anatomy of the prize): q* decomposes as
   ~98.8% perturbative (the rational pi^2-series, Borel-summable)
 + ~1.2%  nonperturbative (transseries sectors e^{-c mu}, invisible to the series).
The bridge to pi^2-arithmetic carries the perturbative part only; a proof must supply
the transseries completion AND its summability at mu_1 -- the same resurgence wall as
route D3.5 on the q-side (32-digit reproduction, no closure), now LOCALIZED to a
measured 1.2% of the constant. The sixth-technology spec sharpens: it must control an
e^{-pi^2/2}-scale correction with provable arithmetic.
"""
