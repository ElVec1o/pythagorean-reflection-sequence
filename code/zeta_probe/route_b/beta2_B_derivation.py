#!/usr/bin/env python3
"""v2.12.16: B = 1309/4050 DERIVED -- the beta_2 family law now has TWO proved rational orders.

THE LAW:  1 - q*_j = (2/mu_j) (1 - (8/9)/mu_j + (1309/4050)/mu_j^2 + O(mu_j^{-3})).

DERIVATION (one more order of the uniform operator calculus of v2.12.15):
 - exact prefactor: 2(1-eps)e^{eps/2} = 2 - eps - (3/4)eps^2 - (5/24)eps^3 - ...
 - c3(k) = -k^3/9 - k^2/12 + 17k/72   [the m^3-terms CANCEL in its defining sum:
   a3 - a1a2 + a1^3/3 = m(2-m)/24 -- same leading -k^3/9 as c2]
 - c4(k) = k^5/450 + O(k^4)           [bracket m^4-coefficient: 1/120 - 1/48 - 1/72
   + 1/24 - 1/64 = -1/2880; times Sum m^4 ~ 32k^5/5]
 - (1/2)c2(D)^2 = D^6/162 + D^5/108 + (lower)
 - D-actions on cos u (D = (u/2)d/du): D^5: sin-lead -u^5/32; D^6: sin-lead -15u^5/64,
   cos-lead -u^6/64; D^9 sin-lead -u^9/512.
 - THE SUBTLETY: at order eps^6 u^9, the CUBE (1/6)(c2(D)eps^2)^3 contributes
   +u^9/2239488 sin u via D^9, cancelling delta^3/6 of the cosine expansion IDENTICALLY.
   Truncating the exponential before the cube leaves a spurious m^5-term that shifts B
   by +2*32/1119744 = 5.7e-5 -- exactly the discrepancy that exposed it.
 - crossing equation: m - eps m^2/36 - eps^2[m^2/36 + m/4 + 17 m^3/32400]
   = 2 - eps - (3/4)eps^2   (m = eps*mu)
   => m = 2 - (8/9)eps - (1891/8100)eps^2
   => B = 2 m2 + 64/81 = -1891/4050 + 3200/4050 = 1309/4050.

CONFIRMATION: free five-order fit on the 30 computed roots:
  A = -0.8888888888888889 (17 digits of -8/9), B = 0.3232098765429447 vs
  1309/4050 = 0.3232098765432099 -- 13-DIGIT AGREEMENT; (A,B)-constrained fit
  out-of-sample residual < 4e-16. Next constant measured: C = -0.474535704766...
  (not an obvious small rational; awaits the same treatment, one more order).
"""
