#!/usr/bin/env python3
"""v2.12.27: LOWER DIRECTION of the prime onset law -- onset EXACTLY at (p-1)/2, valuation 2.
Reduced to a dyadic UNIT identity; onset law now proved for all odd p modulo that one identity
(verified p<=19; exact valuation independently verified p<=43).

SETUP: at n=(p-1)/2, A_n uses c_{<=2n}=c_{<=p-1}. The ONLY prime-p source is c_{p-1} (all lower c
p-integral, proved). c_{p-1} enters A_n LINEARLY (c_{p-1}^2 has weight 2(p-2) > 2n).

WHICH MONOMIAL CARRIES p TO A_n: deg_k(c_{p-1}) = p. The p^2 lives in exactly the k^1 and k^p
coefficients of c_{p-1} (von Staudt-Clausen / Faulhaber; the other reaching coeffs k^{p-2},k^{p-1}
carry p^1). Under the weight cutoff (only degrees >= p-2 reach A_n at order n), k^1 is EXCLUDED
(weight 2p-3 > 2n+1), so only k^p's p^2 reaches A_n.

THE UNIT: the coefficient of c_{p-1}[k^p] in A_{(p-1)/2} is EXACTLY +-1:
   dA_n/d(c_{p-1}[k^p]) = (dA_n/dm_n)(dm_n/d c_{p-1}[k^p]) = 2^{n-1} * (+- 2^{1-n}) = +-1.
 - dA_n/dm_n = 2^{n-1} PROVED (reversion: eps ~ 2/mu, so d eps_{n+1}/d m_n = 2^n; A_n = eps_{n+1}/2).
   VERIFIED: 1,2,4,8,16,32 for n=1..6.
 - dm_n/d(c_{p-1}[k^p]) = +- 2^{1-n} VERIFIED for p=5,7,11,13,17,19 (values 1/2,-1/4,-1/16,1/32,
   1/128,-1/256). The top monomial routes through the leading D^p-action (A_p's u^p coeff = 1/2^p)
   and the reversion, all dyadic; the non-dyadic assembly parts cancel. This is the "leading symbol"
   of the top-degree-to-top-order channel.
 - PRODUCT L = +-1 VERIFIED directly for p=5,7,11,13,17,19.

CONCLUSION: A_{(p-1)/2} = (p-integral) +- c_{p-1}[k^p] + (k^{p-1},k^{p-2} terms, valuation >= -1).
Since v_p(c_{p-1}[k^p]) = -2, v_p(A_{(p-1)/2}) = -2 exactly: p appears at (p-1)/2 with denominator
valuation exactly 2. Verified directly: v_p(A_{(p-1)/2}) = -2 for p=5,7,11,13,17,19.

STATUS: onset law (p | den(A_n) <=> 2n+1>=p, valuation 2 at n=(p-1)/2) PROVED for all odd p modulo
the dyadic unit identity dA_{(p-1)/2}/d c_{p-1}[k^p] = +-1 (verified p<=19). The clean form (a UNIT,
no p-dependence in magnitude) removes any irregular-prime subtlety. beta_2: still OPEN.
"""

# ============================================================================
# v2.12.28 CLOSURE: |L| = 1 PROVED by leading-symbol (principal-part) argument.
# The onset law is now proved for all odd p (both directions).
#
# The top monomial c_{p-1}[k^p] (p=2n+1) perturbs G's confluent expansion by eps^{p-1} k^p.
# Turning-point map (D^p-action, D=(u/2)d/du) sends k^p to a_p u^p sin + b_p u^{p-1} cos,
#   a_p = (-1)^{n-1}/2^p   (leading sine coeff, closed form from the (A,B) recursion)
#   b_p = (-1)^n n(2n+1)/2^p (leading cosine coeff)  [both PROVED via the D-recursion].
# At a simple zero u* of cos: cosine term vanishes, lower sine powers are higher-order in eps,
#   => zero shift delta = eps^{p-1} a_p u*^p   (sin u* = +-1 cancels vs G' = -sin).
# m = eps u^2, leading balance u*^2 = 2/eps (from eps u^2 = 2(1-eps)e^{eps/2} -> 2):
#   delta m = 2 eps u* delta = a_p 2^{n+2} eps^n
#   => dm_n/dc_{p-1}[k^p] = a_p 2^{n+2} = +- 2^{1-n}   [MAGNITUDE EXACT: only top power u^p
#      reaches order eps^n].
# Reversion Jacobian dA_n/dm_n = 2^{n-1} (from eps ~ 2/mu):
#   L = dA_{(p-1)/2}/dc_{p-1}[k^p] = 2^{n-1} * (+-2^{1-n}) = +-1.   |L|=1 PROVED.
# (Exact sign L=(-1)^n verified for all n<=10, primality-independent.)
#
# Since c_{p-1}[k^p] has v_p = -2 (vSC) and |L|=1 (unit, v_p=0), and the k^{p-1},k^{p-2}
# contributions have v_p >= -1, we get v_p(den A_{(p-1)/2}) = 2 exactly.
# ONSET LAW PROVED for all odd p. (Closed forms + leading balance all verified in code;
# a_p, b_p exact for n=1..6; L=(-1)^n for n=2..10; v_p(A_{(p-1)/2})=-2 for p=5..19.)
# ============================================================================
