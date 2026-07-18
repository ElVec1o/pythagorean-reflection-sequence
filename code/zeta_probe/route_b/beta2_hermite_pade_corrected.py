#!/usr/bin/env python3
"""v2.12.34: Hermite-Pade for beta_2, CORRECTED -- and then shown logically insufficient.
Two errors of mine fixed; a scaling law derived; a logical flaw caught before it became a claim.

ERROR 1 FIXED (wrong functions). The earlier attempt (v2.12.30) used u_1,u_2,u_3,u_4 as the
approximating system. That is meaningless for irrationality: u_2(q*), u_3(q*) are UNKNOWN
quantities, so the linear form does not evaluate to a rational at q*. The correct system uses
POWERS OF u_1: since u_1(q*) = 2q*(1-q*) is a POLYNOMIAL in q*, the form
    L = sum_{k<=m} P_k(q) u_1(q)^k = O(q^V)
evaluates at q* to Pi(q*) with Pi(X) = sum P_k(X)(2X(1-X))^k an explicit integer polynomial of
degree <= N + 2m.

ERROR 2 FIXED (no size control). The earlier attempt took an arbitrary nullspace vector, so the
"coefficient explosion" measured there was an artifact of the basis, not of the construction. With
V = unk-1 the kernel is 1-dimensional and LLL has nothing to reduce (verified: logH_LLL = logH_raw
in every such case). The Siegel setup requires V < unk-1, buying kernel dimension, then reducing.

MEASURED (Siegel-optimized, LLL over kernels of dim 2..9): the margin still WORSENS with m --
best margins +3.916 (m=2), +5.516 (m=3), +7.178 (m=4). Mechanism: each added power of u_1 costs
DEGREE 2 in Pi, hence a factor t^2 in the denominator (2 log t = 1.599 per power), while gaining
only theta(N+1)|log(q*/R)| = 0.210 theta (N+1) in the error exponent. Near-balanced -- the
exactness principle in yet another guise.

SCALING LAW (asymptotic, Siegel bound assumed achievable):
    margin = logH + V log(q*/R) + (N+2m) log t,   V = theta(m+1)(N+1),
    logH ~ [theta/(1-theta)](V log(1/R) + m log max|u_1|).
Scanning: positive for all accessible (m,N); turns negative only around m ~ 100, N ~ 250
(margin -27.7), strongly negative at m=200, N=500. That would need ~25000 unknowns, an LLL on a
~20000-dimensional lattice, and u_1 to order ~4000 -- out of reach here.

THE LOGICAL FLAW (why the scaling law is NOT a path, independent of feasibility). Under the
assumption q* = s/t, the construction yields |Pi(q*)| < t^{-(N+2m)}, forcing Pi(q*) = 0, i.e. q*
is a ROOT of Pi -- i.e. q* is ALGEBRAIC. That is IMPLIED BY rationality, not contradictory to it:
if q* = s/t then (tX - s) | Pi is perfectly consistent. So no contradiction arises however
negative the margin becomes. A supplementary non-vanishing/irreducibility argument (showing the
constructed Pi is not divisible by tX - s) would be required, and none is available since s,t are
unknown.
CONTRAST (why the truncation ledger IS logically sound): there D_N(s/t) = 0 for CONSECUTIVE N
forces d_{N+1} = 0 and hence D polynomial, contradicting non-algebraicity of u_1. Hermite-Pade has
no consecutive-N handle, because Pi varies unsystematically with (m,N).

NET: the corrected construction is the right formulation and the scaling law is arithmetically
correct, but the approach cannot prove irrationality as posed. Recorded so the next person does not
walk the same path. beta_2 OPEN.
"""
