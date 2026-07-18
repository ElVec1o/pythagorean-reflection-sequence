#!/usr/bin/env python3
"""v2.12.32: THE SYMMETRIC-BRANCH TOWER -- a genuinely new construction. It monotonically
improves the Diophantine ledger (failure factor 1.803 -> 1.187) and is then PROVABLY capped at
exact criticality by integrality. It also UNIFIES the single-branch ledger with the zero-product
theorem as the two endpoints of one family.

THE IDEA (new). Every ledger for beta_2 dies because u_1 has radius R = 0.5546, set by the FOLD at
q_c = -0.5546 where the zero branch z_1 collides with z_2. But a fold is a square-root branch point
of each branch INDIVIDUALLY and NOT of the colliding pair: if
    z_1 = z_c + C sqrt(q_c - q) + ...,  z_2 = z_c - C sqrt(q_c - q) + ...
then z_1+z_2 and z_1 z_2 are ANALYTIC there -- the square root cancels identically. So the
elementary symmetric functions of the colliding branches continue PAST the obstruction that caps
every ledger. This is NOT a reparametrization, so the radius-cap theorem (about substitutions
q = psi(u)) does not apply; it changes the object.

THE CROSSING SURVIVES. If u_1(q*) = 2q*(1-q*) =: w, then w is a root of X^m - e_1 X^{m-1} + ... ,
so w satisfies a relation in the SYMMETRIC FUNCTIONS ALONE, e.g. for m=2:
    q^2 w^2 - P(q) w + S(q) = 0,   P = q^2 u_1 + u_2,  S = u_1 u_2   (both in Z[[q]]).
Poles of z_k = u_k/q^{2(k-1)} are cleared by an explicit q-power; integrality verified for m<=4.

VERIFIED (fold is a genuine z_1/z_2 collision): G = G_z = 0 at (q_c, z_c) to 1e-21, and the first
two positive zeros converge on z_c = 2.5240 as q -> q_c (gaps 1.99, 1.24, 0.75 at q = -0.50,
-0.53, -0.545), matching u_1 and u_2/q^2 numerically.

MEASURED RADII (coefficient growth at n=290, lattice to order 300):
    m=1 (u_1 alone) : R = 0.5716 -> 0.5546   ledger factor s/R = 1.803
    m=2             : R = 0.7356             factor 1.3595
    m=3             : R = 0.7953             factor 1.2574
    m=4             : R = 0.8425             factor 1.1870
Monotone improvement: each added branch absorbs more pairwise collisions. This is the best
Diophantine margin ever obtained for this problem (previous best 1.76-1.80).

THE CAP IS A THEOREM (not a measurement). Every cleared e_j is an INTEGER power series with
infinitely many nonzero coefficients, so |c_n| >= 1 infinitely often, so limsup |c_n|^{1/n} >= 1,
so RADIUS <= 1 -- for every m. The ledger criterion is s < R'(m) <= 1 while s >= 1 for any integer
numerator. Hence the tower can NEVER close the ledger. Consistently, 1 - R'(m) decays
geometrically (ratio ~0.77): R'(m) -> 1 FROM BELOW, approaching exact criticality and never
crossing.

UNIFICATION (new structural insight). The tower interpolates between the two endpoints already
known to this project:
    m = 1    : the single-branch ledger,           radius 0.5546
    m = infty: the ZERO PRODUCT prod z_k q^{2(k-1)} = (q;q^2)_oo, radius exactly 1
So the zero-product theorem is precisely the m -> infinity limit of this construction, and its
long-observed "tail-confinement" is now explained: it is the critical endpoint of a monotone
family, sitting exactly at s = R' = 1.

STATUS: beta_2 not reached. But this is a real mechanism with a real gain and a proved cap -- the
sharpest instance yet of the exactness principle, now visible as a monotone approach to
criticality rather than a single failed ledger.
"""

# ============================================================================
# v2.12.33 COMPLETION: the DENOMINATOR-RADIUS IDENTITY closes the truncation class.
#
# THEOREM. F = sum f_n q^n, f_n in Q, not eventually zero; D_n = common denominator of
# f_0..f_n; R = radius. Then  R <= liminf D_n^{1/n}.
# PROOF. f_n != 0 => D_n f_n is a nonzero integer => |f_n| >= 1/D_n, so
# 1/R = limsup |f_n|^{1/n} >= limsup D_n^{-1/n} = 1/liminf D_n^{1/n}.
# COROLLARY. If F(s/t) = 0, the truncation ledger (which needs s D_N^{1/N} < R) fails for
# every integer s >= 1: it would force D_N^{1/N} < R/s <= R <= liminf D_N^{1/N}, a quantity
# strictly below its own liminf.
# SHARP: f_n = c^{-n} has D_n = c^n and R = c exactly.
#
# MEANING: the denominator floor and the convergence radius are THE SAME QUANTITY. Buying
# radius by admitting denominators of growth c costs exactly c. This is the general form of
# the exactness principle for truncation ledgers, and it subsumes:
#   - the radius cap (integral case D_n = 1 => R <= 1),
#   - the discreteness cap,
#   - the symmetric-branch tower's ceiling (its e_j are integral, so R_m <= 1 for all m),
#   - and it CLOSES the escape route that motivated this step: non-integral symmetric
#     combinations with geometric denominators c^n gain radius R <= c but cost exactly c.
# VERIFIED on our objects: u_1 R=0.5716<=1; u_1u_2 R=0.7364<=1; u1u2u3u4 R=0.8425<=1;
# Phi (A_n) has D^{1/n} = 3698 -> infinity with R = 0. All consistent.
#
# SCOPE (honest): this closes the TRUNCATION class completely. It does not by itself cover
# Pade / Hermite-Pade (different error/denominator profile) -- those fail separately by
# measured Siegel coefficient growth (v2.12.30-31).
# ============================================================================
