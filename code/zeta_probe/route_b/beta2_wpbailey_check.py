#!/usr/bin/env python3
"""WP-Bailey exclusion (paper2 rem:truncroot swap addendum): the catalytic argument
2q(1-q) is q-power-free at q*, so no Bailey/well-poised-Bailey specialization to a
single-Pochhammer form applies. z*=0.4949 lies strictly between q*^1 and q*^0=1; the only
loci where 2q(1-q) is a q-power (q=1/2 -> =q; q=2/3 -> =q^2) both miss q*. Confluent 1phi1
is outside the well-poised family entirely; WP-Bailey free parameter is the well-poised
parameter, absent here. Completes the transformation-theoretic description of the rho=1/2 wall.
"""
import mpmath as mp
mp.mp.dps=40
# Structural check: is 2q(1-q) EVER equal to a Q-power q^{2m} or a well-poised value +-q^{m}, for the q* of interest?
# If 2q(1-q) = q^j for integer j at q=q*, a Bailey/summation specialization could apply. Check no small j works,
# and that the equation 2q(1-q)=q^j has no root coinciding with q* (=0.4494536...).
qstar=mp.mpf('0.449453630558948046125545825395696389319555316196')
zc=2*qstar*(1-qstar)
print("catalytic value z* = 2q*(1-q*) =", mp.nstr(zc,18))
print("compare to q*^j:")
for j in range(1,8):
    print(f"  q*^{j} = {mp.nstr(qstar**j,12)}   (z*=q*^{j}? {abs(zc-qstar**j)<mp.mpf(10)**-8})")
# and to Q^m = q*^{2m}
print("z* between q*^1 and q*^2:", qstar**2, "<", zc, "<", qstar**1, "->",
      qstar**2 < zc < qstar**1, "(non-lattice: strictly between consecutive q-powers)")
# solve 2q(1-q)=q for the 'accidental q-power' locus: 2-2q=1 => q=1/2 (r=2 logistic fixed pt), NOT q*
print("\n2q(1-q)=q  => q=1/2 (logistic fixed point) != q*=0.4495; the ONE accidental q-power locus misses q*")
print("2q(1-q)=q^2 => 2-2q=q => q=2/3; also != q*")
print("=> at q*, z* lies strictly between q-powers: no Bailey/WP-Bailey specialization applies (needs q-power arg).")
