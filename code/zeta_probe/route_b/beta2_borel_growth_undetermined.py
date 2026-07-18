#!/usr/bin/env python3
"""v2.12.29: the Borel geometry is NOT determined by 23 exact coefficients -- withdrawal of the
earlier singularity reading, and a structural constraint on the growth.

ATTEMPT: apply the leading-symbol technique that closed the onset law to the OTHER two open
problems (Borel representation; beta_2 irrationality). Outcome: a correction on the first,
nothing on the second. Reported as such.

FINDING 1 (correction, three independent tests): the A_n sequence is PRE-ASYMPTOTIC at n=22.
 - Gevrey class: log|A_n|/(n log n) = 0.27,0.38,0.58,0.70,0.76,0.77,0.75,0.70,0.66,0.70,0.68,
   0.66,0.67 for n=10..22 -- below 1, not settling towards 1 (Gevrey-1) or 2 (Gevrey-2).
 - Borel-coefficient ratios |b_n/b_{n-1}| oscillate over two orders (146,29,7.3,2.0,0.52,0.071,
   0.118,6.6,0.269,0.214,1.18) -- no convergence to any 1/|t0|.
 - Pade-Borel nearest singularity WANDERS with approximant order:
   |t| = 2.284 ([5/5]), 0.0067 ([6/6]), 0.0337 ([7/7]), 0.0828 ([8/8]), 0.1287 ([9/9]),
   0.2832 ([10/10]) -- higher orders produce spurious near-origin poles.
 - 3-term Darboux fits give |t0| = 9.19, 1.17, 2.45 at n0 = 18, 20, 22.
 - Signs of A_n irregular (complex singularities, unresolvable at this length).
=> The v2.12.20 reading "three complex-conjugate pairs near |t| ~ 2.6, positive axis clear,
   classical Borel summability expected" is WITHDRAWN: neither the Gevrey class nor the
   singularity locations are established. Borel summability on R+ is NOT supported by the data;
   the Borel representation conjecture's analytic premise is open. paper2 corrected.

FINDING 2 (structural, from the onset-law weight machinery): only Bernoulli numbers of index
<~ n reach A_n. A B_j occurring in c_m sits at k-degree deg(c_m) - j, and reaches A_n only if
deg(c_m) - j >= 2m - 2n, i.e. j <= 2n - m + [m even]; maximizing min(deg c_m, 2n-m+1) over m
gives index ~ n. This EXCLUDES the naive Gevrey-2 growth that B_{2n} ~ (2n)!/(2pi)^{2n} would
otherwise force -- but the single-Bernoulli estimate n!/(2pi)^n (t0 = 2pi) undershoots the
measured |A_22| by ~16 orders, so the assembly multiplicity dominates and the class stays open.

FINDING 3 (beta_2): no new angle. The leading-symbol technique produces asymptotic identities
about exact rational data; beta_2 irrationality is a Diophantine statement requiring the value
theory for Borel sums of non-holonomic factorial-denominator series, which does not exist. The
onset law's proved denominator structure does not transfer: the A_n are coefficients of a
divergent (asymptotic) series and furnish no rational approximations to q* itself.

WHAT THE BOREL PROGRAM NOW NEEDS: either coefficients far beyond n=22 (the asymptotic regime is
not reached; order ~40 would need NEPS ~ 160, hours of exact arithmetic), or an analytic
derivation of the growth constant. Both are concrete; neither is closed here.
"""
