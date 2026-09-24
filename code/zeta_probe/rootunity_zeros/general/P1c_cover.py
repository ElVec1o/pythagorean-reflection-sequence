# P1c: covering scan (floating point, VERIFIED-float only). For grid points x in [X0,X1] and N ~ NN (odd),
# computes err_s(x) = min|Sigma_N(a/N)/Main_s - (+-1)| for the 3 nearest seeds s = p/q (q<=QS, ell(s) >= 0.02, non-degenerate),
# and reports the best seed per x. Main_s = P1a multi-saddle leading term at seed s (P1c_dist.main).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1c_cover.py X0 X1 STEP NN QS
import sys
from math import gcd, log as flog, sin as fsin, pi as fpi
from mpmath import mp, mpf, nstr
from P1c_dist import exact_sigma, main
X0, X1, STEP, NN, QS = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
seeds = [(p, q) for q in range(2, QS+1) for p in range(1, q//2+1) if gcd(p, q) == 1
         and flog(4*fsin(fpi*p/q)) >= 0.02 and not (q % 4 == 0 and q*flog(4*fsin(fpi*p/q)) <= flog(4))]
x = X0
while x <= X1 + 1e-12:
    N = NN if NN % 2 else NN+1
    a = round(x*N)
    while gcd(a, N) != 1: N += 2; a = round(x*N)
    near = sorted(seeds, key=lambda s: abs(s[0]/s[1]-a/N))[:3]
    res = []
    for (p, q) in near:
        theta = q*a - p*N
        if theta == 0: res.append((0.0, p, q)); continue
        S, u = exact_sigma(a, N, q); mp.dps = 40
        r = S/main(p, q, theta, N, u)
        res.append((float(min(abs(r-1), abs(r+1))), p, q))
    best = min(res)
    print('x=%.4f a/N=%d/%d ell=%.3f best seed %d/%d err=%.4f   (others %s)' % (x, a, N, flog(4*fsin(fpi*a/N)), best[1], best[2], best[0],
          ' '.join('%d/%d:%.3f' % (s[1], s[2], s[0]) for s in res)), flush=True)
    x += STEP
