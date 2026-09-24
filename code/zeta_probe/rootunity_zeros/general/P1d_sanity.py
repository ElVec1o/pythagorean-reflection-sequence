# P1d_sanity.py -- VERIFIED end-to-end check of Theorem 5 at concrete (a,N): Sigma_N by direct Arb recursion versus
# Main'_N = G*_N exp(-Phi_N(eps)) Main'_Z (Definition 4, with the seed's n2), all residue classes of N mod 4.
# Prints |Sigma/Main'_N - 1|, to be compared with the certified B of Table 1 (it should be ~K|d|, far below B).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1d_sanity.py p q n2 N1 N2 ...
import sys
from math import gcd
from flint import arb, acb, ctx
from P1d_drift import setup_point, phi_eps, main_prime, sigma_direct, e
p, q, n2 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
for Ns in sys.argv[4:]:
    for th in (1, -1, 3, -5):
        N = int(Ns)
        while (p*N + th) % q or gcd((p*N + th)//q, N) != 1: N += 1
        a = (p*N + th)//q
        S = sigma_direct(a, N)
        ctx.prec = 320
        x, zeta, c, u0, lu = setup_point(a, N)
        n0 = 1 if N % 4 == 2 else 0
        Ph = phi_eps(a, N, u0, lu, 1 if n0 == 0 else e(arb(-n0)/N), 700)
        dd = arb(q*a - p*N)/(q*N)
        M = main_prime(p, q, x, lu, n2, dd) if th > 0 else main_prime(q - p, q, 1 - x, lu.conjugate(), n2, -dd).conjugate()
        G = sum((e(arb((a*r*r - n0*r) % N)/N) for r in range(N)), acb(0))
        Mn = G*(-Ph).exp()*M
        print('%d/%d N=%d (N%%4=%d) theta=%+d d=%.3e |Sigma/Main\'_N - 1| = %s' % (p, q, N, N % 4, th, float(dd.mid()), abs(S/Mn - 1).str(4, radius=False)), flush=True)
