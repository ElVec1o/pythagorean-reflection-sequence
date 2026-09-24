# P1b: scan |Sigma_N(a/N)|/sqrt(N) over all a/N (gcd=1, a<=N/2, ell>=DELTA), N<=NMAX, all N classes
# (twist eps as in S0_lemma: n0=1 iff N=2 mod 4). Two precisions compared.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1b_scan.py NMAX [DELTA]
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, sin, nstr
def sigma(a, N):
    n0 = 1 if N % 4 == 2 else 0
    z = exp(2j*pi*a/N); c = -2*(1-z); C = c**N; w = 1/C
    for _ in range(400): w = (1-w)**2/C
    lam = (1-w)**(mpf(1)/N); eps = exp(-2j*pi*n0/N); u = eps*lam**2/c
    zp = [exp(2j*pi*((a*i) % N)/N) for i in range(N)]
    tot = mpc(0); term = mpc(1); big = mpf(0)
    for r in range(N):
        t = zp[(r*r) % N]*term; tot += t; big = max(big, abs(t))
        term *= eps*lam**2/((1-zp[(2*r+1) % N]*u)*(1-zp[(2*r+2) % N]*u))
    return tot, big
if __name__ == '__main__':
    NMAX = int(sys.argv[1]); DELTA = float(sys.argv[2]) if len(sys.argv) > 2 else 0.05
    res = {0: [9, 0, None, None], 1: [9, 0, None, None], 2: [9, 0, None, None], 3: [9, 0, None, None]}
    maxdiff = 0; n = 0
    for N in range(2, NMAX+1):
        for a in range(1, N//2+1):
            if gcd(a, N) != 1 or 4*sin(pi*a/N) < exp(DELTA): continue
            mp.dps = 50; S1, big = sigma(a, N)
            mp.dps = 80; S2, _ = sigma(a, N)
            maxdiff = max(maxdiff, abs(S1/S2-1)); n += 1
            r = float(abs(S2)/sqrt(N)); cl = N % 4; R = res[cl]
            if r < R[0]: R[0] = r; R[2] = (a, N)
            if r > R[1]: R[1] = r; R[3] = (a, N)
    print('cases', n, 'max precision discrepancy', nstr(maxdiff, 3))
    for cl in range(4): print('N=%d mod 4: min |Sigma|/sqrtN = %.5f at %s ; max = %.5f at %s' % (cl, res[cl][0], res[cl][2], res[cl][1], res[cl][3]))
