# Degree-bounded test of the Q=-1 relation A0(x)f(x)+A1(x)f(-x)=b(x) for f=U,V (paper2a prop:noqdiff).
# A relation forces A0(x_m) - rho_m A1(x_m) = 0 at every travel pole (rho_m = Res_{-x_m} f / Res_{x_m} f).
# For deg A0, deg A1 <= D this is a linear system M_D c = 0, M_D[m] = [u_m^k, -rho_m u_m^k]_{k<=D},
# u_m = (1-x_m)/(1-x_1) (a basis change, which does not affect whether a kernel exists).
# We print the smallest singular value of M_D (rows scaled to unit norm) for D = 0..9, m = 1..20,
# at two working precisions.  Floating point, NOT an interval certificate.
# Usage: python3 rootunity_fit.py dps
import sys
from mpmath import mp, mpf, matrix, svd_r, sqrt, log, nstr, findroot
mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 200
src = open('/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/nondfinite/rootunity_check.py').read()
exec(src.split('guesses =')[0].replace('mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 110', ''))
guesses = [mpf('0.4494536306')] + [mpf(l.strip()) for l in open(POLES).readlines()]
M = 20
xs, rU, rV = [], [], []
for m in range(1, M + 1):
    g0 = guesses[m - 1]
    f = lambda t: blocks(t, Jof(t))[0]
    q = findroot(f, (g0*(1 - mpf(10)**-9), g0*(1 + mpf(10)**-12)), solver='anderson',
                 tol=mpf(10)**(-mp.dps + 15))
    x = sqrt(q)
    g, Se, Y, big = blocks(q, Jof(q))
    t1 = t1_Y3(q, Se, Y)
    bUp = t1*(1 - x + q)/(1 + q) + 1/(2*x); bUm = t1*(1 + x + q)/(1 + q) - 1/(2*x)
    bVp = t1 + (1 + x)/(2*x); bVm = t1 - (1 - x)/(2*x)
    xs.append(x)
    rU.append(((1 - x)/(1 + x))**4*(bUm/bUp)**2)
    rV.append(((1 - x)/(1 + x))**2*(bVm/bVp)**2)
u = [(1 - x)/(1 - xs[0]) for x in xs]
for name, rho in (('U', rU), ('V', rV)):
    for D in range(0, 10):
        A = matrix(M, 2*(D + 1))
        for i in range(M):
            row = [u[i]**k for k in range(D + 1)] + [-rho[i]*u[i]**k for k in range(D + 1)]
            nr = sqrt(sum(v*v for v in row))
            for k, v in enumerate(row): A[i, k] = v/nr
        # scale columns to unit norm as well
        for k in range(2*(D + 1)):
            nc = sqrt(sum(A[i, k]**2 for i in range(M)))
            for i in range(M): A[i, k] /= nc
        S = svd_r(A, compute_uv=False)
        smin = min(S[i] for i in range(len(S)))
        print(name, 'D=%d' % D, 'rows=%d cols=%d' % (M, 2*(D + 1)), 'sigma_min=%s' % nstr(smin, 12),
              'dps=%d' % mp.dps, flush=True)
