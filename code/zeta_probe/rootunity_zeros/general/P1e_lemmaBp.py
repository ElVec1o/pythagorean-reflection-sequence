# P1e_lemmaBp.py -- Lemma B' (P1e_lemma.tex): Lemma B at an individual seed j/n (10 <= n <= 52) with EXACT per-seed inputs:
#   beta, P1, P2 from the explicit sums over m <= M with |1-zeta^{-m}| >= |1-zeta0^{-m}| - 2 pi m r (tail m > M by the Lemma-B bound),
#   |T| = |1-w_n|^{-1/2n} |Z_n(j/n)| and env = sum_k |gamma_k||e^{X_k}| from the exact finite formula (Lemma Zk, P1e_logderiv.data1),
#   radius r = r^B_n = 2 y^n / n^2 (y = 0.5; g = local sup |u0| on the disc), contour height eta with g*e^{2 pi eta} = y = 0.5.
# Prints E (bound for |Z_N/Main'_Z - 1|), R (relative S_amp perturbation), and the constants needed for the induction.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1e_lemmaBp.py n1 n2 xlo xhi [y] [tau]
import sys
from math import gcd
from flint import arb, acb, ctx
import P1e_logderiv as LD
from P1e_lemmaB import bound
PI = arb.pi()
def e(z): return (2*PI*acb(0, 1)*z).exp()
def seed(j, n, y=arb('0.5'), tau=arb('0.02'), M=200):
    ctx.prec = 200
    x0 = arb(j)/n
    cabs = arb((-2*(1 - e(x0))).abs_lower())
    r0 = 2*y**n/n**2                              # r^B_n = 2 y^n / n^2  (hazard radius for 10 <= n <= 52)
    xb = x0 + arb(0, arb(r0.upper()))             # disc [j/n - r, j/n + r]
    cl = arb((-2*(1 - e(xb))).abs_lower())
    ell = cl.log()
    g = (1/cl)*(1 + arb('0.1')*(-151*ell).exp())  # |u0| <= g on the disc (Lemma W)
    r = r0
    rho = y/g; eta = rho.log()/(2*PI)
    # exact beta, P1, P2 (sup over Im t <= eta, d in (0, r])
    S0 = arb(0); S1 = arb(0); S2 = arb(0)
    for m in range(1, M + 1):
        if m % n == 0: continue
        den = arb((1 - e(arb((-m*j) % n)/n)).abs_lower()) - 2*PI*m*r
        assert bool(den > 0)
        t = y**m/(m*den)
        S0 += t; S1 += 2*PI*m*t; S2 += (2*PI*m)**2*t
    tl = y**(M + 1)/(1 - y)
    S0 += n/2*tl/(M + 1); S1 += PI*n*tl; S2 += 2*PI**2*n*(M + 1)*tl/(1 - y)
    wb = y**n
    beta = (wb/(2*n*(1 - wb)) + S0).exp()
    P1 = PI*wb/(1 - wb) + S1
    P2 = 2*PI**2*n*wb/(1 - wb)**2 + S2
    Z, Lam, D1, D2, l = LD.data(j, n)          # |Z_n| lower bound, env/|Z| upper
    ctx.prec = 200
    # |T| >= |1-w|^{-1/2n}|Z| >= (1 - wb)^{1/2n}... use |1-w_n| <= 1 + wb
    Tlo = Z*(1 + wb)**(-arb(1)/(2*n))
    env = Lam*Z*(1 - wb)**(-arb(1)/(2*n))
    E, R, side = bound(n, g, eta, tau, arb(0), arb(1), ell, dover=r, bpp=(beta, P1, P2), Tenv=(Tlo, env))
    return E, R, side, r, g, Z, Lam
if __name__ == '__main__':
    n1, n2 = int(sys.argv[1]), int(sys.argv[2]); xlo, xhi = float(sys.argv[3]), float(sys.argv[4])
    worst = arb(0); cnt = 0; fails = []
    for n in range(n1, n2 + 1):
        for j in range(1, n):
            if gcd(j, n) != 1 or not (xlo <= j/n <= xhi): continue
            E, R, side, r, g, Z, Lam = seed(j, n)
            ok = all(v for _, v in side) and bool(E <= 0.5) and bool(R <= 0.5)
            cnt += 1
            if not ok: fails.append((j, n, E.str(3, radius=False), R.str(3, radius=False), [k for k, v in side if not v]))
            worst = worst.max(E)
        print('n=%d done, seeds so far %d, fails %d, max E <= %s' % (n, cnt, len(fails), worst.str(3, radius=False)), flush=True)
    for f in fails: print('FAIL', f)
