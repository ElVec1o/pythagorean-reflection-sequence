# Root-of-unity q-difference relations for U, V (paper2a prop:noqdiff, root-of-unity case).
# Floating point (mpmath), NOT an interval certificate.
# For m = m0..m1 it computes, at the travel pole q_m (x_m = sqrt(q_m)):
#   t1 (two independent formulas), the residue ratios
#     rhoU = Res_{-x_m}U / Res_{x_m}U = ((1-x)/(1+x))^4 (bU-/bU+)^2,
#     rhoV = Res_{-x_m}V / Res_{x_m}V = ((1-x)/(1+x))^2 (bV-/bV+)^2,
#   and, at q = w q_m for w = -1 and for the non-trivial 3rd and 5th roots of unity, the three
#   functions whose zeros carry the poles of U (Lemma lem:mero): g = 1-Sigma_1, S_e and
#   D_U = (1-q^2)(1-q^3)S_e - 2q^4 Y3  (zero <=> 1 - g_U t1 = 0 when S_e != 0), and D_V likewise.
#   Rotations by w = -1 have heavy cancellation in S_e, D_U, D_V: use rootunity_minus.py for those.
# Usage: python3 rootunity_check.py m0 m1 dps
import sys
from mpmath import mp, mpf, mpc, findroot, sqrt, log, exp, pi, nstr, fabs
mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 110
POLES = '/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/poles.txt'

def blocks(q, J):
    """g=1-Sigma_1, S_e, Y3 at (possibly complex) q; returns values and the largest term size.
    Sums until the terms have fallen below 10^-(dps+5) of the largest term (J is a floor)."""
    g = 0; Se = 0; Y = 0; p2 = 1; a = 1; b = 1; big = mpf(1)
    eps = mpf(10)**(-mp.dps - 5); j = 0
    while True:
        if j > 0:
            p2 *= (1 - q**(2*j - 1))*(1 - q**(2*j))
        tg = (-1)**j * 2**j * q**(j*j) * (1 - q)**j / p2
        ts = (-2*(1 - q))**j * q**(j*(j + 1)) / p2
        ty = (-2)**j * (1 - q)**j * q**(j*j + 3*j) / (a*b)
        a *= (1 - q**(2*j + 2)); b *= (1 - q**(2*j + 5))
        g += tg; Se += ts; Y += ty
        tm = max(abs(tg), abs(ts), abs(ty)); big = max(big, tm)
        j += 1
        if j > J and tm < eps*big: break
        if j > 20000: raise RuntimeError('no convergence')
    return g, Se, Y, big

def Jof(q):
    tau = max(-log(abs(q)), mpf(10)**-6); return int(sqrt(2.3*mp.dps/tau)) + 40

def t1_Y3(q, Se, Y):
    return 2*q**3/(1 - q**3)*Y/Se

def t1_psi(q):
    # at a pole: t1 = -(psi(h)+psi(-h))/(2 psi(-h)), psi(t)=C(Z^2 e^{2t}), e^{2h}=1/q
    J = Jof(q); Z2 = 2*(1 - q)/q
    c = []; p = mpf(1)
    for j in range(J):
        if j > 0: p *= (1 - q**(2*j - 1))*(1 - q**(2*j))
        c.append((-1)**j * q**(j*j + j)/p)
    C = lambda y: sum(c[j]*y**j for j in range(J))
    pm, pp = C(Z2*q), C(Z2/q)
    return -(pp + pm)/(2*pm)

guesses = [mpf('0.4494536306')] + [mpf(l.strip()) for l in open(POLES).readlines()]
m0, m1 = int(sys.argv[1]), int(sys.argv[2])
roots = [('-1', mpc(-1, 0))] + [('e(%d/3)' % k, exp(2j*pi*k/3)) for k in (1, 2)] \
        + [('e(%d/5)' % k, exp(2j*pi*k/5)) for k in (1, 2, 3, 4)]
print('# m tau x t1 t1rel rhoU rhoU*16/(1-x)^4 rhoV rhoV*16/(1-x)^6 bigdigits')
for m in range(m0, m1 + 1):
    g0 = guesses[m - 1]
    f = lambda t: blocks(t, Jof(t))[0]
    q = findroot(f, (g0*(1 - mpf(10)**-9), g0*(1 + mpf(10)**-12)), solver='anderson', tol=mpf(10)**(-mp.dps + 15))
    x = sqrt(q); tau = -log(q)
    g, Se, Y, big = blocks(q, Jof(q))
    t1 = t1_Y3(q, Se, Y); t1b = t1_psi(q)
    bUp = t1*(1 - x + q)/(1 + q) + 1/(2*x)
    bUm = t1*(1 + x + q)/(1 + q) - 1/(2*x)
    bVp = t1 + (1 + x)/(2*x)
    bVm = t1 - (1 - x)/(2*x)
    rhoU = ((1 - x)/(1 + x))**4 * (bUm/bUp)**2
    rhoV = ((1 - x)/(1 + x))**2 * (bVm/bVp)**2
    print('POLE', m, nstr(tau, 8), nstr(x, 25), nstr(t1, 25), nstr(abs(t1 - t1b)/abs(t1), 3),
          nstr(rhoU, 30), nstr(rhoU*16/(1 - x)**4, 12), nstr(rhoV, 30), nstr(rhoV*16/(1 - x)**6, 12),
          int(log(big, 10)), 'dps=%d' % mp.dps, '|g(q_m)|=%s' % nstr(abs(g), 3), flush=True)
    for name, w in roots:
        qq = w*q
        gg, S2, Y2, big2 = blocks(qq, Jof(qq))
        DU = (1 - qq**2)*(1 - qq**3)*S2 - 2*qq**4*Y2
        DV = (1 - qq)*(1 - qq**3)*S2 - 2*qq**4*Y2
        print('  ROT', m, name, '|g|=%s' % nstr(abs(gg), 5), '|Se|=%s' % nstr(abs(S2), 5),
              '|DU|=%s' % nstr(abs(DU), 5), '|DV|=%s' % nstr(abs(DV), 5), 'bigdigits=%d' % int(log(big2, 10)), flush=True)
