#!/usr/bin/env python3
"""
annulus_certificate.py -- the certificate for Appendix app:annulus of paper 2
(Lemmas app:rep, app:euler, app:theta, app:M2 and Proposition prop:selower).

Appendix app:annulus proves  M_2 := max_{[qZ,Z]} |f''| <= 7 w^4  and turns it into
|S_e(q_m)| >= 0.35 sqrt(tau_m).  Every constant in that chain is regenerated here
from the ingredients the proof names, at two working precisions.  m2_certificate.py
measures the TRUE size of M_2 (the sharpness Remark rem:M2sharp); this script
certifies the PROOF's upper bound instead, which is a different quantity: the
proof's bound is about a factor 30 above the truth and it is the bound, not the
truth, that the lemma asserts.

Notation, fixed throughout (Appendix app:annulus):

    q = e^{-tau},  z_0 = sqrt(2(1-q)),  Z = z_0/sqrt(q),  w = sqrt(2/tau),
    f(z) = cos(z;q^2) = C(z^2),  C(y) = sum_j (-1)^j q^{j^2+j} y^j/(q;q)_{2j},
    f''(z) = 2 C'(z^2) + 4 z^2 C''(z^2).

For xi in [qZ, Z] the annulus radius is r = xi e^{-tau/2}, i.e. r^2 = xi^2 e^{-tau},
so that rho = y/r^2 = e^{tau} exactly, which is what kills (log rho - tau)^2 in
Lemma app:theta.  Write

    w_r = r/(1-q),   K_r = r^2/(2(1-r)(1-q^2)),   s = tau*w_r.

Assembling Lemma app:theta with Lemma app:euler and the unfolding identity of the
proof of Lemma app:M2 gives, for n = 1, 2,

    |C^{(n)}(y)|  <=  e^{K_r - n tau + tau w_r^2/4} * Q_n * r^{-2n},

    Q_1 = tau^{-1/2} + [ s*erf(s/(2 sqrt(tau))) + 2 sqrt(tau/pi) e^{-s^2/(4 tau)} ]/(2 tau),
    Q_2 = (2 tau + s^2)/(4 tau^2) + tau^{-3/2}[ same bracket ] + 1/tau,

which are the paper's constants: the appendix quotes  sqrt(tau) Q_1 <= 1.825  and
tau Q_2 <= 3.670  over the whole range.  Both are reported below as computed
suprema, not as quoted values.

Parts:
  1  range geometry: r <= 1/2, sup K_r, sup tau w_r^2/4      (the 0.631 and 0.506)
  2  Lemma app:euler, checked against the true |(x;q)_inf^{-1}| on a theta grid
  3  Lemma app:theta: the excess constant max_d 2 d e^{-pi d/tau} = 2 tau/(pi e)
  4  the unfolding identity of the proof of Lemma app:M2
  5  the moment constants: sup sqrt(tau) Q_1 and sup tau Q_2   (the 1.825 and 3.670)
  6  the assembled bound tau^2 * M_2bound and the margin against the target 28
  7  soundness: the bound is checked to dominate the true max|f''| where both are
     computable
  8  Proposition prop:selower: the discrete-Gronwall constant 0.61, the window
     condition Z <= min(0.2, q/3), the error fraction 28 sqrt(2) 1.02 sqrt(tau),
     and the final constant against 0.35

Arithmetic model: mpmath mpf at the stated dps; NOT interval arithmetic.  Parts
1, 3, 5, 6, 8 are closed-form elementary expressions and are evaluated at two
precisions (dps 30 and dps 60); parts 2, 4, 7 involve series/quadrature and carry
the guard digits noted at their point of use.  Rule 7: the two-precision
disagreement count must be zero.

Regime note (Rule 7 verdict discipline).  The single load-bearing comparison is
"tau^2 M_2bound(tau, xi) <= 28 for every tau in (0, 0.0198] and every xi in
[qZ, Z]".  Both sides are functions of tau alone once the sup over xi is taken,
they are compared at the same tau, and the target 28 is the identity 7 w^4 tau^2 =
28 rather than an independently measured number, so there is no regime to
mismatch.  What CAN go wrong, and is therefore reported separately, is the sup
over xi: the two factors r^{-2n} and e^{tau w_r^2/4} move in opposite directions
across the window, so an endpoint evaluation is not automatically the maximum.
Part 6 scans the window instead of assuming an endpoint, and separately reports
the appendix's own factored bound, which pairs the largest K_r and the largest
tau w_r^2/4 (both at xi = Z) with the largest r^{-2} (at xi = qZ) and is therefore
above the honest sup.
"""
import sys
from mpmath import mp, mpf, exp, sqrt, log, pi, erf, cosh, cos, quad, inf, e

TAU_MAX = '0.0198'          # top of the range of Lemma app:M2
TAU_SEL = '1.29e-4'         # threshold of Proposition prop:selower
TARGET = 28                 # 7 w^4 tau^2, the target of Lemma app:M2

# The two moment constants quoted in the proof of Lemma app:M2.  The appendix as
# first written carried 1.825 and 3.670; this script measures
# sup sqrt(tau) Q_1 = 1.82733, which 1.825 does NOT bound, so the first was
# corrected to 1.83 in the text.  Both are checked against the measured suprema
# below; a False there is a defect in the text, not in the script.
C1_CONST = '1.83'
C2_CONST = '3.670'


# ------------------------------------------------------------- geometry ----

def geom(tau):
    q = exp(-tau)
    z0 = sqrt(2 * (1 - q))
    Z = z0 / sqrt(q)
    return q, z0, Z, sqrt(2 / tau)


def annulus(tau, xi):
    """(r, w_r, K_r, s) at the radius r^2 = xi^2 e^{-tau} of Lemma app:M2."""
    q = exp(-tau)
    r = xi * exp(-tau / 2)
    w_r = r / (1 - q)
    K_r = r ** 2 / (2 * (1 - r) * (1 - q ** 2))
    return r, w_r, K_r, tau * w_r


def Qn(tau, s):
    """the two assembled Gaussian-moment factors of the proof of Lemma app:M2."""
    brack = s * erf(s / (2 * sqrt(tau))) + 2 * sqrt(tau / pi) * exp(-s ** 2 / (4 * tau))
    Q1 = tau ** mpf(-0.5) + brack / (2 * tau)
    Q2 = (2 * tau + s ** 2) / (4 * tau ** 2) + tau ** mpf(-1.5) * brack + 1 / tau
    return Q1, Q2


def m2_bound(tau, xi):
    """the appendix's upper bound on |f''(xi)|, assembled at the point xi."""
    r, w_r, K_r, s = annulus(tau, xi)
    Q1, Q2 = Qn(tau, s)
    core = K_r + tau * w_r ** 2 / 4
    C1 = exp(core - tau) * Q1 / r ** 2
    C2 = exp(core - 2 * tau) * Q2 / r ** 4
    return 2 * C1 + 4 * xi ** 2 * C2


def m2_bound_sup(tau, N=200):
    """sup over xi in [qZ, Z] of tau^2 * m2_bound, and the maximising xi."""
    q, z0, Z, w = geom(tau)
    lo, hi = q * Z, Z
    best, at = mpf(-1), lo
    for i in range(N + 1):
        xi = lo + (hi - lo) * mpf(i) / N
        v = m2_bound(tau, xi)
        if v > best:
            best, at = v, xi
    # local refinement around the grid maximum
    step = (hi - lo) / N
    a, b = max(lo, at - step), min(hi, at + step)
    for _ in range(80):
        m1, m2_ = a + (b - a) / 3, b - (b - a) / 3
        if m2_bound(tau, m1) < m2_bound(tau, m2_):
            a = m1
        else:
            b = m2_
    xi = (a + b) / 2
    best = max(best, m2_bound(tau, xi))
    return tau ** 2 * best, xi


def m2_bound_paper(tau):
    """the appendix's own factored bound: sup K_r and sup tau w_r^2/4 (at xi = Z)
    paired with sup r^{-2} (at xi = qZ) and 4 xi^2/r^4 <= (2/tau) e^{3tau}(1+2tau)."""
    q, z0, Z, w = geom(tau)
    Kmax = max(annulus(tau, q * Z)[2], annulus(tau, Z)[2])
    Emax = max(tau * annulus(tau, q * Z)[1] ** 2 / 4, tau * annulus(tau, Z)[1] ** 2 / 4)
    rmin = min(annulus(tau, q * Z)[0], annulus(tau, Z)[0])
    c1 = mpf(C1_CONST)
    c2 = mpf(C2_CONST)
    t1 = 2 * tau ** 2 * exp(Kmax - tau + Emax) * c1 * tau ** mpf(-0.5) / rmin ** 2
    t2 = tau ** 2 * (2 / tau) * exp(3 * tau) * (1 + 2 * tau) * exp(Kmax - 2 * tau + Emax) * c2 / tau
    return t1 + t2, Kmax, Emax


# --------------------------------------------------------- true objects ----

def qpoch_inv_abs(r, theta, tau):
    """|(x;q)_inf^{-1}| with x = r e^{i theta}.  The product is truncated where
    |x q^j| <= delta, the omitted factors contributing at most
    delta/((1-delta)(1-q)) to |log|, which is held below 10^{-14}."""
    q = exp(-tau)
    delta = (1 - q) * mpf('1e-15')
    logacc = mpf(0)
    ct, st = cos(theta), mp.sin(theta)
    qj = mpf(1)
    for _ in range(400000):
        rj = r * qj
        if rj <= delta:
            break
        u_re, u_im = rj * ct, rj * st
        logacc += log((1 - u_re) ** 2 + u_im ** 2) / 2
        qj *= q
    return exp(-logacc)


def series_length(w, dps):
    """smallest J with w^{2J}/(2J)! below 10^{-dps}: the terms of C(y) on the window
    track w^{2j}/(2j)!, which peaks at 2j ~ w and then falls superexponentially."""
    J, acc, lw = 1, mpf(0), 2 * log(w)
    while J < 20000:
        acc += lw - log(2 * J - 1) - log(2 * J)
        if acc < -dps * mpf('2.302585092994046') and J > w:
            return J + 8
        J += 1
    return J


def coeffs(tau, jmax):
    """c_j = (-1)^j q^{j^2+j}/(q;q)_{2j}, j = 0..jmax."""
    q = exp(-tau)
    out, poch = [], mpf(1)
    for j in range(jmax + 1):
        if j > 0:
            poch *= (1 - q ** (2 * j - 1)) * (1 - q ** (2 * j))
        c = q ** (j * j + j) / poch
        out.append(-c if (j & 1) else c)
    return out


def f2_true(xi, c):
    """the true f''(xi) = 2 C'(xi^2) + 4 xi^2 C''(xi^2), from a coefficient list."""
    y = xi * xi
    d1 = d2 = mpf(0)
    yp = mpf(1)                       # y^{j-1}
    for j in range(1, len(c)):
        d1 += j * c[j] * yp
        if j >= 2:
            d2 += j * (j - 1) * c[j] * (yp / y)
        yp *= y
    return 2 * d1 + 4 * y * d2


def m2_true_sup(tau, N=120):
    """max_{[qZ,Z]} |f''| by a scan (a scan, not a supremum proof)."""
    q, z0, Z, w = geom(tau)
    c = coeffs(tau, series_length(w, mp.dps))
    lo, hi = q * Z, Z
    best = mpf(0)
    for i in range(N + 1):
        best = max(best, abs(f2_true(lo + (hi - lo) * mpf(i) / N, c)))
    return best


def unfolding_lhs(tau, w_r, prec_pts=2000):
    """(1/2pi) int_0^{2pi} e^{w_r cos t} G(pi - 2t) dt,  G(p) = sum_k e^{-(p-2 pi k)^2/(4 tau)}."""
    def G(p):
        tot = mpf(0)
        for k in range(-6, 7):
            tot += exp(-(p - 2 * pi * k) ** 2 / (4 * tau))
        return tot
    return quad(lambda t: exp(w_r * cos(t)) * G(pi - 2 * t), [0, pi / 2, pi, 3 * pi / 2, 2 * pi]) / (2 * pi)


def unfolding_rhs(tau, w_r):
    """(1/2pi) int_R cosh(w_r sin(u/2)) e^{-u^2/(4 tau)} du."""
    L = 12 * sqrt(tau) + 2
    return quad(lambda u: cosh(w_r * mp.sin(u / 2)) * exp(-u ** 2 / (4 * tau)),
                [-L, 0, L]) / (2 * pi)


def series_checks(dps):
    """parts 2, 4, 7: the pieces that need series or quadrature."""
    mp.dps = dps
    out = {}
    tmax = mpf(TAU_MAX)

    # part 2: Lemma app:euler, on a (tau, xi, theta) grid
    worst = mpf(0)
    for tau in [tmax, tmax / 4]:
        q, z0, Z, w = geom(tau)
        for xi in (q * Z, Z):
            r, w_r, K_r, s = annulus(tau, xi)
            for k in range(0, 13):
                th = 2 * pi * mpf(k) / 13
                lhs = qpoch_inv_abs(r, th, tau)
                rhs = exp(w_r * cos(th) + K_r)
                worst = max(worst, lhs / rhs)
    out['euler_ratio_max'] = worst          # must be <= 1

    # part 4: the unfolding identity
    worst = mpf(0)
    for tau in [mpf('0.0198'), mpf('0.005')]:
        q, z0, Z, w = geom(tau)
        for xi in (q * Z, Z):
            r, w_r, K_r, s = annulus(tau, xi)
            a, b = unfolding_lhs(tau, w_r), unfolding_rhs(tau, w_r)
            worst = max(worst, abs(a - b) / abs(b))
    out['unfolding_rel'] = worst

    # part 7: soundness -- the bound must dominate the truth
    ratios = []
    for t in ['0.0198', '0.0126651', '0.005', '0.001']:
        tau = mpf(t)
        gd = int(dps + float(sqrt(2 / tau)) / 2.302585 + 15)
        mp.dps = gd
        true = m2_true_sup(mpf(t), N=120)
        bnd = m2_bound_sup(mpf(t), N=120)[0] / mpf(t) ** 2
        r = true / bnd
        mp.dps = dps
        ratios.append((mpf(t), mpf(r)))
    out['soundness'] = ratios               # every entry must be < 1
    return out


# ------------------------------------------------------------- the run ----

def run(dps):
    """everything that is a closed-form elementary expression, at precision dps."""
    mp.dps = dps
    out = {}
    tmax = mpf(TAU_MAX)
    tsel = mpf(TAU_SEL)

    # part 1: range geometry
    grid = [tmax * mpf(k) / 400 for k in range(1, 401)]
    rmax = Kmax = Emax = mpf(0)
    for tau in grid:
        q, z0, Z, w = geom(tau)
        for xi in (q * Z, Z):
            r, w_r, K_r, s = annulus(tau, xi)
            rmax = max(rmax, r)
            Kmax = max(Kmax, K_r)
            Emax = max(Emax, tau * w_r ** 2 / 4)
    out['r_max'] = rmax
    out['K_max'] = Kmax
    out['E_max'] = Emax

    # part 3: the app:theta excess constant
    out['excess'] = 2 / (pi * e)                        # max_d 2 d e^{-pi d/tau} = 2 tau/(pi e)
    out['excess_ok_upto'] = (1 / out['excess']) ** mpf(2) / 3   # tau^{3/2} <= 1/0.2342

    # part 5: the moment constants, sup over the whole range and window
    q1sup = q2sup = mpf(0)
    for tau in grid:
        q, z0, Z, w = geom(tau)
        for k in range(0, 41):
            xi = q * Z + (Z - q * Z) * mpf(k) / 40
            r, w_r, K_r, s = annulus(tau, xi)
            Q1, Q2 = Qn(tau, s)
            q1sup = max(q1sup, sqrt(tau) * Q1)
            q2sup = max(q2sup, tau * Q2)
    out['sqrt_tau_Q1'] = q1sup
    out['tau_Q2'] = q2sup

    # part 6: the assembled bound
    sup_all, at_all = mpf(0), None
    for tau in grid:
        v, xi = m2_bound_sup(tau, N=120)
        if v > sup_all:
            sup_all, at_all = v, tau
    out['psi_sup'] = sup_all
    out['psi_sup_at'] = at_all
    out['psi_top'], _ = m2_bound_sup(tmax, N=400)
    out['psi_sel'], _ = m2_bound_sup(tsel, N=400)
    out['paper_top'] = m2_bound_paper(tmax)[0]
    out['paper_sel'] = m2_bound_paper(tsel)[0]
    # the low end: tau -> 0 limit of the assembled bound
    out['psi_tiny'], _ = m2_bound_sup(mpf('1e-8'), N=200)

    # part 8: prop:selower
    q, z0, Z, w = geom(tsel)
    out['Z_at_sel'] = Z
    out['Zbound_ok'] = Z <= min(mpf('0.2'), q / 3)
    q2, z02, Z2, w2 = geom(tmax)
    out['Z_at_top'] = Z2
    out['Zbound_ok_top'] = Z2 <= min(mpf('0.2'), q2 / 3)
    # discrete Gronwall: sum kappa_n = qZ/(2q - Z) <= 0.6 Z when Z <= q/3
    gron = mpf(0)
    for tau in grid:
        q, z0, Z, w = geom(tau)
        if Z <= min(mpf('0.2'), q / 3):
            gron = max(gron, (q * Z / (2 * q - Z)) / Z)
    out['gronwall_ratio'] = gron          # must be <= 0.61
    # the final chain at tau = tsel and below
    def selower(tau):
        q, z0, Z, w = geom(tau)
        sZ_lo = sqrt(1 - mpf('0.61') * Z)                 # Casoratian lower bound
        A = q * (1 - sqrt(q)) / (1 - q) * Z * sZ_lo       # first term
        B = (1 - sqrt(q)) * (1 - q) * Z ** 2 * (TARGET / tau ** 2)
        return A, B, (A - B) / sqrt(tau)
    A, B, val = selower(tsel)
    out['errfrac'] = B / A
    out['errfrac_paper'] = 28 * sqrt(mpf(2)) * mpf('1.02') * sqrt(tsel)
    out['selower_const'] = val
    worst = val
    for k in range(1, 400):
        _, _, v = selower(tsel * mpf(k) / 400)
        worst = min(worst, v)
    out['selower_worst'] = worst
    return out


def main():
    A = run(30)
    B = run(60)
    mp.dps = 25

    keys = ['r_max', 'K_max', 'E_max', 'excess', 'sqrt_tau_Q1', 'tau_Q2',
            'psi_sup', 'psi_top', 'psi_sel', 'psi_tiny', 'paper_top', 'paper_sel',
            'gronwall_ratio', 'errfrac', 'errfrac_paper', 'selower_const',
            'selower_worst', 'Z_at_sel', 'Z_at_top']
    print('=' * 88)
    print('APPENDIX app:annulus -- every constant regenerated, at dps 30 and dps 60')
    print('=' * 88)
    print('  %-22s %-26s %-26s %s' % ('quantity', 'dps 30', 'dps 60', 'agree'))
    bad = 0
    for k in keys:
        a, b = mpf(A[k]), mpf(B[k])
        ok = abs(a - b) <= mpf('1e-20') * max(abs(b), mpf(1))
        bad += 0 if ok else 1
        print('  %-22s %-26s %-26s %s' % (k, mp.nstr(a, 12), mp.nstr(b, 12), ok))
    print()
    print('  boolean checks (dps 60):')
    for k in ['Zbound_ok', 'Zbound_ok_top']:
        print('    %-22s %s' % (k, B[k]))
    print('    r <= 1/2 on the window     %s   (sup r = %s)'
          % (B['r_max'] <= mpf('0.5'), mp.nstr(B['r_max'], 8)))
    print('    sup K_r <= 0.631           %s' % (B['K_max'] <= mpf('0.631')))
    print('    sup tau w_r^2/4 <= 0.506   %s' % (B['E_max'] <= mpf('0.506')))
    print('    sup sqrt(tau) Q_1 <= %-6s %s   [1.825 would give %s]'
          % (C1_CONST, B['sqrt_tau_Q1'] <= mpf(C1_CONST),
             B['sqrt_tau_Q1'] <= mpf('1.825')))
    print('    sup tau Q_2 <= %-12s %s' % (C2_CONST, B['tau_Q2'] <= mpf(C2_CONST)))
    print('    excess 2/(pi e) <= 0.2342  %s   [0.234 would give %s]'
          % (B['excess'] <= mpf('0.2342'), B['excess'] <= mpf('0.234')))
    print('    Gronwall ratio <= 0.61     %s' % (B['gronwall_ratio'] <= mpf('0.61')))

    print()
    print('  THE LOAD-BEARING INEQUALITY of Lemma app:M2   (target 7 w^4 tau^2 = 28)')
    print('    sup over tau in (0, %s] and xi in [qZ, Z] of tau^2 |f\'\'| bound : %s'
          % (TAU_MAX, mp.nstr(B['psi_sup'], 10)))
    print('    attained at tau                                                : %s'
          % mp.nstr(B['psi_sup_at'], 8))
    print('    value at tau = %-10s (top of the range)                  : %s'
          % (TAU_MAX, mp.nstr(B['psi_top'], 10)))
    print('    value at tau = %-10s (prop:selower threshold)            : %s'
          % (TAU_SEL, mp.nstr(B['psi_sel'], 10)))
    print('    value at tau = 1e-8       (tau -> 0 plateau)                   : %s'
          % mp.nstr(B['psi_tiny'], 10))
    marg = (mpf(TARGET) - B['psi_sup']) / mpf(TARGET) * 100
    print('    MARGIN against 28                                              : %s %%'
          % mp.nstr(marg, 6))
    print('    bound holds (sup <= 28)                                        : %s'
          % (B['psi_sup'] <= mpf(TARGET)))
    print()
    print("  the appendix's own FACTORED bound (largest K_r and largest tau w_r^2/4")
    print('  paired with the largest r^{-2}; above the honest sup by construction):')
    print('    at tau = %-10s : %s     (appendix text: 25.04)'
          % (TAU_MAX, mp.nstr(B['paper_top'], 8)))
    print('    at tau = %-10s : %s     (appendix text: 20.2)'
          % (TAU_SEL, mp.nstr(B['paper_sel'], 8)))
    print()

    print('  SERIES / QUADRATURE CHECKS (parts 2, 4, 7)')
    SA, SB = series_checks(25), series_checks(40)
    mp.dps = 25
    ok_e = SB['euler_ratio_max'] <= 1
    ok_u = SB['unfolding_rel'] <= mpf('1e-18')
    print('    Lemma app:euler  max |(x;q)_inf^-1| / e^{w_r cos t + K_r} : %s  (<=1: %s)'
          % (mp.nstr(SB['euler_ratio_max'], 10), ok_e))
    print('    unfolding identity, worst relative gap                    : %s  (ok: %s)'
          % (mp.nstr(SB['unfolding_rel'], 6), ok_u))
    ok_s = True
    for tau, ratio in SB['soundness']:
        ok_s = ok_s and ratio < 1
        print('    soundness at tau = %-12s true max|f\'\'| / bound        : %s'
              % (mp.nstr(tau, 8), mp.nstr(ratio, 6)))
    print('    the bound dominates the truth at every sampled tau        : %s' % ok_s)
    bad += 0 if (ok_e and ok_u and ok_s) else 1
    if abs(SA['euler_ratio_max'] - SB['euler_ratio_max']) > mpf('1e-15'):
        bad += 1
    print()
    print('  PROPOSITION prop:selower final chain, at tau = %s:' % TAU_SEL)
    print('    error fraction  B/A                    : %s' % mp.nstr(B['errfrac'], 8))
    print("    appendix's 28 sqrt2 (1.02) sqrt(tau)   : %s  (text says <= 0.46)"
          % mp.nstr(B['errfrac_paper'], 8))
    print('    (|S_e| lower bound)/sqrt(tau)          : %s  (text says >= 0.35)'
          % mp.nstr(B['selower_const'], 8))
    print('    worst over (0, %s]                : %s'
          % (TAU_SEL, mp.nstr(B['selower_worst'], 8)))
    print('    0.35 bound holds                       : %s'
          % (B['selower_worst'] >= mpf('0.35')))
    print()
    print('  two-precision disagreements: %d' % bad)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
