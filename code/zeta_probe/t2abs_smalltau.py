#!/usr/bin/env python3
"""
t2abs_smalltau.py -- the small-tau half of Lemma lem:T2abs of paper 2.

The verified enclosure of the rectangle bound (tools/t2abs_iv, MPFR interval
arithmetic, branch and bound) covers w = sqrt(2/tau) in [10, 101], i.e.
tau in [2/101^2, 0.02].  The remaining range tau < 2/101^2 is closed by an
explicit-constant analytic estimate, because no finite scan reaches tau -> 0.
This script regenerates every constant of that estimate and runs three checks
on it.  It is light: seconds, no memory risk.

The estimate.  Write tau = 2/w^2, and let X be any argument with tau X^2 in
[2e^{-tau}, 2], so that w e^{-tau/2} <= X <= w.  For tau <= 2/101^2 one has
X >= 101 e^{-1/101^2} > 100, w <= X e^{1/X^2} <= 1.0001 X and tau <= 2/X^2.
With sigma_* the largest half-odd-integer below 2w and
R = {1/2 <= Re s <= sigma_*, |Im s| <= X/2},

    |T_2| <= (L + H + R_e)/pi + Tail,

L    = int_0^{X/2} of the left-edge majorant,
H    = int over one horizontal edge,
R_e  = int_0^{X/2} of the right-edge majorant,
Tail = sum_{n > sigma_*} X^{2n}/(2n)!.

Left edge (exact, no Stirling): with s = 1/2+it, 2s+1 = 2+2it,
|Gamma(2+2it)| = |1+2it| |Gamma(1+2it)| and |Gamma(1+2it)|^2 = 2 pi t/sinh(2 pi t),
so the kernel is exactly  X pi sqrt(g(pi t))/sqrt(1+4t^2),  g(u) = tanh(u)/u.

Horizontal edge: with a = 2 sigma+1, u = a/X and
psi(u) = u - arctan u - (u/2) log(1+u^2),  psi'(u) = -(1/2) log(1+u^2),
Stirling with Binet's remainder gives

  X^{2 sigma} pi/(sinh(pi X/2)|Gamma(a+iX)|)
      = sqrt(2 pi) (1-e^{-pi X})^{-1} X^{-1/2} (1+u^2)^{1/4} e^{X psi(u)} e^{-Re mu},

|Re mu| <= |mu(a+iX)| <= mu(a) <= 1/(12a) <= 1/24.  Check (2) below verifies that
rearrangement against mpmath's complex Gamma.

Checks run here:
  (1) the two elementary bounds on psi:  psi(u) <= -u^3/12 on [0,1], and
      psi(u) <= psi(1) + psi'(1)(u-1) for u >= 1 (concavity), on a fine grid;
  (2) the Stirling rearrangement above, against mpmath's complex Gamma;
  (3) the analytic majorant against the actual rectangle-bound integrals,
      computed by direct quadrature at X = 101, 150, 300, 1000.
Check (3) is the falsification attempt: the majorant must exceed the integral it
majorises at every one of those X, and by construction it is not close.

Arithmetic model: mpmath at dps 40 and again at dps 60.  This script does not
carry the rigour of the lemma; the inequalities it checks are proved in the
paper, and the checks are here so that no constant in the paper is unregenerated
(Rule 9) and so that a slip in the derivation would show up.
"""
import sys
from mpmath import mp, mpf, mpc, exp, log, sqrt, pi, gamma, tanh, atan, sinh, quad, nstr

X0 = mpf(100)          # every bound below is asserted for X >= X0
TARGET_C = mpf('0.17')


def psi(u):
    return u - atan(u) - (u / 2) * log(1 + u * u)


def ceil4(x):
    """round up to 6 significant digits, so the printed constant is >= the true one"""
    if x == 0:
        return mpf(0)
    from mpmath import floor, mpf as M
    e = int(mp.floor(mp.log10(abs(x)))) - 5
    return mp.ceil(x / M(10) ** e) * M(10) ** e


def constants():
    """the explicit-constant chain, every step rounded outward"""
    c = {}
    # target: 0.17 tau^{1/4} = 0.17 * 2^{1/4} w^{-1/2} >= c_T X^{-1/2}, using w <= 1.0001 X
    c['target'] = TARGET_C * mpf(2) ** mpf('0.25') / sqrt(mpf('1.0001'))

    # ---- left edge
    # b <= (1/(6X^4))((1+2t)^3/3+(1+2t)^2/2+(1+2t)/3) + 0.02*(2)^{3/2} X^{-3}
    rem3 = mpf('0.02') * mpf(2) ** mpf('1.5')                     # 0.0565685...
    onepX = 1 + X0                                                 # 1+2t <= 1+X <= 1.01 X
    bmax = (onepX ** 3 / 3 + onepX ** 2 / 2 + onepX / 3) / (6 * X0 ** 4) + rem3 / X0 ** 3
    c['eb_left'] = exp(bmax)
    # t <= 1/pi piece
    u0 = 1 + 2 / pi
    c['L_small'] = c['eb_left'] * ((u0 ** 3 / 3 + u0 ** 2 / 2 + u0 / 3))      # * X^{-3}
    c['L_small2'] = c['eb_left'] * rem3                                       # * X^{-2}
    # t >= 1/pi piece: K_L <= (X sqrt(pi)/2) t^{-3/2}; polynomial (8/3)t^3+6t^2+(14/3)t+7/6
    sp = sqrt(pi) / 12                                    # (X sqrt(pi)/2)*(1/(6X^4)) = sp X^{-3}
    c['L1'] = c['eb_left'] * sp * mpf(16) / 15 / mpf(2) ** mpf('2.5')      # X^{-1/2}
    c['L2'] = c['eb_left'] * sp * 4 / mpf(2) ** mpf('1.5')                 # X^{-3/2}
    c['L3'] = c['eb_left'] * sp * mpf(28) / 3 / sqrt(mpf(2))               # X^{-5/2}
    c['L4'] = c['eb_left'] * (sqrt(pi) / 2) * rem3 * 2 * sqrt(pi)          # X^{-2}
    # collect on X^{-1/2}, using X >= X0
    c['c_L'] = (c['L1'] + c['L2'] / X0 + c['L3'] / X0 ** 2
                + (c['L4'] + c['L_small2']) / X0 ** mpf('1.5')
                + c['L_small'] / X0 ** mpf('2.5'))

    # ---- horizontal edge
    c['c_mu'] = exp(mpf(1) / 24) / (1 - exp(-pi * X0))
    # fine region u <= sqrt3: b <= (1+u^2)^{3/2}/(18X) + 0.334 X^{-2}
    c['c_b2'] = mpf(4) / 12 + (2 / mpf(18) + rem3) / X0
    bmaxh = 8 / (18 * X0) + c['c_b2'] / X0 ** 2
    c['eb_h'] = exp(bmaxh)
    G43 = gamma(mpf(4) / 3)
    c['I_73'] = mpf(2) ** mpf('1.75') * G43 * mpf(12) ** (mpf(1) / 3)   # int (1+u^2)^{7/4} e^{X psi}
    c['I_14'] = mpf(2) ** mpf('0.25') * G43 * mpf(12) ** (mpf(1) / 3)   # int (1+u^2)^{1/4} e^{X psi}
    pref = sqrt(2 * pi) * c['c_mu'] / 2
    c['c_H'] = pref * c['eb_h'] * c['I_73'] / 18                        # X^{-5/6}
    c['c_H2'] = pref * c['eb_h'] * c['c_b2'] * c['I_14']                # X^{-11/6}
    # the u >= 1 remnants (tangent bound) and the crude region u > sqrt3
    p1, dp1 = psi(mpf(1)), -log(mpf(2)) / 2
    c['tail_u1'] = pref * c['eb_h'] * 4 ** mpf('1.75') / 18 / (-dp1) * exp(p1 * X0) / X0 ** mpf('1.5')
    crude = 1 + exp(mpf('30.3') * sqrt(2) / X0)
    e2 = p1 + dp1 * (sqrt(mpf(3)) - 1)
    c['tail_crude'] = pref * crude * (1 + 3) ** mpf('0.25') / (-dp1) * exp(e2 * X0)
    # The two exponential remnants decay like e^{-0.131(X-100)}; since
    # e^{-0.131(X-100)} sqrt(X) <= 10 for X >= 100, both are absorbed into the
    # X^{-1/2} coefficient at the cost of a factor 10.
    c['c_0'] = (c['c_L'] + 10 * (c['tail_u1'] + c['tail_crude'])) / pi
    c['c_1'] = c['c_H'] / pi
    c['c_2'] = c['c_H2'] / pi
    return c


def analytic_bound(c, X):
    """the proved majorant for |T_2| at argument X >= 100 (right edge and tail dropped:
       both are below e^{-1.28X}, see the lemma)"""
    return (c['c_0'] * X ** mpf('-0.5') + c['c_1'] * X ** (-mpf(5) / 6)
            + c['c_2'] * X ** (-mpf(11) / 6))


# ------------------------------------------------------------------ checks
def check_psi():
    bad = 0
    for i in range(1, 2001):
        u = mpf(i) / 1000
        if u <= 1 and psi(u) > -u ** 3 / 12:
            bad += 1
        if u >= 1:
            tang = psi(mpf(1)) - log(mpf(2)) / 2 * (u - 1)
            if psi(u) > tang:
                bad += 1
    for i in range(1, 2001):
        u = 1 + mpf(i) * 3 / 1000
        if psi(u) > psi(mpf(1)) - log(mpf(2)) / 2 * (u - 1):
            bad += 1
    return bad


def ker_h_direct(sig, X):
    """X^{2 sigma} pi/(sinh(pi X/2) |Gamma(2 sigma+1+iX)|), straight from mpmath's Gamma"""
    return X ** (2 * sig) * pi / (sinh(pi * X / 2) * abs(gamma(2 * sig + 1 + mpc(0, 1) * X)))


def ker_h_regrouped(sig, X):
    """the same, via the psi rearrangement, with the Binet remainder set to 0"""
    u = (2 * sig + 1) / X
    return (sqrt(2 * pi) / (1 - exp(-pi * X)) / sqrt(X)
            * (1 + u * u) ** mpf('0.25') * exp(X * psi(u)))


def check_regroup(X):
    worst = mpf(0)
    for sig in [mpf('0.5'), mpf(1), mpf(3), mpf(7), mpf('12.5'), mpf(25), mpf(60)]:
        a, b = ker_h_direct(sig, X), ker_h_regrouped(sig, X)
        r = abs(log(a / b))                      # must be <= 1/(12(2 sigma+1))
        worst = max(worst, r * (12 * (2 * sig + 1)))
    return worst


def true_pieces(X, w):
    """the actual rectangle-bound integrals L and H at (tau, X), tau = 2/w^2"""
    tau = 2 / w ** 2
    sstar = mp.floor(2 * w - mpf('0.5')) + mpf('0.5')
    while sstar >= 2 * w:
        sstar -= 1
    crude = 1 + exp(mpf('30.3') * sqrt(tau))

    def amp(sr, si):
        s = mpc(sr, si)
        if abs(s) <= w:
            M = 2 * s
            b = (tau ** 2 / 24) * abs(M ** 3 / 3 + M ** 2 / 2 - M / 3) + mpf('0.02') * tau ** mpf('1.5')
            return min(crude, b * exp(b))
        return crude

    def fl(t):
        g = 1 if t == 0 else tanh(pi * t) / (pi * t)
        return X * pi * sqrt(g) / sqrt(1 + 4 * t * t) * amp(mpf('0.5'), t)

    def fh(sig):
        return ker_h_direct(sig, X) * amp(sig, X / 2)

    L = quad(fl, [0, X / 8, X / 4, X / 2], maxdegree=8)
    brk = sqrt(max(mpf(0), w * w - (X / 2) ** 2))
    nodes = sorted(set([mpf('0.5'), min(brk, sstar), sstar]))
    H = mpf(0)
    for a, b in zip(nodes[:-1], nodes[1:]):
        if b > a:
            H += quad(fh, [a, b], maxdegree=8)
    return (L + H) / pi


def main():
    ok = True
    for dps in (40, 60):
        mp.dps = dps
        c = constants()
        if dps == 40:
            print('constants of the small-tau estimate (dps 40):')
            for k in ['target', 'c_L', 'c_H', 'c_H2', 'c_mu', 'eb_left', 'eb_h',
                      'tail_u1', 'tail_crude', 'c_0', 'c_1', 'c_2']:
                print('   %-10s %s' % (k, nstr(c[k], 8)))
            bad = check_psi()
            print('\n(1) psi grid check over 4000 points: %d violations' % bad)
            ok &= (bad == 0)
            wr = check_regroup(mpf(101))
            print('(2) Stirling rearrangement vs mpmath Gamma at X=101:')
            print('    worst |log ratio| / (1/(12a)) = %s   (must be <= 1)' % nstr(wr, 6))
            ok &= (wr <= 1)
            print('\n(3) analytic majorant vs the actual integrals:')
            print('     X        analytic bound     true (L+H)/pi      ratio')
            for X in [mpf(101), mpf(150), mpf(300), mpf(1000)]:
                A = analytic_bound(c, X)
                T = true_pieces(X, X)          # w = X is the extreme admissible case
                print('  %7s   %s   %s   %s'
                      % (nstr(X, 5), nstr(A, 8), nstr(T, 8), nstr(A / T, 5)))
                ok &= (A > T)
        # the final inequality, at the junction X = 100 and asymptotically
        lhs = c['c_1'] * X0 ** (-mpf(1) / 3) + c['c_2'] * X0 ** (-mpf(4) / 3)
        rhs = c['target'] - c['c_0']
        print('\n[dps %d] final inequality at X=100:  %s <= %s   margin x%s   %s'
              % (dps, nstr(lhs, 8), nstr(rhs, 8), nstr(rhs / lhs, 5), 'OK' if lhs < rhs else 'FAIL'))
        ok &= (lhs < rhs)
    print('\nVERDICT: %s' % ('PASS' if ok else 'FAIL'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
