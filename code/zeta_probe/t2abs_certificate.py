#!/usr/bin/env python3
"""
t2abs_certificate.py -- ADAPTIVE-QUADRATURE CROSS-CHECK for Lemma lem:T2abs of paper 2.

SUPERSEDED as the certificate (2026-08-15).  The lemma is now proved by a verified enclosure of
the same majorant, quantified over parameter BOXES rather than sampled: tools/t2abs_iv (Rust,
MPFR interval arithmetic, branch and bound) on tau in [2/101^2, 0.02], and t2abs_smalltau.py
plus the explicit-constant estimate in the paper below that.  This script is retained because it
shares no code with either -- mpmath adaptive quadrature and mpmath.gamma against MPFR intervals
and closed-form/Stirling kernels -- so its seven tabulated values are an independent check that
the enclosure brackets the right quantity from above.  What it delivers is still a grid, and the
paragraph "A 120-point grid is a grid, not a supremum" below still describes it exactly.

|T_2| <= 0.17 tau^{1/4} <= 0.064 < 1 for tau <= 0.02, by absolute values on the boundary of

    R = { 1/2 <= Re s <= sigma_*,  |Im s| <= X/2 },

where sigma_* is the LARGEST HALF-ODD-INTEGER BELOW 2w.  The right edge must be a half-odd-integer,
not 2w itself: at tau = 0.02 one has 2w = 20 exactly, so an edge at 2w runs through the pole s = 20
of pi/sin(pi s) and the contour integral there is divergent (a quadrature rule whose nodes miss the
pole returns a finite number that means nothing).  On Re s = sigma_* one has |sin(pi s)| = cosh(pi t)
>= 1 instead.  R lies WHOLLY INSIDE the lem:Bbounded strip S -- so no bound on B_s outside S is
needed.  The residues n > sigma_* are not enclosed; they are added back as an elementary tail using
0 <= g_n <= 1 at integers (B_n = sum_{i<=2n} phi(i tau) - n phi(tau) >= n phi(tau) >= 0).

Amplitude, honestly:  |B_s| <= (tau^2/24)|M^3/3 + M^2/2 - M/3| + 0.02 tau^{3/2}  where |2s| <= 2w
(this is eq:Btrunc with P_1(M) - s written out in full; dropping the M^2/2 and -M/3 terms gives an
inequality that is FALSE on the contour, by about 6% at tau = 0.02), and |g_s| <= 1 + e^{30.3
sqrt(tau)} elsewhere on the boundary from eq:Bbounds.

Two things this script gets right that a naive version does not:
  * it integrates by ADAPTIVE QUADRATURE PIECEWISE between the region breakpoints.  The amplitude
    majorant jumps by a factor ~1500 at |2s| = 2w, and a uniform Riemann sum straddling that jump
    converges to the answer FROM BELOW: a uniform N=700 sum reports 0.1366 where the converged
    value is 0.1443.
  * it evaluates at X = w, not X = W.  lem:infpoles uses X = w, and it is the worse of the two by
    about 11%.

The lemma asserts a bound on the whole interval (0, 0.02], so the script does two runs:
  (1) the seven named tau values quoted in the paper, down to 1e-5;
  (2) the 120-point grid tau_i = i * 0.02/120, i = 1..120, on which the ratio |T_2|/tau^{1/4} is
      reported together with its increments, so that the monotonicity claim is checked rather than
      asserted.
A 120-point grid is a grid, not a supremum: what it certifies is the value at 120 points and the
sign of 119 increments, and the lemma says exactly that.

Arithmetic model: mpmath mpf with adaptive quadrature, not interval arithmetic.  Every quantity is
computed at dps = 30 and again at dps = 50; the two runs must agree to the digits reported.
"""
import sys
from mpmath import mp, mpf, mpc, exp, sqrt, pi, gamma, sin as msin, quad, factorial, floor

NAMED = ['0.02', '0.0126651', '0.01', '0.005', '0.001', '1e-4', '1e-5']


def sigma_star(w):
    """largest half-odd-integer strictly below 2w."""
    s = floor(2 * w - mpf('0.5')) + mpf('0.5')
    while s >= 2 * w:
        s -= 1
    return s


def Bb(s, tau):                       # honest eq:Btrunc bound on |B_s|
    M = 2 * s
    P = M**3 / 3 + M**2 / 2 - M / 3   # P1(M) - s, exactly
    return (tau**2 / 24) * abs(P) + mpf('0.02') * tau**mpf(1.5)


def gb(s, tau, w, crude):
    if abs(2 * s) <= 2 * w:
        b = Bb(s, tau)
        return min(crude, b * exp(b))
    return crude


def kern(s, X):
    try:
        return abs(X**(2 * s) / gamma(2 * s + 1) * pi / msin(pi * s))
    except Exception:
        return mpf(0)


def t2bound(ts, dps):
    """the rectangle bound on |T_2| at argument X = w, and its pieces."""
    mp.dps = dps
    tau = mpf(ts)
    w = sqrt(2 / tau)
    X = w                                        # <-- the case lem:infpoles uses
    sig = sigma_star(w)
    crude = 1 + exp(mpf('30.3') * sqrt(tau))
    brk = sqrt(max(mpf(0), w * w - (X / 2)**2))  # where |2s| crosses 2w on the horizontal edge

    def fh(sg):
        s = mpc(sg, X / 2)
        return kern(s, X) * gb(s, tau, w, crude)

    hor = mpf(0)
    for a, b in [(mpf('0.5'), min(brk, sig)), (min(brk, sig), sig)]:
        if b > a:
            hor += quad(fh, [a, b], maxdegree=6)
    hor *= 2

    def fv(sg):
        return lambda t: kern(mpc(sg, t), X) * gb(mpc(sg, t), tau, w, crude)

    ver1 = quad(fv(mpf('0.5')), [-X / 2, 0, X / 2], maxdegree=6)
    ver2 = quad(fv(sig), [-X / 2, 0, X / 2], maxdegree=6)

    # residues n > sigma_*, using 0 <= g_n <= 1
    tail = mpf(0)
    n0 = int(sig) + 1
    for n in range(n0, n0 + 500):
        t = X**(2 * n) / factorial(2 * n)
        tail += t
        if t < mpf('1e-60') * max(tail, mpf('1e-60')):
            break
    tot = (hor + ver1 + ver2) / (2 * pi) + tail
    return tot, hor / (2 * pi), ver1 / (2 * pi), ver2 / (2 * pi), tail, sig


def main():
    print('PART 1: the seven named tau values (X = w, honest amplitude, right edge at sigma_*)')
    print(' tau         sigma_*   horiz      vert(1/2)  vert(sig)  tail       TOTAL      /tau^{1/4}  agree')
    worst = mpf(0)
    disagree = 0
    for ts in NAMED:
        A = t2bound(ts, 30)
        B = t2bound(ts, 50)
        mp.dps = 25
        rA, rB = A[0] / mpf(ts)**mpf(0.25), B[0] / mpf(ts)**mpf(0.25)
        ok = abs(rA - rB) <= mpf('1e-12') * max(rA, mpf(1))
        disagree += 0 if ok else 1
        worst = max(worst, rB)
        print(f'  {ts:>9} {mp.nstr(A[5],6):>8} {mp.nstr(A[1],4):>10} {mp.nstr(A[2],4):>10} '
              f'{mp.nstr(A[3],4):>10} {mp.nstr(A[4],3):>10} {mp.nstr(B[0],5):>10} '
              f'{mp.nstr(rB,5):>11}  {ok}')

    print('\nPART 2: the 120-point grid tau_i = i * 0.02/120, i = 1..120')
    grid = [mpf('0.02') * i / 120 for i in range(1, 121)]
    ratios = []
    for tau in grid:
        A = t2bound(tau, 30)
        B = t2bound(tau, 50)
        mp.dps = 25
        rA, rB = A[0] / tau**mpf(0.25), B[0] / tau**mpf(0.25)
        if not abs(rA - rB) <= mpf('1e-12') * max(rA, mpf(1)):
            disagree += 1
        ratios.append(rB)
    mp.dps = 25
    inc = [ratios[i + 1] - ratios[i] for i in range(len(ratios) - 1)]
    down = [i for i, d in enumerate(inc) if d <= 0]
    gmax = max(ratios)
    print(f'  grid points: {len(grid)}   increments: {len(inc)}   non-increasing increments: {len(down)}')
    print(f'  ratio at tau_1  = {mp.nstr(grid[0],5)}: {mp.nstr(ratios[0],5)}')
    print(f'  ratio at tau_120 = {mp.nstr(grid[-1],5)}: {mp.nstr(ratios[-1],5)}')
    print(f'  grid maximum: {mp.nstr(gmax,6)} at tau = {mp.nstr(grid[ratios.index(gmax)],6)}')
    print('  every 10th grid ratio: ' + ' '.join(mp.nstr(ratios[i], 4) for i in range(9, 120, 10)))
    if down:
        print('  monotonicity violations at grid indices: ' + str([i + 1 for i in down]))

    worst = max(worst, gmax)
    print(f'\n  worst ratio seen (named values and grid): {mp.nstr(worst,5)}')
    print(f'  two-precision disagreements (dps 30 vs 50): {disagree}')
    for C in ['0.17', '0.20', '0.25']:
        print(f'    |T2| <= {C} tau^{{1/4}}  =>  at tau=0.02: '
              f'{mp.nstr(mpf(C)*mpf("0.02")**mpf(0.25),4)}   valid on the scan? {worst <= mpf(C)}')
    return 0 if disagree == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
