#!/usr/bin/env python3
"""
m2_certificate.py -- certificate for the sharpness remark of Lemma app:M2 of paper 2.

Lemma app:M2 proves the load-bearing bound  M_2 := max_{[qZ,Z]} |f''| <= 7 w^4  (w = sqrt(2/tau)),
and adds a remark on how lossy that bound is.  This script measures the true size of M_2/w^4.

    f(z)  = cos(z;q^2) = C(z^2),   C(y) = sum_{j>=0} (-1)^j q^{j^2+j} y^j / (q;q)_{2j},
    f''(z) = 2 C'(z^2) + 4 z^2 C''(z^2),
    z_0 = sqrt(2(1-q)),  Z = z_0/sqrt(q),  q = e^{-tau}.

Why the ratio oscillates rather than settling.  f(z) is the q-cosine, so f''(z) ~ -(W/z_0)^2 cos(zW/z_0)
with (W/z_0)^2 = e^{-tau}/(tau(1-q)) ~ w^4/4.  The window [qZ,Z] spans a phase of only
(1-q)Z/tau ~ sqrt(2 tau) radians, so M_2/w^4 ~ (1/4) max |cos| over a phase window that is short
compared with pi: as tau varies the window slides through the cosine and the ratio sweeps [0, 1/4].
A single sample therefore says nothing about the supremum.  The maximum is attained where the window
covers an extremum of the phase, i.e. at the extreme-phase points w = m pi, tau_m = 2/(m pi)^2 --
the same sequence lem:infpoles uses.  This script scans those, plus the top of the range where no
such point lies, plus the named tau values of the paper.

Arithmetic model: mpmath mpf, run at two precisions.  The series is alternating with terms of size
up to ~e^w against an O(1) sum, so the working precision carries w/ln(10) guard digits on top of the
requested accuracy; the two runs must agree to the reported digits.
"""
import sys
from mpmath import mp, mpf, exp, sqrt, pi, log

TAU_MAX = mpf('0.0198')          # the range of Lemma app:M2


def coeffs(tau, jmax):
    """c_j = (-1)^j q^{j^2+j} / (q;q)_{2j}, for j = 0..jmax."""
    q = exp(-tau)
    out = []
    poch = mpf(1)                # (q;q)_{2j}, built incrementally
    for j in range(jmax + 1):
        if j > 0:
            for i in (2 * j - 1, 2 * j):
                poch *= (1 - q ** i)
        c = q ** (j * j + j) / poch
        out.append(-c if (j & 1) else c)
    return out


def f2(z, c):
    """f''(z) = 2 C'(z^2) + 4 z^2 C''(z^2) from the coefficient list."""
    y = z * z
    d1 = mpf(0)
    d2 = mpf(0)
    yp = mpf(1)                  # y^{j-1} for the C' sum
    for j in range(1, len(c)):
        d1 += j * c[j] * yp
        if j >= 2:
            d2 += j * (j - 1) * c[j] * (yp / y)
        yp *= y
    return 2 * d1 + 4 * y * d2


def series_length(w, dps):
    """smallest J with w^{2J}/(2J)! below 10^{-dps}; the sum behaves like cos(w)."""
    J, term = 1, mpf(1)
    lw = 2 * log(w)
    acc = mpf(0)
    while J < 20000:
        acc += lw - log(2 * J - 1) - log(2 * J)
        if acc < -dps * mpf('2.302585092994046') and J > w:
            return J + 8
        J += 1
    return J


def m2_over_w4(tau, dps):
    """max_{[qZ,Z]} |f''| / w^4, at working precision dps."""
    mp.dps = dps
    tau = mpf(tau)
    q = exp(-tau)
    z0 = sqrt(2 * (1 - q))
    Z = z0 / sqrt(q)
    w = sqrt(2 / tau)
    c = coeffs(tau, series_length(w, dps))
    lo, hi = q * Z, Z
    # coarse scan, then three rounds of golden-section refinement on the best bracket
    N = 400
    best, bi = mpf(-1), 0
    vals = []
    for i in range(N + 1):
        v = abs(f2(lo + (hi - lo) * mpf(i) / N, c))
        vals.append(v)
        if v > best:
            best, bi = v, i
    a = lo + (hi - lo) * mpf(max(bi - 1, 0)) / N
    b = lo + (hi - lo) * mpf(min(bi + 1, N)) / N
    for _ in range(60):
        m1 = a + (b - a) / 3
        m2 = b - (b - a) / 3
        if abs(f2(m1, c)) < abs(f2(m2, c)):
            a = m1
        else:
            b = m2
    best = max(best, abs(f2((a + b) / 2, c)))
    return best * tau ** 2 / 4      # /w^4


def dps_for(tau, extra):
    w = float(sqrt(2 / mpf(tau)))
    return int(30 + w / 2.302585 + extra)


def main():
    # tau values: the paper's named ones, the extreme-phase ladder tau_m = 2/(m pi)^2,
    # and a linear sweep across the top of the range (no extreme-phase point lies in
    # (0.01266, 0.0198], since w = m pi forces tau_4 = 0.012665 then tau_3 = 0.02252 > TAU_MAX).
    named = ['0.0198', '0.0126651', '0.01', '0.005', '0.001', '0.000129', '0.0001']
    taus = [(mpf(s), 'named') for s in named]
    for m in range(4, 121):
        t = 2 / (m * pi) ** 2
        if t <= TAU_MAX:
            taus.append((t, f'w={m}pi'))
    for k in range(0, 41):
        t = mpf('0.0128') + (TAU_MAX - mpf('0.0128')) * mpf(k) / 40
        taus.append((t, 'sweep'))
    taus.sort(key=lambda p: -p[0])

    print('  tau            tag        M2/w^4 (dps A)   M2/w^4 (dps B)   agree')
    worst = mpf(0)
    worst_at = None
    disagree = 0
    for tau, tag in taus:
        dA, dB = dps_for(tau, 20), dps_for(tau, 45)
        rA = m2_over_w4(tau, dA)
        rB = m2_over_w4(tau, dB)
        mp.dps = 25
        ok = abs(rA - rB) <= mpf('1e-15') * max(abs(rA), mpf(1))
        if not ok:
            disagree += 1
        if rB > worst:
            worst, worst_at = rB, (tau, tag)
        print(f'  {mp.nstr(tau, 6):<14} {tag:<10} {mp.nstr(rA, 10):>16} {mp.nstr(rB, 10):>16}   {ok}')

    mp.dps = 25
    print(f'\n  points scanned: {len(taus)}   two-precision disagreements: {disagree}')
    print(f'  sup over the scan of M_2/w^4: {mp.nstr(worst, 10)}  at tau = {mp.nstr(worst_at[0], 8)} ({worst_at[1]})')
    for C in ['0.25', '0.26', '0.3', '7']:
        print(f'    M_2 <= {C} w^4 over the scan?  {worst <= mpf(C)}')
    print('\n  (The load-bearing bound of Lemma app:M2 is M_2 <= 7 w^4; the ratio above is what')
    print('   the "deliberately lossy" remark reports.  The scan is a scan, not a supremum proof.)')
    return 0 if disagree == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
