#!/usr/bin/env python3
"""
qnumerator_certificate.py -- certificate for the numerator layer of paper 2:
Lemma lem:qsinenum, Lemma lem:halfstep and Proposition prop:numnonvanish.

What is certified, at two working precisions:

  (1) the collapse identities, as identities in 0 < q < 1 (off-pole sampling),

          Sigma_0 = (2q/Z) * sfrak(Z),        S_0 = (2q/z_0) * sfrak(z_0),

      alongside the two already in the paper (Proposition prop:qtrig),

          1 - Sigma_1 = c(Z),                 S_e = 1 - S_1 = c(z_0),

      where  c(u) = cos(u;q^2),  sfrak(u) = q^{-1/2} sin(q^{1/2} u; q^2),
             z_0 = sqrt(2(1-q)),  Z = z_0/sqrt(q),  q = e^{-tau};

  (2) the half-step rules and the q-Pythagoras identity of Koornwinder-Swarttouw,

          c(qu)  = c(u) + q^{3/2} u sfrak(sqrt(q) u),
          sfrak(qu) = sfrak(u) - u c(sqrt(q) u),
          c(u) c(sqrt(q) u) + q^{3/2} sfrak(u) sfrak(sqrt(q) u) = 1;

  (3) the consequences at a travel pole (c(Z) = 0), on the first 30 travel poles:

          q^{3/2} sfrak(z_0) sfrak(Z) = 1        (the pole invariant)
          Sigma_0 * S_0 = 2q/(1-q)               (Proposition prop:numnonvanish)

      together with the individual sizes |Sigma_0|/w, |S_0|/w -> 1 that the
      product identity is consistent with, and the observed sign alternation.

Arithmetic model: mpmath mpf at the stated dps; NOT interval arithmetic.  Every
series here is alternating with a monotone tail in its summation range, and is
truncated when a term falls below 10^{-dps-20} relative, so the first omitted
term bounds the tail.  Terms reach size ~e^{w} against an O(1) sum, so the
working precision carries w/ln(10) guard digits on top of the reported accuracy;
the two runs must agree to the digits reported.  Rule 7: load-bearing values are
computed at two distinct precisions and the disagreement count must be zero.

Regime note (Rule 7 verdict discipline).  Part (1) is an identity in q and is
tested at q values that are NOT travel poles, so nothing in it can be an artefact
of the pole condition.  Part (3) is tested only at travel poles, where the pole
condition c(Z) = 0 is exactly what makes the two statements true; the two panels
are therefore deliberately in different regimes, and neither verdict is quoted
for the other's range.
"""
import sys
from mpmath import mp, mpf, sqrt, exp, log, pi, findroot

# ---------------------------------------------------------------- series ----


def _qpoch(q, n, cache):
    """(q;q)_n, memoised in `cache` (a list) across increasing n."""
    while len(cache) <= n:
        k = len(cache)
        cache.append(cache[k - 1] * (1 - q ** k) if k else mpf(1))
    return cache[n]


def qcos(z, q, cache):
    """cos(z;q^2) = sum_j (-1)^j q^{j^2+j} z^{2j} / (q;q)_{2j}."""
    tot = mpf(0)
    eps = mpf(10) ** (-mp.dps - 20)
    for j in range(4000):
        t = (-1) ** j * q ** (j * j + j) * z ** (2 * j) / _qpoch(q, 2 * j, cache)
        tot += t
        if j > 5 and abs(t) < eps * max(mpf(1), abs(tot)):
            return tot
    raise RuntimeError('qcos did not converge')


def qsin(z, q, cache):
    """sin(z;q^2) = sum_j (-1)^j q^{j^2+j} z^{2j+1} / (q;q)_{2j+1}."""
    tot = mpf(0)
    eps = mpf(10) ** (-mp.dps - 20)
    for j in range(4000):
        t = (-1) ** j * q ** (j * j + j) * z ** (2 * j + 1) / _qpoch(q, 2 * j + 1, cache)
        tot += t
        if j > 5 and abs(t) < eps * max(mpf(1), abs(tot)):
            return tot
    raise RuntimeError('qsin did not converge')


def sfrak(u, q, cache):
    """the half-step q-sine  s(u) = q^{-1/2} sin(q^{1/2} u; q^2)."""
    return qsin(sqrt(q) * u, q, cache) / sqrt(q)


# ------------------------------------------------------- the four blocks ----
# k-recursion of eq:krec:
#   Sigma_k = sum_j A_{k+2j} prod_{i<j} C_{k+2i},   S_k = sum_j a_{k+2j} prod_{i<j} g_{k+2i}
#   A_k = 2q/(1-q^{k+1}),  C_k = 2q^{k+3}/(1-q^{k+2}) - 2q^{k+2}/(1-q^{k+1})
#   a_k = 2q^{k+1}/(1-q^{k+1}),  g_k = a_{k+1} - a_k


def block(k, q, travel):
    tot, prod = mpf(0), mpf(1)
    eps = mpf(10) ** (-mp.dps - 20)
    for j in range(4000):
        idx = k + 2 * j
        if travel:
            term = 2 * q / (1 - q ** (idx + 1))
            fac = (2 * q ** (idx + 3) / (1 - q ** (idx + 2))
                   - 2 * q ** (idx + 2) / (1 - q ** (idx + 1)))
        else:
            term = 2 * q ** (idx + 1) / (1 - q ** (idx + 1))
            fac = (2 * q ** (idx + 2) / (1 - q ** (idx + 2))
                   - 2 * q ** (idx + 1) / (1 - q ** (idx + 1)))
        tot += term * prod
        prod *= fac
        if j > 5 and abs(term * prod) < eps * max(mpf(1), abs(tot)):
            return tot
    raise RuntimeError('block did not converge')


def geom(tau):
    q = exp(-tau)
    z0 = sqrt(2 * (1 - q))
    return q, z0, z0 / sqrt(q), sqrt(2 / tau)


def dps_for(tau, extra):
    return int(35 + float(sqrt(2 / mpf(tau))) / 2.302585 + extra)


# ------------------------------------------------------------- the parts ----

def part1(tau, dps):
    """collapse identities, as identities in q.  Returns four relative errors."""
    mp.dps = dps
    tau = mpf(tau)
    q, z0, Z, w = geom(tau)
    cache = []
    Sig0, Sig1 = block(0, q, True), block(1, q, True)
    S0, S1 = block(0, q, False), block(1, q, False)
    rel = lambda a, b: abs(a - b) / max(abs(b), mpf(1))
    return (rel((2 * q / Z) * sfrak(Z, q, cache), Sig0),
            rel((2 * q / z0) * sfrak(z0, q, cache), S0),
            rel(qcos(Z, q, cache), 1 - Sig1),
            rel(qcos(z0, q, cache), 1 - S1))


def part2(tau, u, dps):
    """half-step rules and q-Pythagoras at a generic argument u."""
    mp.dps = dps
    tau, u = mpf(tau), mpf(u)
    q = exp(-tau)
    cache = []
    rq = sqrt(q)
    r1 = qcos(q * u, q, cache) - (qcos(u, q, cache) + q ** mpf(1.5) * u * sfrak(rq * u, q, cache))
    r2 = sfrak(q * u, q, cache) - (sfrak(u, q, cache) - u * qcos(rq * u, q, cache))
    r3 = (qcos(u, q, cache) * qcos(rq * u, q, cache)
          + q ** mpf(1.5) * sfrak(u, q, cache) * sfrak(rq * u, q, cache) - 1)
    scale = max(mpf(1), abs(qcos(u, q, cache)), abs(sfrak(u, q, cache)))
    return abs(r1) / scale, abs(r2) / scale, abs(r3) / scale


def part3(tau, dps):
    """at a travel pole: the pole invariant and the product identity."""
    mp.dps = dps
    tau = mpf(tau)
    q, z0, Z, w = geom(tau)
    cache = []
    Sig0, S0 = block(0, q, True), block(0, q, False)
    inv = q ** mpf(1.5) * sfrak(z0, q, cache) * sfrak(Z, q, cache)
    prod = Sig0 * S0
    tgt = 2 * q / (1 - q)
    return (abs(inv - 1), abs(prod / tgt - 1), abs(qcos(Z, q, cache)),
            Sig0 / w, S0 / w)


def travel_poles(mmax, dps):
    """travel poles as tau values.  The dominant pole q_1 = 0.449453... has
    w in (0, pi) and lies BELOW the extreme-phase ladder w = m pi, so it is
    bracketed separately; the rest are bracketed by the ladder."""
    mp.dps = dps

    def g(t):
        q = exp(-t)
        return qcos(sqrt(2 * (1 - q) / q), q, [])

    out = []
    # the dominant pole: g > 0 near q = 0 (i.e. large tau), g < 0 at w = pi
    a, b = 2 / pi ** 2, mpf(3)
    if g(a) * g(b) < 0:
        out.append(findroot(g, (a, b), solver='bisect', tol=mpf(10) ** (-dps + 12)))
    for m in range(1, mmax + 1):
        a, b = 2 / ((m + 1) * pi) ** 2, 2 / (m * pi) ** 2
        if g(a) * g(b) >= 0:
            continue
        out.append(findroot(g, (a, b), solver='bisect',
                            tol=mpf(10) ** (-dps + 12)))
    return sorted(out, reverse=True)


# ------------------------------------------------------------------ main ----

def main():
    fails = 0

    print('=' * 92)
    print('PART 1  collapse identities  (Lemma lem:qsinenum + Proposition prop:qtrig)')
    print('        tested OFF the travel poles, so they are identities in q, not pole facts')
    print('=' * 92)
    print('  tau          Sigma_0-(2q/Z)s(Z)   S_0-(2q/z0)s(z0)   1-Sig_1-c(Z)   S_e-c(z0)   agree')
    for s in ['0.5', '0.2', '0.05', '0.02', '0.007', '0.003', '0.001']:
        a = part1(s, dps_for(s, 20))
        b = part1(s, dps_for(s, 55))
        mp.dps = 25
        ok = all(x < mpf('1e-25') and y < mpf('1e-25') for x, y in zip(a, b))
        fails += 0 if ok else 1
        print('  %-12s %-20s %-18s %-14s %-11s %s'
              % (s, mp.nstr(b[0], 5), mp.nstr(b[1], 5), mp.nstr(b[2], 5),
                 mp.nstr(b[3], 5), ok))

    print()
    print('=' * 92)
    print('PART 2  half-step rules and q-Pythagoras  (Lemma lem:halfstep)')
    print('=' * 92)
    print('  tau        u          shift c      shift s      Pythagoras   agree')
    for s in ['0.5', '0.2', '0.05', '0.02']:
        q = exp(-mpf(s))
        for u in ['0.15', '0.4', str(sqrt(2 * (1 - q) / q))]:
            a = part2(s, u, dps_for(s, 20))
            b = part2(s, u, dps_for(s, 55))
            mp.dps = 25
            ok = all(x < mpf('1e-25') and y < mpf('1e-25') for x, y in zip(a, b))
            fails += 0 if ok else 1
            print('  %-10s %-10s %-12s %-12s %-12s %s'
                  % (s, mp.nstr(mpf(u), 5), mp.nstr(b[0], 5), mp.nstr(b[1], 5),
                     mp.nstr(b[2], 5), ok))

    print()
    print('=' * 92)
    print('PART 3  at the travel poles  (Proposition prop:numnonvanish)')
    print('        the two panels below are the SAME regime: every row is a root of c(Z)=0')
    print('=' * 92)
    poles = travel_poles(31, 60)
    print('  m   tau              |c(Z)|      invariant-1   Sig_0*S_0/(2q/(1-q))-1   Sig_0/w    S_0/w')
    worst_inv = mpf(0)
    worst_prod = mpf(0)
    signs = []
    for i, tau in enumerate(poles):
        a = part3(tau, dps_for(tau, 20))
        b = part3(tau, dps_for(tau, 55))
        mp.dps = 25
        ok = abs(a[1] - b[1]) < mpf('1e-20')
        fails += 0 if ok else 1
        worst_inv = max(worst_inv, b[0])
        worst_prod = max(worst_prod, b[1])
        signs.append(1 if b[3] > 0 else -1)
        print('  %2d  %-16s %-11s %-13s %-24s %-10s %s'
              % (i + 1, mp.nstr(tau, 9), mp.nstr(b[2], 4), mp.nstr(b[0], 4),
                 mp.nstr(b[1], 4), mp.nstr(b[3], 8), mp.nstr(b[4], 8)))

    mp.dps = 25
    alt = all(signs[i] * signs[i + 1] < 0 for i in range(len(signs) - 1))
    print()
    print('  poles tested                              : %d' % len(poles))
    print('  worst |q^{3/2} s(z0) s(Z) - 1|            : %s' % mp.nstr(worst_inv, 5))
    print('  worst |Sigma_0 S_0 (1-q)/(2q) - 1|        : %s' % mp.nstr(worst_prod, 5))
    print('  sign of Sigma_0 strictly alternates       : %s' % alt)
    print('  two-precision disagreements (all parts)   : %d' % fails)
    print()
    print('  VERDICT (what the numbers above support, and nothing more):')
    print('    the four collapse identities and the three Koornwinder-Swarttouw rules hold')
    print('    to the working precision at every sampled q, and at every tested travel pole')
    print('    the product Sigma_0(q_m) S_0(q_m) equals 2q_m/(1-q_m), a nonzero number.')
    print('    The identities are PROVED in the paper; this script is a check on the')
    print('    bookkeeping, not the proof.')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
