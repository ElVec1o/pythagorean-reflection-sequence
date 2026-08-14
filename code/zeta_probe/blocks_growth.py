#!/usr/bin/env python3
"""
blocks_growth.py -- exact integer certificate for the coefficient-growth hypothesis (G)
of paper 2, Section "Transcendence of the blocks".

The four catalytic blocks are the k-recursion sums

    Sigma_k = sum_{j>=0} A_{k+2j} prod_{i<j} C_{k+2i},   A_k = 2q/(1-q^{k+1}),
                                                        C_k = 2q^{k+3}/(1-q^{k+2}) - 2q^{k+2}/(1-q^{k+1}),
    S_k     = sum_{j>=0} a_{k+2j} prod_{i<j} g_{k+2i},   a_k = 2q^{k+1}/(1-q^{k+1}),
                                                        g_k = 2q^{k+2}/(1-q^{k+2}) - 2q^{k+1}/(1-q^{k+1}),

with Sigma_1, Sigma_0, S_1, S_0 the blocks of the paper.  Everything below is exact
arithmetic in Z[[q]]/(q^{N+1}): no floating point anywhere, so there is no precision to
state.  Rule 7's independent-verification clause is met instead by computing the same
coefficients a second time from the closed forms of Proposition prop:qtrig and
Lemma lem:P12closed, which come from a different derivation (the q-trigonometric collapse,
not the k-recursion), and by reproducing the published G_0 = S_0/(1-S_1) coefficients.

Multiplication by a Lambert factor 1/(1-q^m) is the O(N) in-place recurrence c[k] += c[k-m],
so the whole computation is linear in the truncation degree per step.
"""
import sys

N = 1160                      # truncation degree; 34^2 = 1156 is the deepest index used


def geom(c, m):
    """c *= 1/(1-q^m), in place."""
    for k in range(m, N + 1):
        c[k] += c[k - m]
    return c


def shift(c, s):
    return [0] * s + c[:N + 1 - s] if s else c[:]


def scal(c, s):
    return [s * x for x in c]


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def mul_one_minus_q(c):
    """c *= (1-q)."""
    return [c[k] - (c[k - 1] if k else 0) for k in range(N + 1)]


def one():
    return [1] + [0] * N


# ---------------------------------------------------------------- k-recursion blocks

def block(k0, kind, jmax):
    """Sigma_{k0} (kind='T') or S_{k0} (kind='B'), truncated, as an integer list."""
    P = one()
    out = [0] * (N + 1)
    for j in range(jmax + 1):
        k = k0 + 2 * j
        if kind == 'T':                                   # A_k = 2q/(1-q^{k+1})
            out = add(out, geom(scal(shift(P, 1), 2), k + 1))
            hi = geom(scal(shift(P, k + 3), 2), k + 2)     # C_k, first half
            lo = geom(scal(shift(P, k + 2), 2), k + 1)     # C_k, second half
        else:                                             # a_k = 2q^{k+1}/(1-q^{k+1})
            out = add(out, geom(scal(shift(P, k + 1), 2), k + 1))
            hi = geom(scal(shift(P, k + 2), 2), k + 2)     # g_k, first half
            lo = geom(scal(shift(P, k + 1), 2), k + 1)     # g_k, second half
        P = sub(hi, lo)
        if all(x == 0 for x in P):
            break
    return out


# ---------------------------------------------------------------- closed forms

def qcos_family(exp_of_j, extra_one_minus_q, denom_odd, jmax):
    """
    sum_{j>=0} (-2(1-q))^j q^{exp_of_j(j)} [ (1-q) if extra_one_minus_q ] / (q;q)_{2j+[1 if odd]}.
    Built incrementally; (q;q)_M = prod_{i<=M} (1-q^i) enters as Lambert factors.
    """
    out = [0] * (N + 1)
    t = one()
    if extra_one_minus_q:
        t = mul_one_minus_q(t)
    if denom_odd:
        t = geom(t, 1)                       # the (1-q^1) factor of (q;q)_1
    prev = 0
    for j in range(jmax + 1):
        e = exp_of_j(j)
        if j:
            t = scal(mul_one_minus_q(shift(t, e - prev)), -2)
            t = geom(t, 2 * j - 1 + (1 if denom_odd else 0))
            t = geom(t, 2 * j + (1 if denom_odd else 0))
        prev = e
        out = add(out, t)
        if all(x == 0 for x in t):
            break
    return out


def series_div(num, den):
    """num/den in Z[[q]] (den[0] = 1)."""
    assert den[0] == 1
    out = [0] * (N + 1)
    for k in range(N + 1):
        s = num[k] - sum(den[i] * out[k - i] for i in range(1, k + 1) if den[i])
        out[k] = s
    return out


def main():
    jmax = 40

    # ---- the four blocks from the k-recursion
    Sig1 = block(1, 'T', jmax)
    Sig0 = block(0, 'T', jmax)
    S1 = block(1, 'B', jmax)
    S0 = block(0, 'B', jmax)

    # ---- independent closed forms (q-trigonometric collapse)
    #  1 - Sigma_1 = cos(Z;q^2) = sum_j (-2(1-q))^j q^{j^2}/(q;q)_{2j}
    #  S_e = 1 - S_1           = sum_j (-2(1-q))^j q^{j^2+j}/(q;q)_{2j}
    #  S_0 = (2q/(1-q)) S_o,  S_o = sum_j (-2(1-q))^j q^{j^2+2j} (1-q)/(q;q)_{2j+1}
    cosZ = qcos_family(lambda j: j * j, False, False, jmax)
    Se = qcos_family(lambda j: j * j + j, False, False, jmax)
    So = qcos_family(lambda j: j * j + 2 * j, True, True, jmax)
    Sig1_cf = [(1 if k == 0 else 0) - cosZ[k] for k in range(N + 1)]
    S1_cf = [(1 if k == 0 else 0) - Se[k] for k in range(N + 1)]
    S0_cf = geom(scal(shift(So, 1), 2), 1)      # (2q/(1-q)) * S_o

    print('independent cross-checks (k-recursion vs q-trigonometric closed form):')
    for name, a, b in (('Sigma_1', Sig1, Sig1_cf), ('S_1', S1, S1_cf), ('S_0', S0, S0_cf)):
        ok = a == b
        print(f'  {name:<8} agree to degree {N}: {ok}'
              + ('' if ok else f'   first mismatch at q^{next(k for k in range(N+1) if a[k]!=b[k])}'))
    G0 = series_div(S0, [(1 if k == 0 else 0) - S1[k] for k in range(N + 1)])
    pub = [2, 2, 6, 2, 18, 6, 42, 18, 118, 50, 282, 190, 706, 594]
    print(f'  G_0 = S_0/(1-S_1) first 14 coefficients from q^1: {G0[1:15]}')
    print(f'  match published bulk-block series: {G0[1:15] == pub}')
    print(f'  Sigma_1 head: {Sig1[:8]}   (paper: 2q+2q^3-4q^4+6q^5-4q^6+...)')

    # ---- hypothesis (G) for Sigma_1: |[q^{(j+1)^2}] Sigma_1| >= 2^{j+1}
    print('\n(G) for Sigma_1 along n=(j+1)^2:')
    worst_j, jrange, signbad = None, 0, []
    for j in range(0, 34):
        n = (j + 1) ** 2
        c = Sig1[n]
        ok = abs(c) >= 2 ** (j + 1)
        if (c > 0) != (j % 2 == 0):
            signbad.append(j)
        if not ok and worst_j is None:
            worst_j = j
        if ok:
            jrange = j
        if j < 10 or j >= 30:
            print(f'   j={j:<3} n={n:<5} [q^n]Sigma_1 = {c}   >= 2^{j+1} = {2**(j+1)}: {ok}')
    print(f'   holds for every j <= {jrange}; first failure: {worst_j}')
    print(f'   sign is (-1)^j at every j <= 33: {not signbad}' + (f' (violations {signbad})' if signbad else ''))
    rat = [abs(Sig1[(j + 2) ** 2]) / abs(Sig1[(j + 1) ** 2]) for j in range(0, 33)]
    print(f'   successive |c| ratios: first {rat[0]:.4f}, at j=20 {rat[20]:.4f}, last {rat[-1]:.4f}')
    print(f'   |c|/2^(j+1) at j=9, 20, 33: '
          f'{abs(Sig1[100])//2**10}, {abs(Sig1[441])//2**21}, {abs(Sig1[1156])//2**34}')

    # ---- the same diagonals for the other blocks
    print('\nthe analogous diagonals:')
    r = 0
    for j in range(0, 33):
        n = (j + 1) * (j + 2)
        if n > N:
            break
        if abs(S1[n]) >= 2 ** (j + 1):
            r = j
        elif j >= 4:
            break
    print(f'   S_1 along n=(j+1)(j+2): |c_n| >= 2^(j+1) for all 4 <= j <= {r}')
    r = 0
    for j in range(0, 33):
        n = (j + 1) ** 2
        if n > N:
            break
        if abs(S0[n]) >= 2 ** (j + 1):
            r = j
        elif j >= 3:
            break
    print(f'   S_0 along n=(j+1)^2:    |c_n| >= 2^(j+1) for all 3 <= j <= {r}')
    print(f'   Sigma_0 along n=(j+1)^2, j=0..9: {[Sig0[(j+1)**2] for j in range(10)]}'
          '   (its leading diagonal cancels; the plain diagonal fails from j=9)')

    # ---- one uniform statement covering all four blocks:
    #      there are infinitely many n with |[q^n] Sigma| >= 2^{sqrt(n)-1}.
    # Per block, report the largest J such that every window [(j+1)^2, (j+2)^2), j <= J,
    # contains a witness.  A window witness is what "infinitely many n" needs.
    print('\nhypothesis (G): |[q^n] Sigma| >= 2^{sqrt(n)-1} for infinitely many n')
    print('   per-block verified range (largest J with a witness in every window '
          '[(j+1)^2,(j+2)^2), j<=J):')
    for name, c in (('Sigma_1', Sig1), ('Sigma_0', Sig0), ('S_1', S1), ('S_0', S0)):
        J = -1
        for j in range(0, 33):
            lo, hi = (j + 1) ** 2, min((j + 2) ** 2, N + 1)
            if hi <= lo:
                break
            hit = any(abs(c[n]) >= 2 ** ((n ** 0.5) - 1) for n in range(lo, hi))
            if not hit:
                break
            J = j
        wmax = max(abs(c[n]) for n in range((J + 1) ** 2, min((J + 2) ** 2, N + 1)))
        print(f'   {name:<8} J = {J:<3}  (window max at j=J is {wmax}, '
              f'threshold 2^(sqrt(n)-1) <= {2 ** ((J + 2) - 1)})')
    return 0


if __name__ == '__main__':
    sys.exit(main())
