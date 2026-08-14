#!/usr/bin/env python3
"""
f2_pole_route.py -- exact integer certificate for the pole route to alternative (a)
of Theorem thm:blocks in paper 2.

The pole route excludes the rational alternative of Polya-Carlson without any
coefficient-growth hypothesis.  It needs exactly four facts about the blocks, all of
them statements in Z[[q]] and all of them checked here in exact integer arithmetic:

  (1) Sigma_1(0) = 0 and S_1(0) = 0, so 1 - Sigma_1 and 1 - S_1 are not the zero
      function;  equivalently  cos(Z;q^2)|_{q=0} = S_e|_{q=0} = 1.
  (2) 1 - Sigma_1 = cos(Z;q^2) = sum_j (-2(1-q))^j q^{j^2}     / (q;q)_{2j},
      1 - S_1     = S_e        = sum_j (-2(1-q))^j q^{j^2+j}   / (q;q)_{2j},
      the two odd-ladder collapses of Proposition prop:qtrig, as identities between the
      k-recursion sums of eq:krec and the q-cosine series of eq:blocks.
  (3) Sigma_0 * S_0 is NOT the function 2q/(1-q):  the product vanishes to order 2 at
      q = 0 and 2q/(1-q) to order 1.  This is what refutes the joint rationality of the
      two numerators, given that Sigma_0 S_0 = 2q/(1-q) holds at every travel pole
      (Proposition prop:numnonvanish).
  (4) the head coefficients of all four blocks, quoted in the text.

Arithmetic model: exact integer arithmetic in Z[[q]]/(q^{N+1}).  No floating point
enters, so there is no precision to state; Rule 7's two-run clause is met by running the
whole certificate at two truncation degrees, and by deriving each block twice, once from
the k-recursion of eq:krec and once from the q-trigonometric closed form, which come from
different derivations.

Usage:  code/zeta_probe/tools/runcap.sh 8000 600 python3 code/zeta_probe/f2_pole_route.py
"""
import sys


def geom(c, m, N):
    """c *= 1/(1-q^m), in place."""
    for k in range(m, N + 1):
        c[k] += c[k - m]
    return c


def shift(c, s, N):
    return [0] * s + c[:N + 1 - s] if s else c[:]


def scal(c, s):
    return [s * x for x in c]


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def mul_one_minus_q(c, N):
    return [c[k] - (c[k - 1] if k else 0) for k in range(N + 1)]


def mul(a, b, N):
    out = [0] * (N + 1)
    for i, ai in enumerate(a):
        if ai:
            for j in range(0, N + 1 - i):
                if b[j]:
                    out[i + j] += ai * b[j]
    return out


def one(N):
    return [1] + [0] * N


def block(k0, kind, N, jmax):
    """Sigma_{k0} (kind='T') or S_{k0} (kind='B') of eq:krec, truncated."""
    P = one(N)
    out = [0] * (N + 1)
    for j in range(jmax + 1):
        k = k0 + 2 * j
        if kind == 'T':                                     # A_k = 2q/(1-q^{k+1})
            out = add(out, geom(scal(shift(P, 1, N), 2), k + 1, N))
            hi = geom(scal(shift(P, k + 3, N), 2), k + 2, N)  # C_k, first half
            lo = geom(scal(shift(P, k + 2, N), 2), k + 1, N)  # C_k, second half
        else:                                               # alpha_k = 2q^{k+1}/(1-q^{k+1})
            out = add(out, geom(scal(shift(P, k + 1, N), 2), k + 1, N))
            hi = geom(scal(shift(P, k + 2, N), 2), k + 2, N)  # gamma_k, first half
            lo = geom(scal(shift(P, k + 1, N), 2), k + 1, N)  # gamma_k, second half
        P = sub(hi, lo)
        if all(x == 0 for x in P):
            break
    return out


def qcos(exp_of_j, N, jmax):
    """sum_{j>=0} (-2(1-q))^j q^{exp_of_j(j)} / (q;q)_{2j}."""
    out = [0] * (N + 1)
    t = one(N)
    prev = 0
    for j in range(jmax + 1):
        e = exp_of_j(j)
        if j:
            t = scal(mul_one_minus_q(shift(t, e - prev, N), N), -2)
            t = geom(t, 2 * j - 1, N)
            t = geom(t, 2 * j, N)
        prev = e
        out = add(out, t)
        if all(x == 0 for x in t):
            break
    return out


def run(N, jmax):
    ok = True
    Sig1 = block(1, 'T', N, jmax)
    Sig0 = block(0, 'T', N, jmax)
    S1 = block(1, 'B', N, jmax)
    S0 = block(0, 'B', N, jmax)
    cosZ = qcos(lambda j: j * j, N, jmax)              # = 1 - Sigma_1
    Se = qcos(lambda j: j * j + j, N, jmax)            # = 1 - S_1

    print(f'--- truncation degree N = {N} -------------------------------------------')

    # (4) heads
    print('  head coefficients (from q^0):')
    for name, c in (('Sigma_1', Sig1), ('Sigma_0', Sig0), ('S_1', S1), ('S_0', S0),
                    ('cos(Z;q^2)', cosZ), ('S_e', Se)):
        print(f'    {name:<11} {c[:7]}')

    # (1) constant terms
    for name, c in (('Sigma_1', Sig1), ('Sigma_0', Sig0), ('S_1', S1), ('S_0', S0)):
        good = (c[0] == 0)
        ok &= good
        print(f'  (1) {name}(0) = {c[0]}   [need 0]: {"PASS" if good else "FAIL"}')
    for name, c in (('cos(Z;q^2)', cosZ), ('S_e', Se)):
        good = (c[0] == 1)
        ok &= good
        print(f'  (1) {name}(0) = {c[0]}   [need 1]: {"PASS" if good else "FAIL"}')

    # (2) the two odd-ladder collapses
    one_minus = lambda c: [(1 if k == 0 else 0) - c[k] for k in range(N + 1)]
    for name, a, b in (('1 - Sigma_1 = cos(Z;q^2)', one_minus(Sig1), cosZ),
                       ('1 - S_1     = S_e       ', one_minus(S1), Se)):
        good = (a == b)
        ok &= good
        extra = '' if good else f'  first mismatch at q^{next(k for k in range(N+1) if a[k]!=b[k])}'
        print(f'  (2) {name} to degree {N}: {"PASS" if good else "FAIL"}{extra}')

    # (3) Sigma_0 S_0 is not 2q/(1-q)
    prod = mul(Sig0, S0, N)
    inv = geom(scal(shift(one(N), 1, N), 2), 1, N)      # 2q/(1-q)
    ordp = next((k for k in range(N + 1) if prod[k]), None)
    ordi = next((k for k in range(N + 1) if inv[k]), None)
    good = (prod != inv) and ordp == 2 and ordi == 1
    ok &= good
    print(f'  (3) Sigma_0*S_0 head {prod[:5]}, order of vanishing at q=0: {ordp}')
    print(f'      2q/(1-q)   head {inv[:5]}, order of vanishing at q=0: {ordi}')
    print(f'      Sigma_0*S_0 != 2q/(1-q) in Z[[q]]: {"PASS" if good else "FAIL"}')

    print(f'  ALL CHECKS AT N = {N}: {"PASS" if ok else "FAIL"}')
    return ok


def se_alternation(dps, mmax=40):
    """
    Falsification pass for Lemma lem:infzeros, in mpmath at the stated precision (NOT interval
    arithmetic).  W(tau) = sqrt(2/tau) exp(-tau/2) is strictly decreasing; solve W(tau) = m pi for
    m = 4..mmax, evaluate S_e = sum_j (-2(1-q))^j q^{j(j+1)}/(q;q)_{2j} there, and check
      (i)  sign(S_e) = (-1)^m at every one of them,
      (ii) tau^{[m]} < 2/(m pi)^2 <= tau_4 = 0.012665  (the bound quoted in the lemma),
      (iii) S_e has a sign change, hence a zero, in every bracket (tau^{[m+1]}, tau^{[m]}).
    The series for S_e cancels heavily (terms up to j ~ 1/sqrt(tau), with intermediate magnitudes
    far above the sum), so the working precision has to be well above the answer: at dps = 30 the
    sign test already fails for some m <= 40 and the failure is a precision artifact, not a sign
    change.  The two runs below are therefore at dps 60 and 100.
    """
    from mpmath import mp, mpf, sqrt, exp, pi, findroot, log
    mp.dps = dps

    def W(tau):
        return sqrt(2 / tau) * exp(-tau / 2)

    def Se(tau, K=600):
        q = exp(-tau)
        s, term, den = mpf(0), mpf(1), mpf(1)
        for j in range(K):
            if j:
                den *= (1 - q ** (2 * j - 1)) * (1 - q ** (2 * j))
                term = (-2 * (1 - q)) ** j * q ** (j * (j + 1)) / den
            s += term
            if j > 10 and abs(term) < mpf(10) ** (-dps - 10):
                break
        return s

    taus, signs = {}, {}
    for m in range(4, mmax + 1):
        # W is strictly decreasing, so plain bisection on a bracket; it stays real by construction.
        lo, hi = mpf(2) / (m * pi) ** 2 / 2, mpf(2) / (m * pi) ** 2
        assert W(lo) > m * pi > W(hi)
        for _ in range(8 * dps):
            mid = (lo + hi) / 2
            if W(mid) > m * pi:
                lo = mid
            else:
                hi = mid
        t = (lo + hi) / 2
        taus[m] = t
        signs[m] = 1 if Se(t) > 0 else -1
    ok_sign = all(signs[m] == (-1) ** m for m in taus)
    ok_bound = all(taus[m] < mpf(2) / (m * pi) ** 2 for m in taus)
    ok_dec = all(taus[m + 1] < taus[m] for m in range(4, mmax))
    tau4 = taus[4]
    print(f'  dps={dps}: tau^[4] = {mp.nstr(tau4, 8)} < 2/(4 pi)^2 = '
          f'{mp.nstr(mpf(2)/(4*pi)**2, 8)}: {bool(tau4 < mpf(2)/(4*pi)**2)}')
    print(f'  dps={dps}: sign(S_e) = (-1)^m at all {len(taus)} points m=4..{mmax}: {ok_sign}')
    print(f'  dps={dps}: tau^[m] < 2/(m pi)^2 at all points: {ok_bound}; '
          f'tau^[m] strictly decreasing: {ok_dec}')
    print(f'  dps={dps}: |S_e| at m=4,5,6: '
          + ', '.join(mp.nstr(Se(taus[m]), 6) for m in (4, 5, 6)))
    return ok_sign and ok_bound and ok_dec, [mp.nstr(taus[m], 12) for m in range(4, 9)]


def main():
    ok = True
    print('PART 1 -- exact integer arithmetic in Z[[q]]/(q^{N+1})\n')
    for N, jmax in ((120, 40), (400, 40)):
        ok &= run(N, jmax)
        print()
    print('PART 2 -- lem:infzeros falsification pass (mpmath mpf, two precisions, NOT intervals)')
    a, ta = se_alternation(60)
    b, tb = se_alternation(100)
    agree = (ta == tb)
    ok &= a and b and agree
    print(f'  two-precision agreement on tau^[4..8] to 12 digits: {agree}')
    print()
    print('VERDICT:', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
