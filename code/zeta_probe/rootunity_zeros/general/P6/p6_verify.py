"""
P6 independent sanity check (mpmath, 320 digits): re-derive q*, beta2, and run a small-basis
PSLQ search. This is a lightweight cross-check of the pre-existing, much stronger LLL
certificate in private/ROOM/Beta2/g1_certificate/ (2090-digit bracket, degree<=16 height<10^120
etc.) -- it is NOT a new proof, just independent reproduction to ~60 significant digits plus a
PSLQ pass against a small fixed basis.

Wrap with: perl -e 'alarm 290; exec @ARGV' python3 p6_verify.py
"""
import mpmath as mp
mp.mp.dps = 320


def S(q, K=60):
    # paper2 rem:betanumber series: telescoping continued-fraction-type q-series in the
    # BASE variable q (not a coefficient-generating function in a separate variable).
    w = 2 * q * (1 - q)
    tot = mp.mpf(1)
    term = mp.mpf(1)
    for k in range(1, K):
        term *= -q ** (2 * (k - 1)) * w / ((1 - q ** (2 * k - 1)) * (1 - q ** (2 * k)))
        tot += term
    return tot


def main():
    q = mp.mpf('0.4494536305589480461255458')
    for _ in range(60):
        h = mp.mpf(10) ** (-mp.mp.dps // 2)
        q -= S(q) / ((S(q + h) - S(q - h)) / (2 * h))
    print("residual S(q*) =", mp.nstr(S(q), 5))
    beta2 = 1 / mp.sqrt(q)
    print("q*    =", mp.nstr(q, 60))
    print("beta2 =", mp.nstr(beta2, 60))

    phi = (1 + mp.sqrt(5)) / 2
    vals = [mp.mpf(1), beta2, beta2 ** 2, beta2 ** 3, mp.pi, mp.e, mp.log(2), mp.sqrt(2), phi]
    rel = mp.pslq(vals, maxsteps=2000, maxcoeff=10 ** 6)
    print("PSLQ small-basis [1,beta2,beta2^2,beta2^3,pi,e,log2,sqrt2,phi]:", rel)

    vals2 = [beta2 ** i for i in range(7)]
    rel2 = mp.pslq(vals2, maxsteps=3000, maxcoeff=10 ** 8)
    print("PSLQ deg<=6 integer relation for beta2 alone:", rel2)


if __name__ == "__main__":
    main()
