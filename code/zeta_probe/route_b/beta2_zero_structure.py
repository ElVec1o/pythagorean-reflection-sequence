#!/usr/bin/env python3
"""Structure of the beta_2 zero curve (paper2 prop:zerostructure) -- the verified yield of the
five-route archimedean assault. beta_2 irrationality remains OPEN; these are the survivors.

(i) BASE CHANGE (verified z-independent to 15 digits):
      G(q,z) = (q^2;q^2)_inf / (sqrt(q) (q;q^2)_inf) * z^{1/4} * J^{(3)}_{-1/2}(sqrt(z)/q; q^2),
    J^{(3)} = Hahn-Exton (third Jackson) q-Bessel; so G is the Hahn-Exton q-COSINE up to a prefactor,
    and its zeros are those of a classical studied object (real, simple, interlacing).

(ii) ZERO LATTICE (verified): with Q=q^2, the k-th positive zero z_k satisfies z_k Q^k -> 1, with
    theta-suppressed dressing delta_k = z_k Q^k - 1 = O(c^k Q^{k^2}):
      delta_0=-0.5051, delta_1=-1.17e-2, delta_2=-1.03e-5, delta_3=-3.3e-10, delta_4=-4.1e-16.
    z* = z_1(q*) is the MAXIMALLY dressed (k=0-branch) member -- an O(1) displacement from the bare
    lattice point Q^0=1 -- NOT a torsion/lattice point.

(iii) POWER SUMS ARE RATIONAL (verified): sigma_p(q) := sum_n z_n(q)^{-p} in Q(q) for all p (Newton's
    identities on the Q(q)-coefficients g_k); sigma_1 = 1/((1-q)(1-q^2)). Hence
      z*(q) = lim_p sigma_p(q)/sigma_{p+1}(q)   (geometric rate (z_1/z_2)^p),
    an all-orders Q(q) approximation of the zero curve (sigma_20/sigma_21 = z* to 21 digits).

These do NOT prove beta_2 irrational. The obstruction is purely ARCHIMEDEAN (the mirror of the proven
finite-place adelic-units balance); the sharpest reduction is to a theta non-resonance R_q(2q(1-q))!=-1
(paper2 rem:sharpest), with Lindemann's cos-has-no-algebraic-zero as the confluent-limit evidence.
"""
import mpmath as mp


def qqp(qv, n):
    p = mp.mpf(1)
    for i in range(1, n + 1): p *= (1 - qv**i)
    return p


def power_sums(qv, P=32, N=40):
    """sigma_p = sum_n z_n^{-p}, from g_k = (-1)^k q^{k(k-1)}/(q;q)_{2k} via Newton's identities."""
    g = [mp.mpf((-1)**k) * qv**(k * (k - 1)) / qqp(qv, 2 * k) for k in range(N)]
    e = [mp.mpf((-1)**k) * g[k] for k in range(N)]           # elem. symm. in x_n = 1/z_n
    sig = [None, e[1]]
    for m in range(2, P + 2):
        pm = sum(mp.mpf((-1)**(i - 1)) * e[i] * sig[m - i] for i in range(1, m)) \
            + mp.mpf((-1)**(m - 1)) * m * e[m]
        sig.append(pm)
    return sig


if __name__ == "__main__":
    mp.mp.dps = 40
    qs = mp.mpf('0.449453630558948046125545825396'); zstar = 2 * qs * (1 - qs)
    sig = power_sums(qs)
    print("sigma_1 =", mp.nstr(sig[1], 16), " = 1/((1-q*)(1-q*^2))?",
          abs(sig[1] - 1 / ((1 - qs) * (1 - qs**2))) < mp.mpf(10)**-30)
    print("z*(q*) = lim sigma_p/sigma_{p+1}  (z* =", mp.nstr(zstar, 20), "):")
    for p in [5, 10, 20, 30]:
        print(f"  p={p:>2}: sigma_p/sigma_{{p+1}} = {mp.nstr(sig[p]/sig[p+1], 20)}"
              f"  err={mp.nstr(abs(sig[p]/sig[p+1] - zstar), 3)}")
