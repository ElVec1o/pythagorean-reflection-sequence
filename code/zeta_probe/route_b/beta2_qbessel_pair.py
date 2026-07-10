#!/usr/bin/env python3
"""The explicit q-Bessel PAIR behind beta_2, and the q-Wronskian (paper2 rem:betanumber).

The q-difference equation q G(z) - (q+1-qz) G(q^2 z) + G(q^4 z) = 0 (companion matrix
A(z)=[[0,1],[-q,q+1-qz]], det A = q constant) has TWO solutions with Frobenius exponents 0 and 1/2:

  * G(z)  = sum_k (-1)^k q^{k(k-1)} z^k / (q;q)_{2k}          [exponent 0, the beta_2 function; S(q)=G(q,2q(1-q))]
  * G~(z) = z^{1/2} H(z),  H(z)=sum_k (-1)^k q^{k^2}(1-q) z^k/(q;q)_{2k+1}   [exponent 1/2]

DERIVED (this session): substituting G~=z^{1/2}H into the equation gives H's dual recurrence
    h_k (1-q^{2k})(1-q^{2k+1}) = -q^{2k-1} h_{k-1},  h_0=1,
so H solves  H(z) - (q+1-qz)H(q^2 z) + q H(q^4 z) = 0  (the "conjugate" equation).

EXACT q-WRONSKIAN (Casoratian), verified to 30 digits:
    q G(z) H(q^2 z) - G(q^2 z) H(z) = q - 1     (constant, matching det A = q, W(z)=c z^{1/2}).
At the smallest zero z* = 2q*(1-q*) of G(q*,.):  G(q*, q*^2 z*) * H(q*, z*) = 1 - q*   [exact algebraic relation].

This is the machinery for the q-Siegel (Shidlovskii) construction: the two solutions + q-Wronskian are
exactly what balanced Hermite-Pade approximants are built from. The remaining research is to assemble
these into approximants with quadratic (n^2) q-denominators -- the naive [n/n] Pade has super-quadratic
denominators (q-degrees 34,89 at n=2,3, spurious Hankel factors), so the balanced construction is needed.
NOT a proof of beta_2; the explicit pair + q-Wronskian are the verified prerequisites.

Numerical (mpmath, dps 40, single thread). Fast.
"""
import mpmath as mp


def qq(qv, n):
    p = mp.mpf(1)
    for i in range(1, n + 1): p = p * (1 - qv**i)
    return p


def G(qv, zv, K=300):
    t = mp.mpf(0)
    for k in range(K):
        term = mp.mpf((-1)**k) * qv**(k * (k - 1)) * zv**k / qq(qv, 2 * k)
        t = t + term
        if k > 10 and abs(term) < mp.mpf(10)**-45: break
    return t


def H(qv, zv, K=300):
    t = mp.mpf(0)
    for k in range(K):
        term = mp.mpf((-1)**k) * qv**(k * k) * (1 - qv) * zv**k / qq(qv, 2 * k + 1)
        t = t + term
        if k > 10 and abs(term) < mp.mpf(10)**-45: break
    return t


if __name__ == "__main__":
    mp.mp.dps = 40
    qv, zv = mp.mpf('0.31'), mp.mpf('1.17')
    print("G equation residual:", mp.nstr(qv*G(qv, zv) - (qv+1-qv*zv)*G(qv, qv**2*zv) + G(qv, qv**4*zv), 4))
    print("H equation residual:", mp.nstr(H(qv, zv) - (qv+1-qv*zv)*H(qv, qv**2*zv) + qv*H(qv, qv**4*zv), 4))
    cas = qv*G(qv, zv)*H(qv, qv**2*zv) - G(qv, qv**2*zv)*H(qv, zv)
    print("q-Wronskian q G(z)H(q^2z)-G(q^2z)H(z) =", mp.nstr(cas, 22), " = q-1?", abs(cas-(qv-1)) < mp.mpf(10)**-30)
    qs = mp.mpf('0.449453630558948046125545825396'); zs = 2*qs*(1-qs)
    print("at zero: G(q*,z*)=", mp.nstr(G(qs, zs), 5),
          " ; G(q*,q*^2 z*)*H(q*,z*)=", mp.nstr(G(qs, qs**2*zs)*H(qs, zs), 18),
          " = 1-q*?", abs(G(qs, qs**2*zs)*H(qs, zs) - (1-qs)) < mp.mpf(10)**-28)
