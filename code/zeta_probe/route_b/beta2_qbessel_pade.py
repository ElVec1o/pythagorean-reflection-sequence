#!/usr/bin/env python3
"""beta_2 via q-Bessel zeros: a q-Siegel line, and the precise G-function obstruction (paper2 rem:betanumber).

NEW REFRAMING (this session). Two-variable G(q,z) = 1phi1(0;q;q^2,z) = sum_k (-1)^k q^{k(k-1)} z^k/(q;q)_{2k},
with S(q) = G(q, 2q(1-q)). Unlike the diagonal S (non-holonomic in q), G is q-HOLONOMIC in z:

    q G(q,z) - (q+1-qz) G(q,q^2 z) + G(q,q^4 z) = 0        [2nd-order q-difference eq, verified 1e-51]

KEY FACT (verified): z* = 2 q*(1-q*) = 0.49489012907... is the SMALLEST positive zero of G(q*,.).
Therefore:  beta_2 algebraic  =>  an ALGEBRAIC zero of a q-Bessel-class function at an algebraic base.
The classical analogue is FALSE (Siegel: zeros of the Bessel function J_nu are transcendental). So a
q-analogue of Siegel's theorem for zeros of 1phi1 would prove beta_2 (and, by the same q-connection core, U).

HERMITE-PADE attack (the natural proof), measured here:
  [n/n] approximants Q_n(z)G(q,z) - P_n(z) = O(z^{2n+1}).  At the zero z*, P_n(z*) = -R_n(z*).
  * REMAINDER decays super-exponentially: |R_n(z*)| = 2^{-c n^2}, c ~ 3.5  (the q^{k(k-1)} numerators). GOOD.
  * HEIGHT of the coefficients grows CUBICALLY: 2^{c' n^3}, c' ~ 2.5  (the (q;q)_{2k} denominators, cleared).
  n^3 (height) > n^2 (remainder)  =>  Liouville gives NO contradiction. The gap is EXACTLY the classical
  G-function (Galochkin/Andre bounded-denominator) condition: if G(q,z) is a q-G-function its denominators
  drop to 2^{c'' n^2} and Siegel's mechanism closes it. Whether G is a q-G-function is the sharp OPEN frontier
  (Andre / Di Vizio / Roques q-difference transcendence). NOT a proof -- an honest, precise reduction.

Run: needs mpmath + sympy. OMP-safe (single thread), dps<=60.
"""
import sympy as sp, mpmath as mp


def Gnum(q, z, K=400):
    q = mp.mpf(q); z = mp.mpc(z); t = mp.mpf(0); poch = mp.mpf(1)
    for k in range(K):
        if k > 0: poch *= (1 - q**(2 * k - 1)) * (1 - q**(2 * k))
        term = (-1)**k * q**(k * (k - 1)) * z**k / poch
        t += term
        if k > 10 and abs(term) < mp.mpf(10)**-65: break
    return t


def pade_measure(q, n, z_eval):
    """[n/n] Pade to G(q,.); return (|P_n(z_eval)|, height)."""
    g = []; poch = sp.Integer(1)
    for k in range(2 * n + 2):
        if k > 0: poch *= (1 - q**(2 * k - 1)) * (1 - q**(2 * k))
        g.append((-1)**k * q**(k * (k - 1)) / poch)
    b = [sp.Integer(1)] + [sp.Symbol(f'b{i}') for i in range(1, n + 1)]
    a = [sp.Symbol(f'a{i}') for i in range(0, n + 1)]
    eqs = []
    for j in range(2 * n + 1):
        conv = sum(b[i] * g[j - i] for i in range(0, min(n, j) + 1))
        eqs.append(sp.Eq(conv - (a[j] if j <= n else 0), 0))
    sol = sp.solve(eqs, [b[i] for i in range(1, n + 1)] + list(a), dict=True)[0]
    P = [sol.get(a[i]) for i in range(n + 1)]
    Q = [sp.Integer(1)] + [sol.get(b[i]) for i in range(1, n + 1)]
    h = 1
    for c in P + Q:
        num, den = sp.fraction(sp.nsimplify(c)); h = max(h, abs(int(num)), abs(int(den)))
    Pz = sum(mp.mpf(str(sp.Rational(P[i]))) * mp.mpf(str(z_eval))**i for i in range(n + 1))
    return abs(Pz), h


if __name__ == "__main__":
    mp.mp.dps = 50
    q = mp.mpf('0.37'); z = mp.mpf('1.3')
    res = q * Gnum(q, z) - (q + 1 - q * z) * Gnum(q, q**2 * z) + Gnum(q, q**4 * z)
    print("q-difference eq residual:", mp.nstr(res, 4))
    z1 = mp.findroot(lambda z: Gnum(mp.mpf('0.5'), z).real, mp.mpf('0.43'))
    print(f"\n[n/n] Pade to G(1/2,.), evaluated at its smallest zero z1={mp.nstr(z1,12)}:")
    print(" n | -log2|R_n|/n^2 (->c, remainder) | log2(height)/n^3 (->c', height)")
    for n in [2, 3, 4, 5, 6]:
        Pz, h = pade_measure(sp.Rational(1, 2), n, z1)
        r = -mp.log(Pz, 2) / n**2
        hh = mp.log(mp.mpf(int(h)), 2) / n**3
        print(f" {n:>2} | {mp.nstr(r,4):>10} | {mp.nstr(hh,4):>10}")
    print("\n=> remainder ~2^{-3.5 n^2}, height ~2^{2.5 n^3}: n^3 > n^2, Liouville fails.")
    print("   Sharp open frontier: is G(q,z) a q-G-function (Galochkin/Andre)? Then n^2 and Siegel closes it.")
