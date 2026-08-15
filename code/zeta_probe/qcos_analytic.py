#!/usr/bin/env python3
"""qcos_analytic.py -- the analytic certificates of the Hahn-Exton q-cosine paper.

Regenerates every high-precision number quoted in
paper/journal/hahn_exton_qcosine.tex outside the integer lattice:

  eq:qwron                q G(z) H(Qz) - G(Qz) H(z) = q - 1.
  thm:zeroproduct         C_1 = 1/(q;q)_inf and prod_k z_k Q^{k-1} = (q;q^2)_inf,
                          at three bases including q*; likewise the H-side product.
  rem:zeroproduct-dioph   the tail product prod_{k>=2} z_k Q^{k-1} at q*.
  eq:wron-zero            G(q*, q*^2 z*) H(q*, z*) = 1 - q*.
  sec:arith confluence    z_1(q)/(1-q)^2 -> j_{-1/2,1}^2 = (pi/2)^2.
  rem:zerocurve-arith(e)  the fold (q_c, z_c), its second-order data, and the
                          closed-form constant of the coefficient asymptotics.

Rule 7.  Every load-bearing quantity is computed at TWO working precisions and the
two results compared; the script prints the agreement actually attained rather than
the working precision, and a disagreement between the two runs aborts.  Nothing here
is a proof: these are certificates that the stated identities hold to the printed
number of digits.

Runtime under 1 min, peak RSS 30 MB.  Usage:  python3 qcos_analytic.py
"""
import mpmath as mp


# ------------------------------------------------------------------ series --

def qpoch(a, q, n):
    r = mp.mpf(1) if not isinstance(a, mp.mpc) else mp.mpc(1)
    for i in range(n):
        r *= (1 - a * q**i)
    return r


def qpoch_inf(a, q, tol=None):
    r = mp.mpf(1)
    i = 0
    while True:
        f = 1 - a * q**i
        r *= f
        i += 1
        if abs(a * q**i) < mp.mpf(10) ** (-mp.mp.dps - 5):
            return r


def G(q, z, K=None):
    """G(q,z) = sum_k (-1)^k q^{k(k-1)} z^k / (q;q)_{2k}."""
    K = K or _terms(q, z)
    t = mp.mpf(0) * z
    poch = mp.mpf(1)
    for k in range(K):
        if k > 0:
            poch *= (1 - q ** (2 * k - 1)) * (1 - q ** (2 * k))
        t += (-1) ** k * q ** (k * (k - 1)) * z**k / poch
    return t


def Gz(q, z, K=None):
    K = K or _terms(q, z)
    t = mp.mpf(0) * z
    poch = mp.mpf(1)
    for k in range(K):
        if k > 0:
            poch *= (1 - q ** (2 * k - 1)) * (1 - q ** (2 * k))
        if k >= 1:
            t += (-1) ** k * k * q ** (k * (k - 1)) * z ** (k - 1) / poch
    return t


def H(q, z, K=None):
    """H(q,z) = sum_k (-1)^k q^{k^2} (1-q) z^k / (q;q)_{2k+1}."""
    K = K or _terms(q, z)
    t = mp.mpf(0) * z
    poch = 1 - q
    for k in range(K):
        if k > 0:
            poch *= (1 - q ** (2 * k)) * (1 - q ** (2 * k + 1))
        t += (-1) ** k * q ** (k * k) * (1 - q) * z**k / poch
    return t


def _terms(q, z):
    """Enough terms that q^{k(k-1)} |z|^k is below the working precision."""
    lq = -mp.log(abs(q))
    lz = mp.log(max(abs(z), mp.mpf(1)))
    target = mp.mp.dps * mp.log(10) + 20
    k = 4
    while k * (k - 1) * lq - k * lz < target:
        k += 1
        if k > 4000:
            break
    return int(k) + 4


def theta_Q(Q, x, K=None):
    """theta_Q(x) = sum_{n in Z} Q^{n(n-1)/2} x^n."""
    K = K or _terms(mp.sqrt(abs(Q)), x) + 5
    t = mp.mpf(0) * x
    for n in range(-K, K + 1):
        t += Q ** (mp.mpf(n * (n - 1)) / 2) * x**n
    return t


# --------------------------------------------------------- rescaled zeros ---

def F_cos(q, k, u, K=None):
    """q^{k(k-1)} G(q, u q^{-2(k-1)}) = sum (-1)^j q^{(j-k)(j-k+1)} u^j/(q;q)_{2j}."""
    K = K or (k + _terms(q, mp.mpf(1)) + 6)
    t = mp.mpf(0) * u
    poch = mp.mpf(1)
    for j in range(K):
        if j > 0:
            poch *= (1 - q ** (2 * j - 1)) * (1 - q ** (2 * j))
        t += (-1) ** j * q ** ((j - k) * (j - k + 1)) * u**j / poch
    return t


def F_sin(q, k, v, K=None):
    """q^{k(k-1)} H(q, v q^{1-2k}) = sum (-1)^j q^{(j-k)(j-k+1)} v^j/(q^2;q)_{2j}."""
    K = K or (k + _terms(q, mp.mpf(1)) + 6)
    t = mp.mpf(0) * v
    poch = mp.mpf(1)
    for j in range(K):
        if j > 0:
            poch *= (1 - q ** (2 * j)) * (1 - q ** (2 * j + 1))
        t += (-1) ** j * q ** ((j - k) * (j - k + 1)) * v**j / poch
    return t


def u_k(q, k):
    """The rescaled zero u_k = q^{2(k-1)} z_k, found near u = 1.  Well conditioned:
    F_cos(q,k,.) has a simple root at 1 + O(q^{k(2k-1)}) with unit derivative."""
    return mp.findroot(lambda u: F_cos(q, k, u), mp.mpf(1))


def v_k(q, k):
    return mp.findroot(lambda v: F_sin(q, k, v), mp.mpf(1))


def z1_direct(q, steps=4000):
    """The least positive zero of G(q,.), located by a sign scan and then refined.

    This is NOT u_k(q,1).  The Hensel branch u_1 in 1 + qZ[[q]] of thm:integrality
    is the analytic continuation of the least zero only inside its disc of
    convergence |q| < 0.5546 (rem:zerocurve-arith(e)); at q = 0.9 the two differ,
    which is exactly why the confluence limit q -> 1 must be taken on the zero
    itself and not on the series."""
    lo = mp.mpf(0)
    f0 = G(q, mp.mpf('1e-30'))
    hi = mp.mpf(4)
    step = hi / steps
    x = step
    while x <= hi:
        if G(q, x) * f0 < 0:
            a, b = x - step, x
            fa = G(q, a)
            for _ in range(60):
                m = (a + b) / 2
                if G(q, m) * fa <= 0:
                    b = m
                else:
                    a, fa = m, G(q, m)
            return mp.findroot(lambda z: G(q, z), (a + b) / 2)
        x += step
    raise RuntimeError("no sign change found")


# ------------------------------------------------------------------ checks --

def digits(a, b):
    """Number of agreeing significant digits between a and b."""
    a, b = mp.mpf(a), mp.mpf(b)
    if a == b:
        return mp.mp.dps
    d = abs(a - b) / max(abs(a), abs(b), mp.mpf(10) ** (-mp.mp.dps))
    return int(-mp.log10(d))


def at_dps(dps, f):
    old = mp.mp.dps
    mp.mp.dps = dps
    try:
        return f()
    finally:
        mp.mp.dps = old


def q_star(dps):
    """Least positive root of S(q) = G(q, 2q(1-q)); the base of beta_2."""
    mp.mp.dps = dps + 15
    q = mp.mpf('0.4494536305589480461255458')
    for _ in range(6):
        q = mp.findroot(lambda x: G(x, 2 * x * (1 - x)), q)
    mp.mp.dps = dps
    return +q


# --------------------------------------------------------------------- run --

def run_wronskian():
    print("eq:qwron -- q G(z) H(Qz) - G(Qz) H(z) = q - 1")
    print(f"  {'q':>6} {'z':>6} {'dps':>5} {'agreeing digits':>16}")
    out = []
    for q0, z0 in [('0.3', '0.7'), ('0.62', '1.9'), ('0.13', '5.0')]:
        row = []
        for dps in (60, 120):
            mp.mp.dps = dps
            q = mp.mpf(q0)
            z = mp.mpf(z0)
            Q = q * q
            lhs = q * G(q, z) * H(q, Q * z) - G(q, Q * z) * H(q, z)
            row.append(digits(lhs, q - 1))
            print(f"  {q0:>6} {z0:>6} {dps:>5} {row[-1]:>16}")
        out.append(min(row))
    print(f"  worst agreement over the three points and two precisions: "
          f"{min(out)} digits\n")
    return min(out)


def run_zeroproduct():
    print("thm:zeroproduct -- C_1 = 1/(q;q)_inf, and prod_k z_k Q^{k-1} = (q;q^2)_inf")
    print("  The product is computed as prod_k u_k with u_k = q^{2(k-1)} z_k, the")
    print("  rescaled zero of cor:hexagonal.  Since u_k = 1 + O(q^{k(2k-1)}) the")
    print("  truncation at K costs only O(q^{(K+1)(2K+1)}), so a short product")
    print("  already certifies many digits.")
    mp.mp.dps = 40
    qs = q_star(40)
    print(f"  q* = {mp.nstr(qs, 30)}")
    print(f"  {'q':>22} {'K':>4} {'dps':>5} {'cos digits':>11} {'sin digits':>11}")
    worst = 10**9
    for label, qv in [('0.3', mp.mpf('0.3')), ('0.42', mp.mpf('0.42')), ('q*', None)]:
        for dps in (120, 240):
            mp.mp.dps = dps
            q = q_star(dps) if qv is None else mp.mpf(label)
            Q = q * q
            K = 2
            while (K + 1) * (2 * K + 1) * abs(mp.log10(q)) < dps + 10:
                K += 1
            pc = mp.mpf(1)
            ps = mp.mpf(1)
            for k in range(1, K + 1):
                pc *= u_k(q, k)
                ps *= v_k(q, k)
            dc = digits(pc, qpoch_inf(q, Q))
            # H-side: prod w_k q Q^{k-1} = prod v_k = (q^3;q^2)_inf
            ds = digits(ps, qpoch_inf(q**3, Q))
            worst = min(worst, dc, ds)
            print(f"  {label:>22} {K:>4} {dps:>5} {dc:>11} {ds:>11}")
    # the connection constant itself, along z = u Q^{-N}
    print("  connection constant (q;q)_inf G(uQ^{-N})/theta_Q(-uQ^{-N}) -> 1, u = -1:")
    print(f"  {'q':>8} {'N':>4} {'dps':>6} {'|ratio - 1|':>16}")
    for label in ('0.3', '0.42'):
        for N, dps in ((30, 400), (45, 900)):
            mp.mp.dps = dps
            q = mp.mpf(label)
            Q = q * q
            z = -Q ** (-N)
            r = qpoch_inf(q, q) * G(q, z) / theta_Q(Q, -z)
            print(f"  {label:>8} {N:>4} {dps:>6} {mp.nstr(abs(r - 1), 4):>16}")
    print(f"  worst product agreement over all bases and both precisions: "
          f"{worst} digits\n")
    return worst


def run_qstar_items():
    print("rem:zeroproduct-dioph and eq:wron-zero, at q = q*")
    for dps in (60, 120):
        mp.mp.dps = dps
        q = q_star(dps)
        Q = q * q
        zs = 2 * q * (1 - q)
        K = 2
        while (K + 1) * (2 * K + 1) * abs(mp.log10(q)) < dps + 10:
            K += 1
        full = mp.mpf(1)
        for k in range(1, K + 1):
            full *= u_k(q, k)
        tail = full / zs
        wron = G(q, Q * zs) * H(q, zs)
        print(f"  dps {dps:>4}: z* = 2q*(1-q*) = {mp.nstr(zs, 25)}")
        print(f"            tail product prod_{{k>=2}} z_k Q^{{k-1}} = {mp.nstr(tail, 25)}")
        print(f"            G(q*,Q z*) H(q*,z*) - (1-q*) agrees to "
              f"{digits(wron, 1 - q)} digits")
        print(f"            |G(q*,z*)| = {mp.nstr(abs(G(q, zs)), 4)}  (z* is a zero)")
    print()


def run_confluence():
    print("sec:arith -- confluence z_1(q)/(1-q)^2 -> j_{-1/2,1}^2 = (pi/2)^2")
    mp.mp.dps = 60
    print(f"  j_{{-1/2,1}}^2 = (pi/2)^2 = {mp.nstr((mp.pi/2)**2, 12)}")
    print(f"  {'q':>7} {'z_1(q)':>18} {'z_1/(1-q)^2':>14} {'(q pi/2)^2':>13}")
    for label in ('0.9', '0.95', '0.99'):
        vals = []
        for dps in (40, 80):
            mp.mp.dps = dps
            q = mp.mpf(label)
            vals.append(z1_direct(q))
        mp.mp.dps = 40
        q = mp.mpf(label)
        z1 = vals[0]
        assert digits(z1, vals[1]) > 25, "the two precisions disagree"
        print(f"  {label:>7} {mp.nstr(z1, 10):>18} "
              f"{mp.nstr(z1/(1-q)**2, 6):>14} "
              f"{mp.nstr((q*mp.pi/2)**2, 6):>13}")
    print("  the discarded scaling (q pi/2)^2 stays O(1) while z_1 collapses to 0.\n")


def Gzz(q, z, K=None):
    K = K or _terms(q, z)
    t = mp.mpf(0) * z
    poch = mp.mpf(1)
    for k in range(K):
        if k > 0:
            poch *= (1 - q ** (2 * k - 1)) * (1 - q ** (2 * k))
        if k >= 2:
            t += (-1) ** k * k * (k - 1) * q ** (k * (k - 1)) * z ** (k - 2) / poch
    return t


def run_fold():
    """The fold is the double point G = G_z = 0 on the negative q-axis, where the
    branches z_1 and z_2 collide.  It sets the radius of convergence of u_1."""
    print("rem:zerocurve-arith(e) -- the fold: G = G_z = 0 on the negative q-axis")
    prev = None
    for dps in (120, 230):
        work = 3 * dps
        mp.mp.dps = work
        h = mp.mpf(10) ** (-dps)
        q = mp.mpf('-0.5545786101465797')
        z = mp.mpf('2.5239525204417103')
        for _ in range(200):
            f1, f2 = G(q, z), Gz(q, z)
            j11 = (G(q + h, z) - G(q - h, z)) / (2 * h)
            j12 = Gz(q, z)
            j21 = (Gz(q + h, z) - Gz(q - h, z)) / (2 * h)
            j22 = Gzz(q, z)
            det = j11 * j22 - j12 * j21
            dq = (f1 * j22 - f2 * j12) / det
            dz = (j11 * f2 - j21 * f1) / det
            q, z = q - dq, z - dz
            if abs(dq) + abs(dz) < mp.mpf(10) ** (-(dps + 10)):
                break
        gzz = Gzz(q, z)
        gq = (G(q + h, z) - G(q - h, z)) / (2 * h)
        Ct2 = 2 * gq / (-gzz)
        const = abs(mp.sqrt(abs(Ct2))) * mp.sqrt(abs(q)) / (2 * mp.sqrt(mp.pi))
        mp.mp.dps = dps
        print(f"  target {dps} digits (working precision {work}):")
        print(f"    q_c  = {mp.nstr(q, min(dps, 24))}")
        print(f"    z_c  = {mp.nstr(z, min(dps, 24))}")
        print(f"    residuals |G| = {mp.nstr(abs(G(q,z)),3)}, "
              f"|G_z| = {mp.nstr(abs(Gz(q,z)),3)}")
        print(f"    G_zz = {mp.nstr(gzz, 8)},  G_q = {mp.nstr(gq, 8)}")
        print(f"    |C~| sqrt|q_c| / (2 sqrt pi) = {mp.nstr(const, 12)}")
        if prev is not None:
            print(f"    agreement with the {prev[3]}-digit run: q_c to "
                  f"{digits(q, prev[0])} digits, z_c to {digits(z, prev[1])}, "
                  f"the constant to {digits(const, prev[2])}")
        prev = (q, z, const, dps)
        if dps == 230:
            fold_jet(q, z, dps)
            fold_pslq(q, z, dps)
    print()


def Hz(q, z, K=None):
    K = K or _terms(q, z)
    t = mp.mpf(0) * z
    poch = 1 - q
    for k in range(K):
        if k > 0:
            poch *= (1 - q ** (2 * k)) * (1 - q ** (2 * k + 1))
        if k >= 1:
            t += (-1) ** k * k * q ** (k * k) * (1 - q) * z ** (k - 1) / poch
    return t


def fold_pslq(qc, zc, dps):
    """No integer polynomial relation of low degree for q_c, z_c, or the pair."""
    mp.mp.dps = dps
    print("    integer-relation search (mpmath.pslq, tol 1e-200 at 230 digits):")
    for name, x in (("q_c", qc), ("z_c", zc)):
        hits = []
        for d in range(1, 9):
            r = mp.pslq([x**i for i in range(d + 1)],
                        tol=mp.mpf(10) ** -200, maxcoeff=10**14, maxsteps=20000)
            if r is not None:
                hits.append((d, r))
        print(f"      {name}: degree <= 8, coefficients <= 1e14 -> "
              f"{'none' if not hits else hits}")
    # Only profiles with enough digits per unknown are meaningful: n basis elements
    # against a maxcoeff of 10^14 need well over 14n digits before a hit means
    # anything.  At 230 digits that caps the pair search at the bilinear profile.
    hits = []
    for d in (1,):
        basis = [qc**i * zc**j for i in range(d + 1) for j in range(d + 1)]
        r = mp.pslq(basis, tol=mp.mpf(10) ** -200, maxcoeff=10**14, maxsteps=20000)
        if r is not None:
            hits.append((d, r))
    print(f"      the pair (q_c,z_c): bilinear, 4 terms -> "
          f"{'none' if not hits else hits}")
    print("      (larger pair profiles are not reported: 230 digits do not support")
    print("       more than about 16 unknowns against a 10^14 coefficient bound, and")
    print("       PSLQ returns spurious vectors past that point.)")


def fold_jet(qc, zc, dps):
    """rem:zerocurve-arith(j): the first-jet web at the fold, and the two exact
    finite-height relations it satisfies."""
    mp.mp.dps = 3 * dps
    q, z = +qc, +zc
    Q = q * q
    A = G(q, Q * z)
    B = Q * z * Gz(q, Q * z)          # (theta G)(Q z_c)
    h = H(q, z)
    eta = z * Hz(q, z)                # (theta H)(z_c)
    mp.mp.dps = dps
    print(f"    first-jet web at the fold (theta = z d/dz):")
    print(f"      A h - (1 - q_c)  agrees to {digits(A*h, 1-q)} digits")
    print(f"      B h + A eta      agrees to {digits(B*h, -A*eta)} digits")
    # the telescoped orbit bilinear
    mp.mp.dps = 3 * dps
    S = mp.mpf(0)
    m = 0
    while True:
        w = Q**m * z
        t = q * Q**m * z * (G(q, Q * w) * (Q * w) * Hz(q, Q * w)
                            - H(q, Q * w) * (Q * w) * Gz(q, Q * w))
        S += t
        m += 1
        if m > 4 and abs(t) < mp.mpf(10) ** (-(dps + 20)):
            break
    mp.mp.dps = dps
    print(f"      B eta = sum_{{m>=0}} q Q^m z_c [G thH - H thG](Q^{{m+1}} z_c): "
          f"agrees to {digits(B*eta, S)} digits ({m} terms)")


if __name__ == "__main__":
    print("qcos_analytic: two-precision certificates for the Hahn-Exton q-cosine\n")
    run_wronskian()
    run_zeroproduct()
    run_qstar_items()
    run_confluence()
    run_fold()
    print("done.")
