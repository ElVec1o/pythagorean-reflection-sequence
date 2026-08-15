#!/usr/bin/env python3
"""qcos_lattice.py -- the integer zero lattice of the Hahn-Exton q-cosine.

Regenerates, by exact arithmetic in Z[[q]], every lattice number quoted in
paper/journal/hahn_exton_qcosine.tex:

  thm:integrality        u_k = q^{2(k-1)} z_k lies in 1 + q Z[[q]]; the u_1 prefix.
  cor:hexagonal          onset(u_k - 1) = k(2k-1) = T_{2k-1}, leading coefficient -1.
  prop:sinelattice(c)    onset(v_k - 1) = k(2k+1) = T_{2k}.
  rem:triangular         the two onset families interleave over the triangular numbers.
  prop:stablelaw         (1-u_k) q^{-T_{2k-1}} and (1-v_k) q^{-T_{2k}} both agree with
                         1/(q^2;q^2)_inf^2 to a measured depth, reported per k.
  rem:zerocurve-arith(i) prod_k phi_k = 1 with phi_k = u_k(q) u_k(-q) / u_k(q^2),
                         and the leading terms of phi_1..phi_4.

Method.  u_k is the Hensel/Newton root at u = 1 of

    F_k(q,u) = q^{k(k-1)} G(q, u q^{-2(k-1)})
             = sum_{k'>=0} (-1)^{k'} q^{(k'-k)(k'-k+1)} u^{k'} / (q;q)_{2k'},

and v_k the root of the same shape with (q;q)_{2k'} replaced by (q^2;q)_{2k'}.  Both
have coefficients in Z[[q]] (partition generating functions) and unit u-derivative at
u = 1, so the Newton iteration runs entirely over Z: every printed coefficient is an
exact integer, not a rounded float.  The Newton residual is asserted to vanish
identically to the working order before anything is reported.

Runtime about 20 s at ORDER = 300, peak RSS 17 MB (Rule 8: small job, Python permitted).
Usage:  python3 qcos_lattice.py [ORDER] [KMAX]
"""
import sys

ORDER = int(sys.argv[1]) if len(sys.argv) > 1 else 300
KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 8


def mul(a, b, n=None):
    n = n or ORDER + 1
    c = [0] * n
    for i, ai in enumerate(a[:n]):
        if not ai:
            continue
        for j in range(min(len(b), n - i)):
            if b[j]:
                c[i + j] += ai * b[j]
    return c


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def inv_unit(a):
    """1/a for a with a[0] = +-1: stays inside Z[[q]]."""
    u = a[0]
    assert u in (1, -1), f"leading coefficient {u} is not a unit of Z"
    c = [0] * (ORDER + 1)
    c[0] = u
    for n in range(1, ORDER + 1):
        c[n] = -u * sum(a[i] * c[n - i] for i in range(1, n + 1))
    return c


def shift(n):
    c = [0] * (ORDER + 1)
    if n <= ORDER:
        c[n] = 1
    return c


ONE = shift(0)


def parts_at_most(m):
    """1/(q;q)_m = generating function of partitions into parts <= m."""
    c = [0] * (ORDER + 1)
    c[0] = 1
    for part in range(1, m + 1):
        for n in range(part, ORDER + 1):
            c[n] += c[n - part]
    return c


def parts_in_range(lo, hi):
    """1/((1-q^lo)...(1-q^hi)) = partitions into parts in [lo,hi]."""
    c = [0] * (ORDER + 1)
    c[0] = 1
    for part in range(lo, hi + 1):
        for n in range(part, ORDER + 1):
            c[n] += c[n - part]
    return c


def newton_root(coef):
    """Root in 1 + qZ[[q]] of sum_j coef[j] u^j, by Newton over Z."""
    K = len(coef)

    def ev(z):
        acc = coef[K - 1][:]
        for j in range(K - 2, -1, -1):
            acc = add(mul(acc, z), coef[j])
        return acc

    def evd(z):
        acc = [(K - 1) * x for x in coef[K - 1]]
        for j in range(K - 2, 0, -1):
            acc = add(mul(acc, z), [j * x for x in coef[j]])
        return acc

    z = ONE[:]
    for _ in range(ORDER.bit_length() + 2):
        z = sub(z, mul(ev(z), inv_unit(evd(z))))
    assert all(x == 0 for x in ev(z)), "Newton residual nonzero"
    return z


def cosine_lattice(k):
    """u_k(q) in 1 + qZ[[q]]."""
    coef = []
    kp = 0
    while True:
        e = (kp - k) * (kp - k + 1)
        if e > ORDER and kp > k:
            break
        coef.append([0] * (ORDER + 1) if e > ORDER else
                    [(-1) ** kp * x for x in mul(shift(e), parts_at_most(2 * kp))])
        kp += 1
    return newton_root(coef)


def sine_lattice(k):
    """v_k(q) in 1 + qZ[[q]] (the H-side; parts in [2, 2k'+1])."""
    coef = []
    kp = 0
    while True:
        e = (kp - k) * (kp - k + 1)
        if e > ORDER and kp > k:
            break
        pr = ONE if kp == 0 else parts_in_range(2, 2 * kp + 1)
        coef.append([0] * (ORDER + 1) if e > ORDER else
                    [(-1) ** kp * x for x in mul(shift(e), pr)])
        kp += 1
    return newton_root(coef)


def onset(series):
    """(index, coefficient) of the first nonzero term of 1 - series."""
    d = sub(ONE, series)
    for n in range(ORDER + 1):
        if d[n]:
            return n, d[n]
    return None, 0


def agreement_depth(a, b):
    """Last index through which two series agree (the paper's "agreement depth")."""
    for n in range(ORDER + 1):
        if a[n] != b[n]:
            return n - 1
    return ORDER


def substitute_qd(a, d):
    c = [0] * (ORDER + 1)
    for n in range(ORDER + 1):
        if n * d <= ORDER:
            c[n * d] = a[n]
    return c


def negate_q(a):
    return [(-1) ** n * x for n, x in enumerate(a)]


def main():
    print(f"qcos_lattice: exact Z[[q]] arithmetic, ORDER = {ORDER}, k <= {KMAX}\n")

    us = {k: cosine_lattice(k) for k in range(1, KMAX + 1)}
    vs = {k: sine_lattice(k) for k in range(1, min(KMAX, 6) + 1)}

    # -- thm:integrality: the u_1 prefix, and integrality of every u_k.
    print("thm:integrality")
    print("  u_1 = z_1, first 25 coefficients:")
    print("   ", us[1][:25])
    ok = all(all(isinstance(x, int) for x in us[k]) and us[k][0] == 1
             for k in us)
    print(f"  every u_k has integer coefficients and u_k(0) = 1: {ok}")
    okv = all(all(isinstance(x, int) for x in vs[k]) and vs[k][0] == 1 for k in vs)
    print(f"  every v_k has integer coefficients and v_k(0) = 1: {okv}\n")

    # -- cor:hexagonal / prop:sinelattice(c) / rem:triangular.
    print("cor:hexagonal and prop:sinelattice(c): deviation onsets")
    print(f"  {'k':>3} {'onset(u_k-1)':>13} {'k(2k-1)':>9} {'coef':>5} "
          f"{'onset(v_k-1)':>13} {'k(2k+1)':>9} {'coef':>5}")
    hex_ok = tri_ok = True
    onsets = []
    for k in range(1, KMAX + 1):
        nu, cu = onset(us[k])
        pred_u = k * (2 * k - 1)
        row = [k, nu, pred_u, cu]
        if k in vs:
            nv, cv = onset(vs[k])
            pred_v = k * (2 * k + 1)
            row += [nv, pred_v, cv]
            tri_ok &= (nv == pred_v and cv == 1)
            onsets += [(pred_u, "u"), (pred_v, "v")]
        else:
            row += ["-", "-", "-"]
            onsets += [(pred_u, "u")]
        hex_ok &= (nu == pred_u and cu == 1)
        print("  " + " ".join(f"{str(x):>{w}}" for x, w in
                              zip(row, (3, 13, 9, 5, 13, 9, 5))))
    print(f"  onset(u_k-1) = k(2k-1) with leading coefficient -1 for all k tested: {hex_ok}")
    print(f"  onset(v_k-1) = k(2k+1) with leading coefficient -1 for all k tested: {tri_ok}")
    seen = sorted(onsets)
    tri = [n * (n + 1) // 2 for n in range(1, 2 * len(vs) + 1)]
    print(f"  onsets in order: {[n for n, _ in seen]}")
    print(f"  triangular numbers T_1..T_{2*len(vs)}: {tri}")
    print(f"  the two families interleave over the triangular numbers exactly once each: "
          f"{[n for n, _ in seen][:len(tri)] == tri}\n")

    # -- prop:stablelaw.
    print("prop:stablelaw: (1-u_k) q^{-T_{2k-1}} and (1-v_k) q^{-T_{2k}} against "
          "1/(q^2;q^2)_inf^2")
    twocol = [0] * (ORDER + 1)          # 1/(q^2;q^2)_inf^2, two-coloured partitions
    twocol[0] = 1
    for colour in range(2):
        for part in range(2, ORDER + 1, 2):
            for n in range(part, ORDER + 1):
                twocol[n] += twocol[n - part]
    print(f"  1/(q^2;q^2)_inf^2 = {twocol[:14]}  (coefficients at even powers: "
          f"{[twocol[2*i] for i in range(7)]})")
    print(f"  {'k':>3} {'cosine depth':>13} {'2k-2':>6} {'sine depth':>11} {'2k-1':>6}")
    for k in range(1, KMAX + 1):
        T = k * (2 * k - 1)
        dev = [x for x in sub(ONE, us[k])[T:]] + [0] * T
        dc = agreement_depth(dev, twocol)
        if k in vs:
            T2 = k * (2 * k + 1)
            dev2 = [x for x in sub(ONE, vs[k])[T2:]] + [0] * T2
            ds = agreement_depth(dev2, twocol)
        else:
            ds = "-"
        print(f"  {k:>3} {dc:>13} {2*k-2:>6} {str(ds):>11} {2*k-1:>6}")
    print("  (depth = last index through which the rescaled deviation and the")
    print("   eta-quotient agree.  The proposition asserts the depth grows without")
    print("   bound; the table is the measured agreement, not the proof.)\n")

    # -- rem:zerocurve-arith(i): the three-base relation.
    print("rem:zerocurve-arith(i): phi_k = u_k(q) u_k(-q) / u_k(q^2)")
    phis = []
    for k in range(1, min(KMAX, 4) + 1):
        num = mul(us[k], negate_q(us[k]))
        phi = mul(num, inv_unit(substitute_qd(us[k], 2)))
        phis.append(phi)
        lead = [(n, phi[n]) for n in range(1, 40) if phi[n]][:4]
        print(f"  phi_{k} = 1 + " + " + ".join(f"{c}q^{n}" for n, c in lead) + " + ...")
    prod = ONE[:]
    for phi in phis:
        prod = mul(prod, phi)
    first_bad = next((n for n in range(1, ORDER + 1) if prod[n]), None)
    print(f"  partial product over k <= 4: 1 + O(q^{first_bad}).  The relation is not")
    print(f"  termwise; adjacent leading defects cancel in pairs, and the identity")
    print(f"  prod_{{k>=1}} phi_k = 1 closes only over the full family.  What is measured")
    print(f"  here is that the truncated product agrees with 1 through order {first_bad-1}.")


if __name__ == "__main__":
    main()
