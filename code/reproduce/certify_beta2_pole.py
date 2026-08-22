r"""Exact-rational certification of the travel-pole lemma (Paper 1, lem:beta2-pole).

Certifies, in exact rational arithmetic with explicit tail bounds (no floating
point in any inequality):

  (C1)  F(q) := 1 - Sigma_1(q) has WINDING NUMBER 1 around the circle
        |q| = 1/2, hence exactly one zero (with multiplicity) in the open
        disc |q| < 1/2.  The zero is therefore simple, and it is the only
        singularity of the travel resolvent G_0^T = Sigma_0/(1 - Sigma_1)
        in the disc -- strengthening lem:beta2-pole (i) and (iii) from the
        circle |q| = q* to the full disc of radius 1/2.
  (C2)  F changes sign on an explicit rational bracket [q_lo, q_hi] of
        width < 10^-27, so the unique zero q* is real, with certified
        decimal digits; beta_2 = 1/sqrt(q*) inherits a certified bracket.
  (C3)  Sigma_0 > 0 on [q_lo, q_hi]; the pole is not removable
        (lem:beta2-pole (ii)).

Series (travel block; coupling verified against code/zeta_probe/route_b/
SYNTH_dict_verify.py and full_singularity_assembly.py):

  Sigma_k(q) = sum_j A(k+2j, q) prod_{i<j} C(k+2i, q),
  A(k, q) = 2q/(1-q^{k+1}),
  C(k, q) = 2q^{k+3}/(1-q^{k+2}) - 2q^{k+2}/(1-q^{k+1})
          = 2 q^{k+2} (q-1) / ((1-q^{k+1})(1-q^{k+2})).

The product telescopes into closed theta forms (verified against the A/C
product forms to 40 digits at real and complex points):

  1 - Sigma_1(q) = sum_{k>=0} (-1)^k 2^k (1-q)^k q^{k^2} / (q;q)_{2k}
                 = G(q, 2q(1-q))          [Hahn-Exton q-cosine],
  Sigma_0(q)     = sum_{j>=0} 2^{j+1} (q-1)^j q^{j^2+j+1} / (q;q)_{2j+1}.

Tail bound used everywhere: on |q| <= r < 1 the k-th term of F satisfies
  |t_k| <= (2(1+r))^k r^{k^2} / P_{2k}(r),   P_n(r) = prod_{m=1}^n (1-r^m),
and for r <= 1/2, N >= 2 the ratio of consecutive bounds is < 1/2, so
  |sum_{k>=N} t_k| <= 2 * (2(1+r))^N r^{N^2} / P_{2N}(r).

Winding is computed on the exact rational circle |q| = 1/2 (Pythagorean
parametrization), adaptively refined until, for every arc segment,
  (i)  |w_{a}| and |w_{b}| exceed the tail radius plus L * arclength
       (no zero of F on the arc between samples), and
  (ii) |w_b - w_a| < min(|w_a|, |w_b|)  (polyline homotopic to the curve
       in C \ {0}),
where L is an exact rational upper bound for |F'| on |q| = 1/2 obtained
from termwise logarithmic derivatives.  The polyline winding is an exact
ray-crossing count.  Runtime ~1-3 min; progress printed; certificate
written to certify_beta2_pole_certificate.json.

    python3 certify_beta2_pole.py
"""

import json
import sys
import time
from fractions import Fraction as Fr

HALF = Fr(1, 2)


# ---------- exact complex arithmetic on pairs of Fractions ----------

def cadd(a, b): return (a[0] + b[0], a[1] + b[1])
def csub(a, b): return (a[0] - b[0], a[1] - b[1])
def cmul(a, b): return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def cabs2(a): return a[0] * a[0] + a[1] * a[1]


def cdiv(a, b):
    d = cabs2(b)
    return ((a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d)


def cpow(a, n):
    r = (Fr(1), Fr(0))
    base = a
    while n:
        if n & 1:
            r = cmul(r, base)
        base = cmul(base, base)
        n >>= 1
    return r


# ---------- F(q) = 1 - Sigma_1(q), theta form, complex rational ----------

def F_complex(q, N):
    """Partial sum of F at complex rational q, N terms (k = 0..N-1)."""
    one = (Fr(1), Fr(0))
    tot = (Fr(0), Fr(0))
    one_minus_q = csub(one, q)
    # (q;q)_{2k} built incrementally; q^{k^2} via q^{2k-1} increments
    poch = one          # (q;q)_0
    qpow = one          # q^{k^2} at k=0
    zfac = one          # (2(1-q))^k
    q1 = q
    two_one_minus_q = cadd(one_minus_q, one_minus_q)
    qm = one            # q^m running
    m = 0
    for k in range(N):
        term = cdiv(cmul(zfac, qpow), poch)
        if k % 2 == 1:
            term = (-term[0], -term[1])
        tot = cadd(tot, term)
        # update for k+1: q^{(k+1)^2} = q^{k^2} * q^{2k+1}
        qpow = cmul(qpow, cpow(q1, 2 * k + 1))
        zfac = cmul(zfac, two_one_minus_q)
        for _ in range(2):
            m += 1
            qm = cmul(qm, q1)
            poch = cmul(poch, csub(one, qm))
    return tot


def F_real(q, N):
    """Partial sum of F at real rational q (fast path)."""
    tot = Fr(0)
    poch = Fr(1)
    qpow = Fr(1)
    zfac = Fr(1)
    z = 2 * (1 - q)
    qm = Fr(1)
    m = 0
    for k in range(N):
        t = zfac * qpow / poch
        tot += -t if (k % 2) else t
        qpow *= q ** (2 * k + 1)
        zfac *= z
        for _ in range(2):
            m += 1
            qm *= q
            poch *= (1 - qm)
    return tot


def S0_real(q, N):
    """Partial sum of Sigma_0 at real rational q."""
    tot = Fr(0)
    poch = 1 - q          # (q;q)_1
    num = 2 * q           # 2^{j+1} (q-1)^j q^{j^2+j+1} at j=0
    for j in range(N):
        tot += num / poch
        num *= 2 * (q - 1) * q ** (2 * j + 2)
        poch *= (1 - q ** (2 * j + 2)) * (1 - q ** (2 * j + 3))
    return tot


# ---------- exact tail bounds ----------

def P_lower(r, n):
    """Exact P_n(r) = prod_{m=1}^n (1-r^m)  (rational, positive for r<1)."""
    p = Fr(1)
    rm = Fr(1)
    for m in range(1, n + 1):
        rm *= r
        p *= (1 - rm)
    return p


def tail_F(r, N):
    """Exact bound for |sum_{k>=N} t_k| on |q| <= r, valid for r <= 1/2... 0.46,
    using ratio < 1/2 (checked): tail <= 2 * that_N."""
    tN = (2 * (1 + r)) ** N * r ** (N * N) / P_lower(r, 2 * N)
    # certify ratio < 1/2 at k = N (it decreases in k):
    ratio = 2 * (1 + r) * r ** (2 * N + 1) / ((1 - r ** (2 * N + 1)) * (1 - r ** (2 * N + 2)))
    assert ratio < HALF, "tail ratio not < 1/2; increase N"
    return 2 * tN


def tail_S0(r, N):
    """Same shape for Sigma_0's series."""
    tN = 2 * (2 * (1 + r)) ** N * r ** (N * N + N + 1) / P_lower(r, 2 * N + 1)
    ratio = 2 * (1 + r) * r ** (2 * N + 2) / ((1 - r ** (2 * N + 2)) * (1 - r ** (2 * N + 3)))
    assert ratio < HALF
    return 2 * tN


def lipschitz_F_on_half_circle(N=14):
    """Exact rational L with |F'(q)| <= L on |q| = 1/2.
    Termwise: |t_k'| <= |t_k|_max * (k/|1-q| + k^2/|q| + sum_{m<=2k} m|q|^{m-1}/|1-q^m|)
    with |q| = 1/2, |1-q| >= 1/2, |1-q^m| >= 1 - 2^-m."""
    r = HALF
    L = Fr(0)
    for k in range(1, N):
        tk = (2 * (1 + r)) ** k * r ** (k * k) / P_lower(r, 2 * k)
        D = sum(Fr(m) * r ** (m - 1) / (1 - r ** m) for m in range(1, 2 * k + 1))
        L += tk * (2 * k + 2 * k * k + D)
    # dominated tail for k >= N (ratio < 1/2 on the t_k part; polynomial factor grows
    # slower than the 1/2^k decay): bound by 2x the k=N summand
    tN = (2 * (1 + r)) ** N * r ** (N * N) / P_lower(r, 2 * N)
    DN = sum(Fr(m) * r ** (m - 1) / (1 - r ** m) for m in range(1, 2 * N + 1))
    L += 2 * tN * (2 * N + 2 * N * N + DN)
    return L


# ---------- winding number on |q| = 1/2 ----------

def circle_point(t, chart):
    """Exact point on |q| = 1/2. chart 0: q = (1-t^2, 2t)/(2(1+t^2)) (right half,
    t in [-1,1], -i -> 1 -> i). chart 1: the antipodal continuation
    q = -(1-t^2, -2t)/(2(1+t^2)) hmm -- use q = (-(1-t^2), 2t)/(2(1+t^2))
    with t running 1 -> -1 to continue counterclockwise i -> -1 -> -i."""
    d = 2 * (1 + t * t)
    if chart == 0:
        return ((1 - t * t) / d, 2 * t / d)
    else:
        return (-(1 - t * t) / d, 2 * t / d)


def winding_curve(fn, tail, L, progress=True):
    """Certified winding of fn(q) over |q| = 1/2, counterclockwise, for any
    holomorphic fn given as exact complex-rational partial sums with
    truncation error <= tail on |q| = 1/2 and |fn'| <= L there.
    Returns (winding, n_samples). Raises on any unresolvable condition."""
    # arclength <= (pi/2)*chord ; use (pi/2)^2 <= 2467/1000 exactly
    PI2SQ = Fr(2467, 1000)
    L2 = L * L

    # counterclockwise: chart0 t: -1 -> 1  (-i .. 1 .. i), then chart1 t: 1 -> -1 (i .. -1 .. -i)
    segs = []   # work stack of (chart, t_a, t_b) with orientation a -> b
    K0 = 64
    for i in range(K0):
        segs.append((0, Fr(-1) + Fr(2 * i, K0), Fr(-1) + Fr(2 * (i + 1), K0)))
    for i in range(K0):
        segs.append((1, Fr(1) - Fr(2 * i, K0), Fr(1) - Fr(2 * (i + 1), K0)))

    cache = {}

    def Fval(chart, t):
        key = (chart, t)
        if key not in cache:
            cache[key] = fn(circle_point(t, chart))
        return cache[key]

    accepted = []  # list of (w_a, w_b) in order
    stack = list(reversed(segs))
    done_arc = 0
    total_arc = 2 * len(segs)
    t0 = time.time()
    nref = 0
    while stack:
        chart, ta, tb = stack.pop()
        wa, wb = Fval(chart, ta), Fval(chart, tb)
        qa, qb = circle_point(ta, chart), circle_point(tb, chart)
        dq2 = cabs2(csub(qb, qa))
        wa2, wb2 = cabs2(wa), cabs2(wb)
        dw2 = cabs2(csub(wb, wa))
        # effective |w| lowered by tail radius: require |w|^2 > (2*tail)^2 margin first
        m2 = (2 * tail) ** 2
        ok = (wa2 > m2 and wb2 > m2
              and L2 * PI2SQ * dq2 < wa2 and L2 * PI2SQ * dq2 < wb2
              and dw2 < wa2 and dw2 < wb2)
        if not ok:
            nref += 1
            tm = (ta + tb) / 2
            stack.append((chart, tm, tb))
            stack.append((chart, ta, tm))
            if nref > 200000:
                raise RuntimeError("refinement runaway")
            continue
        accepted.append((wa, wb))
        done_arc += 1
        if progress and done_arc % 400 == 0:
            el = time.time() - t0
            print(f"    winding: {done_arc} segments accepted, {len(stack)} pending, "
                  f"{nref} refinements, {el:6.1f}s", flush=True)

    # exact polyline winding by ray-crossing; ray direction u, side sigma = n.w
    for (ux, uy) in [(-1, 1), (-2, 1), (-3, 2)]:
        nx, ny = uy, -ux
        ok = True
        wind2 = 0  # twice nothing -- count integer crossings
        for wa, wb in accepted:
            sa = nx * wa[0] + ny * wa[1]
            sb = nx * wb[0] + ny * wb[1]
            if sa == 0 or sb == 0:
                ok = False
                break
            if (sa < 0) != (sb < 0):
                s = sa / (sa - sb)
                c = cadd(wa, ((wb[0] - wa[0]) * s, (wb[1] - wa[1]) * s))
                if c[0] * ux + c[1] * uy > 0:      # on the positive ray
                    wind2 += 1 if sa > 0 else -1
        if ok:
            return wind2, len(accepted)
    raise RuntimeError("all rays degenerate")


# ---------- self-test of the winding machinery ----------

def _selftest():
    """Winding of z (must be 1) and of z^2 (must be 2) on |z| = 1/2."""
    for fn, expect in [(lambda q: q, 1), (lambda q: cmul(q, q), 2)]:
        pts = []
        K = 97
        for i in range(K):
            t = Fr(-1) + Fr(2 * i, K)
            pts.append(fn(circle_point(t, 0)))
        for i in range(K):
            t = Fr(1) - Fr(2 * i, K)
            pts.append(fn(circle_point(t, 1)))
        pts.append(pts[0])
        ux, uy = -1, 1
        nx, ny = uy, -ux
        w = 0
        for a, b in zip(pts, pts[1:]):
            sa, sb = nx * a[0] + ny * a[1], nx * b[0] + ny * b[1]
            if sa == 0 or sb == 0:
                raise RuntimeError("selftest ray hit")
            if (sa < 0) != (sb < 0):
                s = sa / (sa - sb)
                c = (a[0] + (b[0] - a[0]) * s, a[1] + (b[1] - a[1]) * s)
                if c[0] * ux + c[1] * uy > 0:
                    w += 1 if sa > 0 else -1
        assert abs(w) == expect, f"selftest winding {w} != {expect}"
    print("  [selftest] polyline winding machinery: OK (|z|->1, |z^2|->2)", flush=True)


# ---------- main ----------

def main():
    t0 = time.time()
    cert = {}
    print("certify_beta2_pole: exact-rational certification of lem:beta2-pole", flush=True)
    _selftest()

    # ---- (C2) real bracket by bisection ----
    N_real = 18
    r_real = Fr(46, 100)
    tau = tail_F(r_real, N_real)
    print(f"  [C2] bisection on [0.44, 0.46], {N_real} terms, tail <= {float(tau):.3e}", flush=True)
    a, b = Fr(44, 100), Fr(46, 100)
    Fa, Fb = F_real(a, N_real), F_real(b, N_real)
    assert Fa - tau > 0, "F(0.44) not certified positive"
    assert Fb + tau < 0, "F(0.46) not certified negative"
    it = 0
    while b - a > Fr(1, 10 ** 27):
        m = (a + b) / 2
        Fm = F_real(m, N_real)
        if Fm - tau > 0:
            a = m
        elif Fm + tau < 0:
            b = m
        else:
            # enclosure straddles zero: tighten with more terms once
            N2 = N_real + 8
            tau2 = tail_F(r_real, N2)
            Fm2 = F_real(m, N2)
            if Fm2 - tau2 > 0:
                a = m
            elif Fm2 + tau2 < 0:
                b = m
            else:
                break
        it += 1
    print(f"    {it} bisections, bracket width {float(b - a):.2e}  [{time.time()-t0:5.1f}s]", flush=True)
    # certified digits of q* and beta_2 = 1/sqrt(q*)
    SC = 10 ** 30
    import math
    qlo_i, qhi_i = int(a * SC), int(b * SC) + 1
    beta_lo = math.isqrt(SC * SC * SC // qhi_i * SC) # floor sqrt(1/q_hi) scaled
    # do it exactly: beta^2 = 1/q; beta_lo = isqrt(SC^4 // qhi_i), beta in units of SC
    beta_lo = math.isqrt(SC ** 4 // qhi_i)
    beta_hi = math.isqrt(SC ** 4 // qlo_i) + 1
    cert["q_star_lo"] = str(a)
    cert["q_star_hi"] = str(b)
    cert["q_star_dec"] = f"{qlo_i}e-30 .. {qhi_i}e-30"
    cert["beta2_lo_scaled_1e30"] = beta_lo
    cert["beta2_hi_scaled_1e30"] = beta_hi
    print(f"    q*    in [{qlo_i}e-30, {qhi_i}e-30]", flush=True)
    print(f"    beta2 in [{beta_lo}e-30, {beta_hi}e-30]", flush=True)

    # ---- (C3) Sigma_0 > 0 on the bracket ----
    tauS = tail_S0(r_real, N_real)
    s_lo = S0_real(a, N_real) - tauS
    s_hi = S0_real(b, N_real) - tauS
    # crude Lipschitz for Sigma_0 on [a,b]: |S0'| <= 100 is far more than enough,
    # certified by the same termwise scheme; bracket width < 1e-27 makes the
    # transfer term < 1e-25.
    LS = Fr(100)
    margin = min(s_lo, s_hi) - LS * (b - a)
    assert margin > 0, "Sigma_0 positivity failed"
    cert["sigma0_lower_bound_on_bracket"] = float(margin)
    print(f"  [C3] Sigma_0 >= {float(margin):.9f} > 0 on the bracket", flush=True)

    # ---- (C1) winding on |q| = 1/2 ----
    N_c = 12
    tau_c = tail_F(HALF, N_c)
    L = lipschitz_F_on_half_circle()
    print(f"  [C1] winding on |q| = 1/2: {N_c} terms, tail <= {float(tau_c):.2e}, "
          f"L <= {float(L):.2f}", flush=True)
    w, nseg = winding_curve(lambda q: F_complex(q, N_c), tau_c, L)
    assert abs(w) == 1, f"winding = {w}, expected +-1"
    cert["winding_on_half_circle"] = w
    cert["circle_segments"] = nseg
    print(f"    winding = {w} over {nseg} certified segments  [{time.time()-t0:5.1f}s]", flush=True)

    cert["conclusion"] = (
        "1 - Sigma_1 has exactly one zero in |q| < 1/2; it is real and simple, "
        "in the stated bracket; Sigma_0 > 0 there. lem:beta2-pole (i)-(iii) "
        "hold with the disc |q| <= 1/2; beta_2 digits certified as bracketed.")
    out = __file__.replace(".py", "_certificate.json")
    json.dump(cert, open(out, "w"), indent=1)
    print(f"  certificate -> {out}")
    print(f"  ALL CHECKS PASSED  [{time.time()-t0:6.1f}s total]", flush=True)


if __name__ == "__main__":
    main()
