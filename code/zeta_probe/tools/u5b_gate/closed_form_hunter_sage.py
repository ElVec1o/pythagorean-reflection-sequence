#!/usr/bin/env sage-python
# Closed-form hunter (Sage) for the U-gate confluence constants a1,a2,a3,C.
#   Y3(1/q)/[(3/sqrt2) tau^{3/2} sin w] = 1 + a1 tau + a2 tau^2 + a3 tau^3 + ...   (at travel poles)
# a1 = 2269/1296 = 7/4 + 1/1296 (proven exact).  PREDICTION: every a_n is rational (parity argument).
#
# Upgrade over the mpmath version: Sage's algdep() tests ALGEBRAIC of ANY degree and returns the
# minimal polynomial (rational = deg 1; quadratic surd = deg 2; ...). Heavy extraction stays in mpmath.
#
# RUN under Sage's python (NO preparser, so mpmath sees plain python ints):
#     cd /Users/vico/Documents/elvec1o/u5b_gate
#     sage -python closed_form_hunter_sage.py 300 22 48
#     sage -python closed_form_hunter_sage.py 500 24 58      # deeper
# Paste back the per-coefficient "min poly" / "rational?" lines + any *** TRUSTWORTHY *** tag.

import sys, time
import mpmath as mp
from sage.all import algdep, RealField, RR

DPS  = int(sys.argv[1]) if len(sys.argv) > 1 else 300
M_LO = int(sys.argv[2]) if len(sys.argv) > 2 else 22
M_HI = int(sys.argv[3]) if len(sys.argv) > 3 else 48
mp.mp.dps = DPS
TOL = mp.mpf(10) ** (-(DPS - 8))

def qpoch(a, q2, n):
    p = mp.mpf(1)
    for j in range(n):
        p *= (1 - a * q2 ** j)
    return p

def sigt_w(w):
    tau = 2 / w ** 2; q = mp.e ** (-tau); s = mp.mpf(0); mx = mp.mpf(0)
    for k in range(0, 4000):
        t = 2 * q * (-2 * (1 - q)) ** k * q ** (k * k + 2 * k) / (qpoch(q * q, q * q, k + 1) * qpoch(q ** 3, q * q, k))
        s += t; at = abs(t); mx = max(mx, at)
        if k > 3 and at < TOL * mx: break
    return s

def find_pole(m):
    w0 = (m + mp.mpf(1) / 2) * mp.pi - mp.sqrt(2) / 36 * mp.sqrt(2 / ((m + mp.mpf(1) / 2) * mp.pi) ** 2)
    return mp.findroot(lambda w: sigt_w(w) - 1, w0, tol=mp.mpf(10) ** (-(DPS - 25)))

def Y3(x, q):
    s = mp.mpf(0); mx = mp.mpf(0)
    for k in range(0, 4000):
        d = (-2) ** k * (1 - q) ** k * q ** (k * k + 3 * k) / (qpoch(q * q, q * q, k) * qpoch(q ** 5, q * q, k))
        t = d * x ** (2 * k + 3); s += t; at = abs(t); mx = max(mx, at)
        if k > 3 and at < TOL * (mx + 1): break
    return s

sq2 = mp.sqrt(2)
pts = []; t0 = time.time()
print("# extracting r_m at poles m=%d..%d (dps=%d) ..." % (M_LO, M_HI, DPS))
for m in range(M_LO, M_HI + 1):
    w = find_pole(m); tau = 2 / w ** 2; q = mp.e ** (-tau)
    lead = (3 / sq2) * tau ** (mp.mpf(3) / 2) * mp.sin(w)
    r = Y3(1 / q, q) / lead - 1
    pts.append((tau, r))
    print("  m=%2d  tau=%s  r/tau=%s  (%.0fs)" % (m, mp.nstr(tau, 6), mp.nstr(r / tau, 14), time.time() - t0))
    sys.stdout.flush()

def fit(J):
    use = pts[-J:]
    V = mp.matrix(J, J); rhs = mp.matrix(J, 1)
    for i, (tau, r) in enumerate(use):
        rhs[i] = r
        for j in range(J): V[i, j] = tau ** (j + 1)
    a = mp.lu_solve(V, rhs); return [a[j] for j in range(J)]

Jbig = min(len(pts), max(8, (M_HI - M_LO) - 2))
aA = fit(Jbig); aB = fit(Jbig - 2)
a1 = aA[0]; a2 = aA[1] if len(aA) > 1 else mp.mpf('nan'); a3 = aA[2] if len(aA) > 2 else mp.mpf('nan')
C = (3 / sq2) * a1

def identify(name, x, va, vb):
    rel = float(-mp.log10(abs(va - vb) + mp.mpf(10) ** (-DPS))) if va is not None else \
          float(-mp.log10(abs(aA[0] - aB[0]) + mp.mpf(10) ** (-DPS)))
    bits = int(rel * 3.33) + 40
    Rf = RealField(bits)
    xs = Rf(mp.nstr(x, int(rel) + 6))
    print(" --- %s = %s   (reliable ~%.0f digits) ---" % (name, mp.nstr(x, min(44, int(rel))), rel))
    for d in [1, 2, 3, 4, 5, 6, 8]:
        try:
            p = algdep(xs, d)
        except Exception as e:
            print("    deg %d: algdep error %s" % (d, e)); continue
        if p == 0 or p.degree() < 1: continue
        H = max(abs(int(c)) for c in p.coefficients())
        res = abs(p(xs))
        spend = float(p.degree()) * (float(RR(H).log(10)) if H > 1 else 0.0)
        margin = rel - spend
        good = (margin > 15) and (res < Rf(10) ** (-int(rel * 0.7)))
        tag = "*** TRUSTWORTHY ***" if good else "(insufficient precision)"
        if d == 1:
            print("    rational?  %s = %s/%s   [height %d, margin %.0f] %s" % (name, -p[0], p[1], H, margin, tag))
        else:
            print("    deg %d min poly: %s   [height %d, margin %.0f] %s" % (d, p, H, margin, tag))
        if good:
            print("        ==> %s is ALGEBRAIC of degree %d." % (name, d)); return
    print("    no trustworthy algebraic relation up to deg 8 at this precision (raise dps/poles).")

for nm, x, va, vb in [("a1", a1, aA[0], aB[0]),
                      ("a2", a2, aA[1] if len(aA) > 1 else None, aB[1] if len(aB) > 1 else None),
                      ("a3", a3, aA[2] if len(aA) > 2 else None, aB[2] if len(aB) > 2 else None),
                      ("C", C, None, None)]:
    if mp.isnan(x): continue
    identify(nm, x, va, vb)

print("\n# sanity: a1 - 2269/1296 =", mp.nstr(a1 - mp.mpf(2269) / 1296, 6), " (should be ~0)")
print("# prediction: a2,a3 come back deg-1 (rational) once reliable >= 2*log10(denominator).")
