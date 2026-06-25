#!/usr/bin/env python3
# Closed-form hunter for the U-gate confluence constants a1, a2, a3, C.
#
# Y3(1/q) / [ (3/sqrt2) tau^{3/2} sin w ]  =  1 + a1 tau + a2 tau^2 + a3 tau^3 + ...   (at travel poles)
# C = boundC limit = (3/sqrt2)*a1.  If a1 is algebraic (p + q*sqrt2, from the sqrt2/36 pole phase) or a
# modular/dilog value, the whole asymptotic is exact -> U closes.  This extracts a1,a2,a3,C to high
# precision and runs PSLQ (integer-relation) against a rich constant basis.
#
# RUN (Mac):
#     cd /Users/vico/Documents/elvec1o/u5b_gate
#     python3 closed_form_hunter.py                 # default dps=200, poles m=14..40
#     python3 closed_form_hunter.py 300 16 48       # dps=300, poles m=16..48 (slower, more precise)
# Paste me the printed block (it also saves to hunter_out.txt).  Progress is printed per pole.

import sys, time
import mpmath as mp

DPS   = int(sys.argv[1]) if len(sys.argv) > 1 else 200
M_LO  = int(sys.argv[2]) if len(sys.argv) > 2 else 14
M_HI  = int(sys.argv[3]) if len(sys.argv) > 3 else 40
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
    w0 = (m + mp.mpf(1) / 2) * mp.pi - mp.sqrt(2) / 36 * mp.sqrt(2 / ((m + 0.5) * mp.pi) ** 2)
    return mp.findroot(lambda w: sigt_w(w) - 1, w0, tol=mp.mpf(10) ** (-(DPS - 25)))

def Y3(x, q):
    s = mp.mpf(0); mx = mp.mpf(0)
    for k in range(0, 4000):
        d = (-2) ** k * (1 - q) ** k * q ** (k * k + 3 * k) / (qpoch(q * q, q * q, k) * qpoch(q ** 5, q * q, k))
        t = d * x ** (2 * k + 3); s += t; at = abs(t); mx = max(mx, at)
        if k > 3 and at < TOL * (mx + 1): break
    return s

# ---- collect (tau, r) at the poles,  r = Y3(1/q)/[(3/sqrt2) tau^{3/2} sin w] - 1 ----
sq2 = mp.sqrt(2)
pts = []
t0 = time.time()
print("# extracting r_m at poles m=%d..%d (dps=%d) ..." % (M_LO, M_HI, DPS))
for m in range(M_LO, M_HI + 1):
    w = find_pole(m); tau = 2 / w ** 2; q = mp.e ** (-tau)
    lead = (3 / sq2) * tau ** (mp.mpf(3) / 2) * mp.sin(w)
    r = Y3(1 / q, q) / lead - 1
    pts.append((tau, r))
    print("  m=%2d  tau=%s  r/tau=%s  (%.0fs)" % (m, mp.nstr(tau, 6), mp.nstr(r / tau, 14), time.time() - t0))
    sys.stdout.flush()

# ---- fit r = a1 tau + a2 tau^2 + ... + aJ tau^J  via Vandermonde (exact J pts), cross-check two J ----
def fit(J):
    use = pts[-J:]
    V = mp.matrix(J, J); rhs = mp.matrix(J, 1)
    for i, (tau, r) in enumerate(use):
        rhs[i] = r
        for j in range(J):
            V[i, j] = tau ** (j + 1)
    a = mp.lu_solve(V, rhs)
    return [a[j] for j in range(J)]

Jbig = min(len(pts), max(8, (M_HI - M_LO) - 2))
aA = fit(Jbig); aB = fit(Jbig - 2)
a1, a2, a3 = aA[0], aA[1] if len(aA) > 1 else mp.mpf('nan'), aA[2] if len(aA) > 2 else mp.mpf('nan')
agree = -mp.log10(abs(aA[0] - aB[0]) + mp.mpf(10) ** (-DPS))
C = (3 / sq2) * a1
print("\n# a1 stable to ~%s digits (J=%d vs %d)" % (mp.nstr(agree, 4), Jbig, Jbig - 2))
for nm, v in [("a1", a1), ("a2", a2), ("a3", a3), ("C=(3/sqrt2)a1", C)]:
    print("#   %-14s = %s" % (nm, mp.nstr(v, min(60, int(agree)) if agree > 10 else 30)))

# ---- PSLQ against bases ----
def pslq_report(name, x, basis_names, basis_vals, reliable_digits, maxc=10 ** 9):
    vec = [x] + basis_vals
    rel = mp.pslq(vec, maxcoeff=maxc, maxsteps=10 ** 6)
    if rel and rel[0] != 0:
        terms = []
        for c, nm in zip(rel[1:], basis_names):
            if c != 0: terms.append("%+d*%s" % (c, nm))
        # TRUSTWORTHINESS: a relation "spends" sum(log10|ci|) digits; need margin beyond that.
        bits = sum(mp.log10(abs(c)) for c in rel if c != 0)
        margin = reliable_digits - float(bits)
        tag = "*** TRUSTWORTHY ***" if margin > 12 else ("plausible" if margin > 4 else "SPURIOUS (too few digits)")
        print("  %s = -(%s)/%d   [margin %.1f digits -> %s]" % (name, " ".join(terms), rel[0], margin, tag))
        return margin > 12
    print("  %s : no relation (maxcoeff=%g, reliable~%.0f digits)" % (name, maxc, reliable_digits))
    return False

G = mp.catalan
basis_small = (["1", "sqrt2"], [mp.mpf(1), sq2])
basis_med = (["1", "sqrt2", "sqrt3", "pi", "1/pi"],
             [mp.mpf(1), sq2, mp.sqrt(3), mp.pi, 1 / mp.pi])
basis_big = (["1", "sqrt2", "sqrt3", "pi", "pi^2", "zeta3", "Catalan", "log2", "sqrt2*pi", "1/pi"],
             [mp.mpf(1), sq2, mp.sqrt(3), mp.pi, mp.pi ** 2, mp.zeta(3), G, mp.log(2), sq2 * mp.pi, 1 / mp.pi])

work_dps = mp.mp.dps
basis_rat = (["1"], [mp.mpf(1)])  # pure rational, huge maxcoeff -- tested FIRST (a_n predicted rational)
print("\n# ===== PSLQ closed-form search (PSLQ at each coeff's OWN reliable precision) =====")
print("#  a1 = 2269/1296 = 7/4 + 1/1296.  PREDICTION: every a_n is rational (large denominators).")
print("#  -> rational hit with margin>12 = CONFIRMED.  Raise dps/poles until a_n stable to 2*log10(denom)+ digits.")
coeffs = [("a1", a1, aA[0], aB[0]), ("a2", a2, aA[1] if len(aA)>1 else mp.mpf('nan'), aB[1] if len(aB)>1 else mp.mpf('nan')),
          ("a3", a3, aA[2] if len(aA)>2 else mp.mpf('nan'), aB[2] if len(aB)>2 else mp.mpf('nan')), ("C", C, None, None)]
for nm, x, va, vb in coeffs:
    if mp.isnan(x): continue
    rel_k = float(-mp.log10(abs(va - vb) + mp.mpf(10) ** (-work_dps))) if va is not None else float(agree)
    mp.mp.dps = max(30, int(rel_k * 0.85)); xr = +x
    print(" --- %s = %s   (reliable ~%.0f digits) ---" % (nm, mp.nstr(xr, min(40, int(rel_k))), rel_k))
    found = pslq_report(nm + ":rational", xr, *basis_rat, rel_k, maxc=10 ** 150)
    if not found: found = pslq_report(nm + ":{1,sqrt2}", xr, *basis_small, rel_k, maxc=10 ** 60)
    if not found: found = pslq_report(nm + ":{med}", xr, *basis_med, rel_k, maxc=10 ** 12)
    mp.mp.dps = work_dps

# ---- save ----
with open("hunter_out.txt", "w") as f:
    f.write("dps=%d poles m=%d..%d  a1-stable-digits~%s\n" % (DPS, M_LO, M_HI, mp.nstr(agree, 4)))
    for nm, v in [("a1", a1), ("a2", a2), ("a3", a3), ("C", C)]:
        f.write("%s = %s\n" % (nm, mp.nstr(v, min(80, int(agree)) if agree > 10 else 30)))
print("\n# saved hunter_out.txt — paste the a1 line + any PSLQ relation back to me.")
