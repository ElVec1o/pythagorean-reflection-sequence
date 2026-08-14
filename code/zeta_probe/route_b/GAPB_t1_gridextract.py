"""
WELL-CONDITIONED extraction of the t1(tau)/tau power-series coefficients c_k.

Key point: the pole-based Vandermonde (taus spread 6e-4..9e-2) is exponentially ill-conditioned,
so only c0..c9 came out reliable.  But t1=P12/Se is analytic in tau (the oscillatory factor cancels
in the RATIO), so we can sample t1(tau)/tau at GENERIC tau on a TIGHT interval [a,L] where the
monomial Vandermonde is well-conditioned, and recover MANY reliable c_k at modest precision.

Strategy: Chebyshev nodes on [a,L], solve V c = f, cross-check c0..c4 vs known rationals, certify
reliability by varying (degree, L, dps), rational-ID the stable c_k, estimate radius = 1/limsup|c_k|^{1/k}.
"""
import mpmath as mp

def cocycle(q, N):
    """Stable transfer-matrix cocycle.  Returns (P12, Se)=(Y,y).  Complex-safe."""
    x = mp.mpf(0); y = mp.mpf(1); X = mp.mpf(1); Y = mp.mpf(0); qn = mp.mpf(1)
    if isinstance(q, mp.mpc):
        x = mp.mpc(0); y = mp.mpc(1); X = mp.mpc(1); Y = mp.mpc(0); qn = mp.mpc(1)
    for n in range(1, N + 1):
        qn *= q; q2n = qn * qn; q3n = q2n * qn
        x, y, X, Y = (x * (1 + 2 * q2n) - 2 * y * qn,
                      2 * x * q3n + y * (1 - 2 * q2n),
                      X * (1 + 2 * q2n) - 2 * Y * qn,
                      2 * X * q3n + Y * (1 - 2 * q2n))
    return Y, y   # P12, Se

def f_t1_over_tau(tau):
    """f(tau) = t1/tau = P12 / (tau * Se)."""
    q = mp.e ** (-tau)
    N = int((mp.mp.dps + 18) * 2.302585 / abs(tau)) + 60
    P12, Se = cocycle(q, N)
    return P12 / (tau * Se)

def cheb_nodes(a, L, npts):
    """npts Chebyshev points on [a,L]."""
    c = (a + L) / 2; h = (L - a) / 2
    return [c + h * mp.cos(mp.pi * (2 * j + 1) / (2 * npts)) for j in range(npts)]

def extract(a, L, deg, dps):
    """Fit f on deg+1 Chebyshev nodes in [a,L]; return list of c_k (k=0..deg)."""
    mp.mp.dps = dps
    nodes = cheb_nodes(mp.mpf(a), mp.mpf(L), deg + 1)
    vals = [f_t1_over_tau(t) for t in nodes]
    A = mp.matrix(deg + 1, deg + 1); b = mp.matrix(deg + 1, 1)
    for i in range(deg + 1):
        p = mp.mpf(1)
        for j in range(deg + 1):
            A[i, j] = p; p *= nodes[i]
        b[i] = vals[i]
    c = mp.lu_solve(A, b)
    return [c[k] for k in range(deg + 1)]

known = [mp.mpf(1)/4, mp.mpf(3)/16, mp.mpf(13)/96, mp.mpf(13)/256, -mp.mpf(629)/7680]

print("=" * 78)
print("WELL-CONDITIONED grid extraction of t1/tau = sum c_k tau^k")
print("=" * 78)

# Primary fit
DPS = 240; DEG = 26; A0, L0 = 0.035, 0.26
c_main = extract(A0, L0, DEG, DPS)
print(f"\nPrimary: {DEG+1} Chebyshev nodes on [{A0},{L0}], dps={DPS}")
print(f"Sanity c0..c4 vs known rationals (digits agreeing):")
for k in range(5):
    err = abs(c_main[k] - known[k])
    d = (-mp.log10(err)) if err > 0 else mp.mpf('inf')
    print(f"  c_{k}: fit={mp.nstr(c_main[k],18)}  known={mp.nstr(known[k],18)}  ~{int(d) if d!=mp.inf else 999} digits")

# Stability fit (different interval & degree) to certify which c_k are reliable
c_alt = extract(0.045, 0.30, 30, DPS)
print(f"\nStability: which c_k agree between two independent fits (different L, degree)?")
print(f"{'k':>3} {'c_k (primary)':>30} {'|c_k|^(1/k)':>12} {'agree-digits':>12}")
reliable = []
for k in range(DEG + 1):
    err = abs(c_main[k] - c_alt[k]) if k < len(c_alt) else mp.mpf(1)
    d = int(-mp.log10(err)) if err > 0 and err < 1 else 0
    rk = (abs(c_main[k]) ** (mp.mpf(1)/k)) if k >= 1 else mp.mpf(0)
    star = " <-- reliable" if d >= 20 else ("" if d >= 8 else "  (unreliable)")
    if d >= 20: reliable.append((k, c_main[k]))
    print(f"{k:>3} {mp.nstr(c_main[k],16):>30} {mp.nstr(rk,8):>12} {d:>12}{star}")

# Radius estimate from reliable coefficients
if len(reliable) >= 6:
    tail = reliable[len(reliable)//2:]
    ls = max(float(abs(ck) ** (1.0/k)) for k, ck in tail)
    print(f"\nlimsup |c_k|^(1/k) over reliable tail ~ {ls:.4f}  =>  radius ~ {1/ls:.4f}")
    print(f"   need radius > tau_1 = 0.0905 for Option-2 convergence:  {'YES' if 1/ls > 0.0905 else 'NO'}")

# Rational-ID the reliable coefficients
print(f"\nRational-ID of reliable c_k (mp.identify with small-denominator basis):")
for k, ck in reliable:
    rid = mp.identify(ck)
    # try pslq for p/q
    frac = None
    for D in [2**a * 3**b * 5**c * 7**d for a in range(14) for b in range(7) for c in range(4) for d in range(3) if 2**a*3**b*5**c*7**d < 10**12]:
        num = ck * D
        if abs(num - mp.nint(num)) < mp.mpf(10)**(-30):
            frac = f"{int(mp.nint(num))}/{D}"; break
    print(f"  c_{k} = {mp.nstr(ck, 24)}   {'= '+frac if frac else ('identify: '+rid if rid else '(no simple rational)')}")
