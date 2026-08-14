"""
travel_poles_mp.py -- high-precision travel poles q_m (roots of Sigma_1(q)=1), written to poles.txt.

The pole equation is the ALTERNATING Lambert sum Sigma_1 = sum_j A(k+2j) prod C(k+2i) (this is the
lem:cos engine: cancellation ~ e^w near q->1), so f64 dies past m~5. We use mpmath at high dps.
The m-th pole sits near w=(m+1.5)*pi (since Sigma_1 ~ 1-cos w); we bisect the unique Sigma_1-1 sign
change in the window w in [(m+1)pi,(m+2)pi], q=exp(-2/w^2). Output: one full-precision q_m per line.

These poles feed the (validated, O(Smax), OOM-free) f64 Riccati bulk solve in bulk_riccati.rs --
`./bulk_riccati --poles poles.txt` -- to extend B_U(q_m)/B_V(q_m) far past the f64/double-double walls.

Run:  python3 travel_poles_mp.py [M]      (default M=40)
"""
import sys
import mpmath as mp

M = int(sys.argv[1]) if len(sys.argv) > 1 else 40
# dps grows with m: cancellation ~ e^w, w~(M+1.5)pi, need ~ w/ln10 digits + margin.
mp.mp.dps = max(60, int(2.2 * (M + 2) * 3.1416 / 2.302) + 40)
KSTART = 1
print(f"# mpmath dps={mp.mp.dps}, finding {M} travel poles", file=sys.stderr)


def Aq(k, q):
    return 2 * q / (1 - q ** (k + 1))


def Cq(k, q):
    return 2 * q ** (k + 3) / (1 - q ** (k + 2)) - 2 * q ** (k + 2) / (1 - q ** (k + 1))


def sig_t(q, J=400000):
    tot = mp.mpf(0)
    prod = mp.mpf(1)
    tiny = mp.mpf(10) ** (-(mp.mp.dps + 10))
    for j in range(J):
        kk = KSTART + 2 * j
        tot += Aq(kk, q) * prod
        prod *= Cq(kk, q)
        if abs(prod) < tiny and j > 40:
            break
    return tot


def g(w):
    q = mp.e ** (-2 / (w * w))
    return sig_t(q) - 1


pi = mp.pi
poles = []
for idx in range(M):
    wlo = (idx + 1) * pi
    whi = (idx + 2) * pi
    # coarse scan for the unique sign change, then bisect
    steps = 60
    a = wlo
    fa = g(a)
    seg = None
    for s in range(1, steps + 1):
        b = wlo + (whi - wlo) * mp.mpf(s) / steps
        fb = g(b)
        if fa * fb < 0:
            seg = (a, b)
            break
        a, fa = b, fb
    if seg is None:
        print(f"# WARNING: no pole in window m={idx}", file=sys.stderr)
        continue
    lo, hi = seg
    for _ in range(140):
        mid = (lo + hi) / 2
        if g(lo) * g(mid) <= 0:
            hi = mid
        else:
            lo = mid
    w = (lo + hi) / 2
    q = mp.e ** (-2 / (w * w))
    resid = abs(sig_t(q) - 1)
    poles.append(q)
    print(f"# m={idx:2d}  w={mp.nstr(w,10):>12}  q={mp.nstr(q,40)}  resid={mp.nstr(resid,3)}",
          file=sys.stderr)

with open("poles.txt", "w") as f:
    for q in poles:
        f.write(mp.nstr(q, 40) + "\n")
print(f"# wrote {len(poles)} poles to poles.txt", file=sys.stderr)
