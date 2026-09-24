# P1e_all.py (P1d_all.py driving P1e_cert, extra grid over VQ) -- parameter search driver for P1d_cert.certify: for one seed p/q (side d>0), find (by bisection in log r)
# the largest r for which the rigorous certificate gives B < BTARGET, over a small grid of (eta_frac, kappa).
# Every reported line "BEST" is a complete certificate (re-run P1d_cert.py with the printed arguments to reproduce it).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1d_all.py p q [BTARGET] [RMAX] [NSTAR_MIN]
# A trial counts as a success only if B < BTARGET and N* >= NSTAR_MIN (default 1e10).
import sys, time
from math import log, exp, floor, pi, sin
from flint import arb, acb
from P1e_cert import certify, Fail, setup_x, find_t0, e, PI, I, aup
p, q = int(sys.argv[1]), int(sys.argv[2])
BT = float(sys.argv[3]) if len(sys.argv) > 3 else 0.9
RMAX = float(sys.argv[4]) if len(sys.argv) > 4 and float(sys.argv[4]) > 0 else 0.3/q**2
NSM = float(sys.argv[5]) if len(sys.argv) > 5 else 1e10
T0 = time.time()
# wall: |W| = 1 at Im t = h_w = -log|U|/(2 pi q); t0 approx
_, _, U, _ = setup_x(p, q, 0.0, 1e-9, q)
Ua = float(aup(U).mid()); hw = -log(Ua)/(2*pi*q)
t0 = find_t0(q, U, rad0=1e-10); im0 = float(t0.imag.mid())
def params(r, ef, ka):
    n2 = max(q, min(int(1.0/(q*r)) - 1, int(1.0/(2*r)), 250))
    eta = ef*hw
    V0 = 0.85*(eta - im0)/0.72
    return n2, eta, V0, ka
def trial(r, ef, ka, NP=6):
    n2, eta, V0, ka = params(r, ef, ka)
    if n2 < q or V0 <= 0: return None
    try:
        B, Ns, Bs, rows = certify(p, q, r, n2, '%.6g' % eta, '%.6g' % V0, ka, NP, verbose=False, KSEG=32, VQ=VQG, NPC=48)
        return float(B.upper().mid()), float(Ns.lower().mid()) if Ns.is_finite() else float('inf'), (r, n2, '%.6g' % eta, '%.6g' % V0, ka, NP)
    except Fail as ex:
        return None
best = None
VQG = sys.argv[6] if len(sys.argv) > 6 else '0.3'
for ef in (0.3, 0.45, 0.6):
    for ka in (3.0, 4.0):
        lo, hi = None, RMAX
        res = trial(hi, ef, ka)
        if res and res[0] < BT and res[1] >= NSM: lo, cand = hi, res
        else:
            r = hi
            for _ in range(40):   # step down geometrically until success
                r /= 2
                res = trial(r, ef, ka)
                if res and res[0] < BT and res[1] >= NSM: lo, cand = r, res; break
                if r < 1e-9: break
            if lo is None: continue
            hi = 2*lo
            for _ in range(5):
                mid = (lo*hi)**0.5
                res = trial(mid, ef, ka)
                if res and res[0] < BT and res[1] >= NSM: lo, cand = mid, res
                else: hi = mid
        if best is None or cand[2][0] > best[2][0]: best = cand
        print('  eta_frac=%.2f kappa=%.1f: r=%.4g B=%.3f N*=%.3g  [%.0fs]' % (ef, ka, cand[2][0], cand[0], cand[1], time.time() - T0), flush=True)
        if time.time() - T0 > 240: break
    if time.time() - T0 > 240: break
if best:
    r, n2, eta, V0, ka, NP = best[2]
    print('BEST %d/%d d>0: r=%.5g B<=%.4f N*>=%.3g   args: %d %d %.6g %d %s %s %s %d' % (p, q, r, best[0], best[1], p, q, r, n2, eta, V0, ka, NP))
else:
    print('NONE %d/%d: no certificate found' % (p, q))
