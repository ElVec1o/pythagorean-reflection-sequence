# room28_landscape_cert.py -- attempt to close the Room 27 gap (0, 4.2) on the constant-height legs
# Im x = +-pi/6, near the saddles x_{-1}, x_{-3} (Re x = 0.349119...).
#
# Two things are done, both reusing room27_landscape_cert.py / P1i_landscape_cert.py machinery UNMODIFIED:
#
# (A) DIAGNOSTIC: is Room 27's X0~4.2 boundary a certificate-tightness artifact (rad(X)|Omega'| slack,
#     shared-Vref slack) or a genuine fact about the exact (uncertified, floating) landscape?  We evaluate
#     Re((Omega_mu(x) - Vref) e^{-i theta*}) at floating-point midpoints (no box, no rad(X) term) directly,
#     for every explicit mode, at the saddle real part and throughout (0, 4.2).  This settles the question:
#     if the EXACT value is already positive there, no amount of box-tightening, per-mode Vref bookkeeping,
#     or finer bisection can ever certify that region -- the obstruction is analytic, not numerical.
#
# (B) A genuine (if modest) tightening: room27 used ONE conservative X0=4.3 for BOTH legs.  The two legs
#     are NOT symmetric (the cross term -2 pi mu H/N flips sign with H, and Room 27's own explicit-mode
#     table already showed this).  We bisect the true certifiable X0 SEPARATELY per leg (still exact Arb,
#     same eta=1e-3, same WIN=0.05), and report the tightest boundary the EXISTING machinery can reach on
#     each leg without any new derivation.
#
# Usage: perl -e 'alarm 290; exec @ARGV' python3 room28_landscape_cert.py [LAMBDA] [WIN]
import sys, os, time, resource
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'P1i'))
from P1i_landscape_cert import Case, CertFail, PI, I, CAP_MB
from room27_landscape_cert import landscape_leg, HEIGHT
from flint import arb, acb

A, N = 1, 6

def guard():
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20
    if rss > CAP_MB: print('MEMORY GUARD %.0f MB, abort' % rss, flush=True); sys.exit(2)

def exact_worst(C, Vref, E, H, x0):
    """Floating (uncertified, midpoint-only, NO box/rad(X) term) worst-case Re((Om_mu-Vref)e^{-iTH})
    over all explicit modes at a single point Re x = x0, Im x = H. This is NOT a certificate; it is a
    diagnostic to tell genuine obstruction from certificate slack."""
    x = acb(x0, H)
    m = None
    for mu in range(-22, 23, 2):
        v = float(((C.Om(x, mu) - Vref)*E).real.mid())
        if m is None or v > m[0]: m = (v, mu)
    return m

def find_true_crossing(C, Vref, E, H, lo=0.01, hi=10.0, iters=40):
    """Bisect the EXACT (floating) crossing point where the worst explicit-mode height turns negative.
    Assumes (checked empirically below) monotone decrease past the ridge."""
    for _ in range(iters):
        mid = (lo + hi)/2
        v, mu = exact_worst(C, Vref, E, H, mid)
        if v > 0: lo = mid
        else: hi = mid
    return hi, exact_worst(C, Vref, E, H, hi)

def bisect_cert_X0(C, which, H, excl, lo, hi, LAMBDA, WIN, tol=arb('0.01')):
    """Bisect the tightest X0 (to within tol) at which room27's landscape_leg CERTIFIES on [X0,LAMBDA]."""
    lo_f, hi_f = float(lo), float(hi)
    def ok(x0):
        try:
            landscape_leg(C, which, H, '', excl, arb(x0), LAMBDA, WIN)
            return True
        except CertFail:
            return False
    if not ok(hi_f): return None  # doesn't even certify at hi
    while hi_f - lo_f > float(tol):
        mid = (lo_f + hi_f)/2
        if ok(mid): hi_f = mid
        else: lo_f = mid
    return hi_f

if __name__ == '__main__':
    LAMBDA = arb(sys.argv[1]) if len(sys.argv) > 1 else arb(20)
    WIN = arb(sys.argv[2]) if len(sys.argv) > 2 else arb('0.05')
    t0 = time.time()
    C = Case(A, N)
    Vref = C.V(-3)
    E = (-I*C.TH).exp()
    href = (Vref*E).real
    print('N=6, 1/6: n=%d th*=%.6fdeg ell=%.4f |w|<=%.2e' %
          (C.n, float(C.th.mid())*180/PI.mid(), float(C.ell.mid()), float(C.w.abs_upper())))
    print('Room 28: (A) diagnostic -- is the Room 27 gap (0,4.2) a certificate artifact or genuine?')
    print('         (B) leg-by-leg tightest reachable boundary with the EXISTING (unmodified) machinery.')

    legs = [('-pi/6', -HEIGHT, -3), ('+pi/6', HEIGHT, -1)]

    print()
    print('=== (A) Exact (floating, no box/rad(X) term) worst explicit-mode height on each leg ===')
    saddle_re = 0.349119
    for label, H, excl in legs:
        Hf = float(H)
        print(' leg Im x=%s (excl mu=%d):' % (label, excl))
        for x0 in (0.01, saddle_re, 1.0, 2.0, 3.0):
            v, mu = exact_worst(C, Vref, E, Hf, x0)
            print('   x0=%.6f  exact worst=%+.5f at mu=%d  (>0 => GENUINELY unhealthy, not slack)' % (x0, v, mu))
        xc, (vc, muc) = find_true_crossing(C, Vref, E, Hf)
        print('   true (uncertified) crossing point: x0=%.6f (worst mode mu=%d, value~%.2e there)' % (xc, muc, vc))
        guard()

    print()
    print('=== (B) Leg-specific tightest certifiable X0 (bisected, tol=0.01, Arb-certified each point) ===')
    results = {}
    for label, H, excl in legs:
        best = {}
        for which in ('B', 'S'):
            b = bisect_cert_X0(C, which, H, excl, arb('3.0'), arb('5.0'), LAMBDA, WIN)
            best[which] = b
            print('  leg Im x=%s  %s: tightest certifiable X0 ~ %s' %
                  (label, which, ('%.4f' % b) if b is not None else 'not found in [3,5]'))
            guard()
        results[label] = best

    x0_minus = max(v for v in results['-pi/6'].values() if v is not None)
    x0_plus = max(v for v in results['+pi/6'].values() if v is not None)
    print()
    print('=== Final asymmetric certified run (X0 chosen per leg, +0.01 safety over the bisected boundary) ===')
    for label, H, excl, X0 in [('-pi/6', -HEIGHT, -3, x0_minus + 0.01), ('+pi/6', HEIGHT, -1, x0_plus + 0.01)]:
        for which in ('B', 'S'):
            try:
                o = landscape_leg(C, which, H, '', excl, arb(X0), LAMBDA, WIN)
                print('  leg Im x=%s  %s: X0=%.4f  Tref=%.4f  nd<=%.4f  domfar<=%.4f  rem<=%.4f  -> CERTIFIED' %
                      (label, which, X0, float(o['Tref'].mid()), float(o['nd'].upper()),
                       float(o['domfar'].upper()), float(o['rem'].upper())))
            except CertFail as ex:
                print('  leg Im x=%s  %s FAILED at X0=%.4f: %s' % (label, which, X0, ex))
        guard()

    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20
    print()
    print('elapsed %.1fs, peak RSS %.0f MB (cap %d MB)' % (time.time() - t0, rss, CAP_MB))
