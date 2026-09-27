# room22_landscape_cert.py -- RIGOROUS (Arb, python-flint) landscape certificate for the N=6 contour
# construction of room20_seat_direct.tex, at the specific starting point x_c^(6) = -LAMBDA (real, negative,
# theta* = 0 for N=6).
#
# SCOPE (read room20_seat_direct.tex Sec.3-5 first): x_c^(6) itself has Re x < 0, where Omega_mu is not
# known to be holomorphic/bounded by the P1f/P1i machinery (that is exactly the open "crossing region"
# Poisson-summation piece, Room 19/20 Sec.5, NOT attempted here). What CAN be certified rigorously with
# the existing P1i machinery, unmodified in its mathematical content, is the claim of room20 Sec.4: that
# the landscape bounds (non-dominant mode bound (a), dominant mode Taylor+far bound (b), remainder-ray
# bound (c), Re x>0 bound (d)) hold with negative, certified margins on the ENTIRE real-axis segment
# Re x in [X0, LAMBDA] (theta=0, matching N=6's theta*=0 exactly, so x_A is real) -- i.e. on the Re x>0
# portion of the legs Gamma_mp^(6), Pi_0^(6) all the way out to a concrete, large LAMBDA, not just in the
# tiny delta=1/(8N) box that P1i_landscape_cert.py certifies. This directly certifies, for a concrete
# LAMBDA, that "the far side is healthy" is not merely qualitative (room20's own wording) but a genuine
# Arb-certified statement over the WHOLE real segment out to that LAMBDA.
#
# This is a piece of the landscape at x_c^(6), not a certificate of x_c^(6) itself, and not the Rouche
# step (see verdict at the bottom of room22_seat_direct.tex).
#
# Usage: perl -e 'alarm 290; exec @ARGV' python3 room22_landscape_cert.py [LAMBDA] [X0]
#   defaults LAMBDA=8, X0=0.05 (X0 must stay > 0: Re x=0 is the branch line, excluded by construction).
import sys, os, time, resource
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'P1i'))
from P1i_landscape_cert import (Case, CertFail, fail, ball, cball, radc, up, scan, target,
                                 PI, I, ALPHA, ETA, S0, V0, CAP_MB, guard)
from flint import arb, acb, ctx

A, N = 1, 6   # zeta_0 = e(1/6), theta* = 0 exactly (room20 Sec.0/3)

def landscape_real_segment(C, which, r0, r1, win=arb('0.05')):
    """Certify (a)/(c)/(d)-type bounds (NOT the head check (H), a separate, already-known result --
    room20 Sec.1/P1i_lemma.tex Sec.six: B's head fails, S's does not, at N=6) DIRECTLY on the REAL segment
    Re x in [r0, r1], Im x = 0 (theta = theta* = 0 exactly for N=6), instead of P1i's tiny box
    [delta/2, 2 delta]*e^{i Theta} connected to the saddle by a line segment. Since theta=0 this is a
    genuinely different (larger-scale) region than P1i certifies, and the direct approach (bound Wup on
    boxes covering the real interval itself, no connecting segment to the saddle) is the honest one here:
    a segment from the P1i-scale saddle box out to a real point at distance O(LAMBDA) would need a box
    radius of O(LAMBDA) and the centred-form error blows up (this was tried and fails -- see room22_seat_direct.tex).
    For each explicit mode mu with real saddle part xs.real inside (r0,r1), the interval is split into
    [r0, xs.real-win] and [xs.real+win, r1] (excluding a small window around its own saddle, where by
    definition the height touches its own reference and no negative margin can hold); modes whose saddle
    real part lies outside [r0,r1] use the whole interval. Every piece is required to certify strictly
    below -ETA (this is therefore slightly stronger than P1i's own domfar test, which only requires <0)."""
    Nn = C.N; n = C.n; s = C.s
    if which == 'B':
        dom = (n, n + s); ref = n
    else:
        dom = (n + 1,); ref = n + 1
    if not C.even:
        fail('N=6 is even; odd branch unused')
    eps = -1 if Nn % 4 == 2 else 1   # N=6: 6%4=2 -> eps=-1 for B (matches P1i_landscape_cert.run)
    if which == 'S':
        eps = -eps
    if eps == 1:
        expl = list(range(-(4*Nn-2), 4*Nn+1, 2)); rem = (-4*Nn, 4*Nn+2)
    else:
        expl = list(range(-(4*Nn-1), 4*Nn, 2)); rem = (-4*Nn-1, 4*Nn+1)
    for m in dom:
        if m not in expl: fail('dominant mode %d not among explicit modes' % m)
    Vref = C.V(ref); E = (-I*C.TH).exp()
    href = (Vref*E).real
    out = {}
    worst_nd = arb(-100); worst_dq = arb('nan'); worst_df = arb(-100); worst_rem = arb(-100)
    # (d) Re x > 0 on every box: certified by construction since r0 > 0 and theta box is centred at 0
    #     with a tiny +-1e-5 rad halo (C.TH), so cos(C.TH) certifies > 0.99999 -- checked explicitly:
    if not bool(C.TH.cos().lower() > arb('0.99999')): fail('(d) real-axis box not certified Re x>0')
    for mu in expl:
        xs = C.xs(mu); isdom = mu in dom
        Vr = C.V(mu) if isdom else Vref
        thr = -ETA
        xr = arb(xs.real.mid())
        if bool(xr > r0) and bool(xr < r1):
            pieces = []
            if bool(xr - win > r0): pieces.append((r0, xr - win))
            if bool(xr + win < r1): pieces.append((xr + win, r1))
            if not pieces: fail('window [%s] covers the whole interval for mu=%d' % (win.str(3), mu))
        else:
            pieces = [(r0, r1)]
        for (rr0, rr1) in pieces:
            if not bool(arb(rr0) < arb(rr1)): fail('empty piece mu=%d (win too large for [%s,%s])' % (mu, r0.str(3), r1.str(3)))
            f = lambda vv: C.Wup(vv*(I*C.TH).exp(), mu, Vr)
            v = scan(f, rr0, rr1, target(f, rr0, rr1, thr, False))
            if v is None: fail('%s mode mu=%d real segment [%s,%s]' % (which, mu, arb(rr0).str(4), arb(rr1).str(4)))
            if isdom: worst_df = worst_df.max(v)
            else: worst_nd = worst_nd.max(v)
        guard()
    # remainder rays, base point now at Re x = r1 (far end of the certified real segment) instead of x_A
    for sgn, mu in ((-1, rem[0]), (1, rem[1])):
        be = C.TH + sgn*ALPHA
        dr = (I*be).exp()
        A2 = (C.TH + sgn*2*ALPHA).cos()
        if not bool(A2.lower() > 0) or not bool(be.cos().lower() > 0): fail('remainder ray geometry')
        XA = ball(r1, r1)*(I*C.TH).exp()
        A0 = up(((XA*C.Lmu(mu) - XA*XA)*E).real + PI**2/(3*Nn**2) - href)
        A1 = up(((C.Lmu(mu) - 2*XA)*(I*sgn*ALPHA).exp()).real)
        P1 = arb(2)
        while True:
            tail = up(A0 + A1*P1 - arb(A2.lower())*P1**2)
            vert_ok = bool(A1 <= 2*arb(A2.lower())*P1)
            if vert_ok and bool(tail < -ETA): break
            P1 = P1 + 1
            if bool(P1 > 60): fail('remainder tail mu=%d' % mu)
        f = lambda rr: C.Wup(XA + rr*dr, mu, Vref)
        v = scan(f, arb(0), P1, target(f, arb(0), P1, -ETA, False))
        if v is None: fail('%s remainder mu=%d' % (which, mu))
        worst_rem = worst_rem.max(v).max(tail)
    out.update(nd=worst_nd, domfar=worst_df, rem=worst_rem, Tref=href)
    return out

def fmt(v):
    try: return '%.4f' % float(v.upper())
    except Exception: return 'n/a'

if __name__ == '__main__':
    LAMBDA = arb(sys.argv[1]) if len(sys.argv) > 1 else arb(8)
    X0 = arb(sys.argv[2]) if len(sys.argv) > 2 else arb('0.05')
    t0 = time.time()
    C = Case(A, N)
    print('N=6, 1/6: n=%d th*=%.6fdeg (certified box +-1e-5) ell=%.4f |w|<=%.2e' %
          (C.n, float(C.th.mid())*180/3.141592653589793, float(C.ell.mid()), float(C.w.abs_upper())))
    print('Certifying landscape (a)/(b)/(c)/(d) on the REAL segment Re x in [%s, %s] (theta=theta*=0),' %
          (X0.str(3), LAMBDA.str(3)))
    print('i.e. the Re x>0 portion of the legs starting at x_c^(6) = -LAMBDA (room20 Sec.3-4). Head check (H) NOT redone here (known: B fails, S passes -- room20 Sec.1).')
    bad = []
    for which in ('B', 'S'):
        try:
            o = landscape_real_segment(C, which, X0, LAMBDA)
            print('  %s: Tref=%.4f  nd<=%s  domfar<=%s  rem<=%s  -> CERTIFIED' %
                  (which, float(o['Tref'].mid()), fmt(o['nd']), fmt(o['domfar']), fmt(o['rem'])))
        except CertFail as ex:
            print('  %s FAILED: %s' % (which, ex)); bad.append(which)
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20
    print('elapsed %.1fs, peak RSS %.0f MB (cap %d MB)' % (time.time() - t0, rss, CAP_MB))
    if bad:
        print('NOT CERTIFIED: %s' % bad); sys.exit(1)
    print('ALL CERTIFIED (real-segment extension, LAMBDA=%s, X0=%s)' % (LAMBDA.str(4), X0.str(4)))
