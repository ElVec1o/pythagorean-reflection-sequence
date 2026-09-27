# room27_landscape_cert.py -- RIGOROUS (Arb, python-flint) landscape certificate on the ACTUAL
# constant-height legs of room20_seat_direct.tex Sec.4: Gamma_-^(6) at Im x = -pi/6 (through the
# saddle x_{-3} = 0.349119... - i pi/6) and Pi_0^(6) at Im x = +pi/6 (through x_{-1} = 0.349119...+i pi/6).
#
# Room 22 certified only the REAL-AXIS (Im x = 0) approach segment feeding into these legs; this room
# extends the same P1i_landscape_cert.py machinery (Case/Wup/scan/target, all imported UNMODIFIED) to
# boxes that sit directly on the two constant-height lines themselves, using the confirmed Room 17/19
# separation-constant fact that the d(x) >= 1 - e^{-2 Re(x)} bound is ANGLE-INDEPENDENT: it depends only
# on Re(x), not on theta or Im(x) (Room 19 Sec. "Consequence" -- the bound "depends only on Re(x) ... and
# uniformly over Im(x)"). That is exactly what licenses moving Wup's box off the real axis onto Im x=+-pi/6
# while reusing the identical centred-form machinery: Wup(X, mu, Vref) takes an arbitrary acb box X, not
# necessarily a ray through the origin, and the rotation e^{-i TH} used throughout is fixed at theta*=0
# (the tie-ray direction), independent of where the box sits.
#
# SCOPE: this certifies the landscape bounds (a)/(c)/(d)-type: Re((Omega_mu(x)-Vref) e^{-i TH}) <= -eta
# strictly below -ETA on each constant-height leg for Re x in [X0, LAMBDA], EXCLUDING a small window
# around the one saddle that sits exactly on that leg (mu=-3 for Im x=-pi/6, mu=-1 for Im x=+pi/6) -- at
# its own saddle the height touches its own reference by definition, exactly as room22's mode-exclusion
# handled the real-axis case. It does NOT redo the head check (H) (room20 Sec.1/room22 Sec.1: B's head
# fails, S's does not -- unchanged, orthogonal to this room). It does NOT certify Re x <= 0 (the crossing
# region, room20 Sec.5, still open) or the saddle box itself (P1i's own delta-box, which already covers a
# small neighbourhood of the saddle at N=6 only for S_pm, per room22 Sec.1).
#
# Usage: perl -e 'alarm 290; exec @ARGV' python3 room27_landscape_cert.py [LAMBDA] [X0] [WIN]
#   defaults LAMBDA=10, X0=1.0, WIN=0.05
import sys, os, time, resource
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'P1i'))
from P1i_landscape_cert import (Case, CertFail, fail, ball, cball, radc, up, scan, target,
                                 PI, I, ALPHA, ETA, S0, V0, CAP_MB, guard)
from flint import arb, acb, ctx

A, N = 1, 6   # zeta_0 = e(1/6), theta* = 0 exactly (room20 Sec.0/3)
HEIGHT = PI/6

def landscape_leg(C, which, H, sign_label, excl_mu, r0, r1, win):
    """Certify the (a)/(c)/(d)-type landscape bound on the constant-height box line Im x = H (H = +-pi/6),
    Re x in [r0, r1], for the mode family 'which' in {'B','S'}. excl_mu is the mode whose saddle sits
    exactly on THIS line (mu=-3 for H=-pi/6, mu=-1 for H=+pi/6 -- room20 Sec.4); a window of half-width
    win around its saddle's real part is excluded, exactly as room22 did for the real-axis case (there
    the excluded mode's OWN reference tie means no negative margin can hold in an arbitrarily small
    neighbourhood of its own saddle). Every surviving piece must certify strictly below -ETA."""
    Nn = C.N; n = C.n; s = C.s
    if which == 'B':
        dom = (n, n + s); ref = n
    else:
        dom = (n + 1,); ref = n + 1
    if not C.even:
        fail('N=6 is even; odd branch unused')
    eps = -1 if Nn % 4 == 2 else 1
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
    worst_nd = arb(-100); worst_df = arb(-100); worst_rem = arb(-100)
    # (d) Re x > 0 on every box: r0 > 0 directly bounds every box's real part from below.
    if not bool(arb(r0) > 0): fail('(d) leg segment not certified Re x>0 (need X0>0)')
    for mu in expl:
        xs = C.xs(mu); isdom = mu in dom
        Vr = C.V(mu) if isdom else Vref
        thr = -ETA
        xr = arb(xs.real.mid())
        if mu == excl_mu and bool(xr > r0) and bool(xr < r1):
            pieces = []
            if bool(xr - win > r0): pieces.append((r0, xr - win))
            if bool(xr + win < r1): pieces.append((xr + win, r1))
            if not pieces: fail('window covers the whole interval for mu=%d' % mu)
        else:
            pieces = [(r0, r1)]
        for (rr0, rr1) in pieces:
            if not bool(arb(rr0) < arb(rr1)): fail('empty piece mu=%d [%s,%s]' % (mu, arb(rr0).str(4), arb(rr1).str(4)))
            # box on the constant-height line: real part ranges over [rr0,rr1], imaginary part fixed at H
            f = lambda vv: C.Wup(vv + I*H, mu, Vr)
            v = scan(f, rr0, rr1, target(f, rr0, rr1, thr, False))
            if v is None: fail('%s mode mu=%d leg segment [%s,%s]' % (which, mu, arb(rr0).str(4), arb(rr1).str(4)))
            if isdom: worst_df = worst_df.max(v)
            else: worst_nd = worst_nd.max(v)
        guard()
    # remainder rays, base point at Re x = r1, Im x = H (far end of the certified leg segment)
    for sgn, mu in ((-1, rem[0]), (1, rem[1])):
        be = C.TH + sgn*ALPHA
        dr = (I*be).exp()
        A2 = (C.TH + sgn*2*ALPHA).cos()
        if not bool(A2.lower() > 0) or not bool(be.cos().lower() > 0): fail('remainder ray geometry')
        XA = r1 + I*H
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
    return dict(nd=worst_nd, domfar=worst_df, rem=worst_rem, Tref=href)

def fmt(v):
    try: return '%.4f' % float(v.upper())
    except Exception: return 'n/a'

if __name__ == '__main__':
    LAMBDA = arb(sys.argv[1]) if len(sys.argv) > 1 else arb(10)
    X0 = arb(sys.argv[2]) if len(sys.argv) > 2 else arb('1.0')
    WIN = arb(sys.argv[3]) if len(sys.argv) > 3 else arb('0.05')
    t0 = time.time()
    C = Case(A, N)
    print('N=6, 1/6: n=%d th*=%.6fdeg (certified box +-1e-5) ell=%.4f |w|<=%.2e' %
          (C.n, float(C.th.mid())*180/3.141592653589793, float(C.ell.mid()), float(C.w.abs_upper())))
    print('Certifying landscape (a)/(c)/(d) on the constant-height legs Im x = +-pi/6, Re x in [%s, %s]' %
          (X0.str(3), LAMBDA.str(3)))
    print('(room20 Sec.4: Gamma_-^(6) at Im x=-pi/6 through x_{-3}, Pi_0^(6) at Im x=+pi/6 through x_{-1}).')
    print('Head check (H) NOT redone here (known: B fails, S passes -- room20 Sec.1/room22 Sec.1).')
    legs = [('-pi/6', -HEIGHT, -3), ('+pi/6', HEIGHT, -1)]
    bad = []
    for label, H, excl in legs:
        for which in ('B', 'S'):
            try:
                o = landscape_leg(C, which, H, label, excl, X0, LAMBDA, WIN)
                print('  leg Im x=%s  %s: Tref=%.4f  nd<=%s  domfar<=%s  rem<=%s  -> CERTIFIED' %
                      (label, which, float(o['Tref'].mid()), fmt(o['nd']), fmt(o['domfar']), fmt(o['rem'])))
            except CertFail as ex:
                print('  leg Im x=%s  %s FAILED: %s' % (label, which, ex)); bad.append('%s:%s' % (label, which))
        guard()
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20
    print('elapsed %.1fs, peak RSS %.0f MB (cap %d MB)' % (time.time() - t0, rss, CAP_MB))
    if bad:
        print('NOT CERTIFIED: %s' % bad); sys.exit(1)
    print('ALL CERTIFIED (constant-height legs, LAMBDA=%s, X0=%s, WIN=%s)' % (LAMBDA.str(4), X0.str(4), WIN.str(4)))
