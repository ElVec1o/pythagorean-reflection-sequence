# P1i_landscape_cert.py -- per-case RIGOROUS (Arb, python-flint) landscape certificate replacing the analytic constants
# of P1f Lemmas LS, LSp, head at small N (3 <= N <= 16).  FAILS LOUDLY (exit 1, 'CERT FAILED').
#
# For zeta = e(a/N) (notation of P1f_lemma.tex, Sections set/dec/est) it certifies, with theta in the ball
# THETA = theta* +- EPS_TH and |x_A| in [delta/2, 2 delta] (delta = 1/(8N)), x_A = |x_A| e^{i theta}:
#   (H) head:     H_head := delta*(ell + 2*(-log rho_N)) + (2 delta/N)(1 + log(1/(1.8 delta))) <= h_ref(theta) - eta,
#                 rho_N = 1 - (1/(4N)) e^{1/(4N)} / (2 sin(pi/N))                          [P1i Lemma head_N]
#   (a) every explicit NON-dominant mode mu, on Pi_mu = [x_A, x_mu] U (x_mu + e^{i theta/2}[0,oo)):
#                 Re((Omega_mu(x) - V_ref) e^{-i theta}) <= -eta
#   (b) each dominant mode mu, on Pi_mu:  near x_mu (sigma <= S0 on the segment, v <= V0 on the ray)
#                 Re(e^{-i theta} d^2 Omega_mu''(y)) < 0 on the whole piece (d = unit direction), which with
#                 Omega_mu'(x_mu) = 0 gives W_mu - h_mu <= -kappa |x - x_mu|^2 (Taylor, integral remainder);
#                 away from x_mu:  Re((Omega_mu(x) - V_mu) e^{-i theta}) < 0  (box scan)  + analytic ray tail.
#   (c) remainder modes mu_-+ on gamma_-+ = x_A + e^{i(theta -+ pi/8)}[0,oo):  Re((Omega - V_ref) e^{-i theta}) <= -eta
#   (d) Re x > 0 on every box (so Re x >= delta' > 0 on the compact pieces; rays have increasing Re x).
# V_ref = V_n (B, and S_pm for N odd: reference height h_n = T at theta*), V_ref = V_{n+1} (S_pm, N even: T').
# Mode sets (P1f Section dec): N odd: explicit nu in {-(2N-1)..2N}, mu = nu, remainders -2N, 2N+1;
#   N even: mu = 2 nu; eps=+1: explicit even mu in [-(4N-2), 4N], remainders -4N, 4N+2;
#           eps=-1: explicit odd mu in [-(4N-1), 4N-1], remainders -4N-1, 4N+1.  For S_pm (N even) eps flips.
# Enclosures: W on a box X by the centred form  Re((Omega(mid X) - V_ref) e^{-i THETA}) + rad(X) |Omega'(X)|;
#   Li2 only at exact midpoints; Omega' = L_mu - 2x - (2/N) Log(1 - e^{-2Nx}), Omega'' = -2 - 4/(e^{2Nx} - 1).
# Tails (analytic, in Arb): explicit ray v >= V1:  <= Re((V_mu - V_ref)e^{-i theta}) + C0 + C1 v - v^2,
#   C0 = (pi^2/6 + |Li2 w|)/N^2, C1 = 2|Log(1-w)|/N  (P1f Lemma saddle (iii));
#   remainder ray rho >= P1: Re((x L_mu - x^2) e^{-i theta}) + pi^2/(3N^2) - h_ref, a concave quadratic in rho.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1i_landscape_cert.py a/N [a/N ...]
#        perl -e 'alarm 290; exec @ARGV' python3 P1i_landscape_cert.py range N1 N2 [xlo]   (reduced a/N in [xlo, 1-xlo],
#        xlo default 0.143, a/N != 1/2)
import sys, time, resource
from math import gcd
from flint import arb, acb, ctx
ctx.prec = 128
CAP_MB = 3000
PI = arb.pi(); I = acb(0, 1)
import os
EPS_TH = arb('1e-5'); ALPHA = PI/8; ETA = arb(os.environ.get('P1I_ETA', '1e-3'))   # P1I_ETA: fail-injection test only
S0 = arb('0.08'); V0 = arb('0.25')
MAXDEPTH = 22

def guard():
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20
    if rss > CAP_MB: print('MEMORY GUARD %.0f MB, abort' % rss, flush=True); sys.exit(2)
class CertFail(Exception): pass
def fail(msg): raise CertFail(msg)
def up(v): return arb(v.upper())
def ball(lo, hi):  # arb ball containing [lo, hi]
    lo, hi = arb(lo), arb(hi); return arb((lo + hi)/2, (hi - lo)/2) + arb(0, 1e-40)
def cball(z): return acb(z.mid())
def radc(X): return (X.real.rad()**2 + X.imag.rad()**2).sqrt()

class Case:
    def __init__(self, a, N):
        self.a, self.N = a, N
        z = (2*PI*I*arb(a)/N).exp(); self.z = z
        c = -2*(1 - z); L = c.log(); self.L = L; self.ell = L.real; phi = L.imag
        X = c**N; B = 2 + X; w = 2/(B*(1 + (1 - 4/(B*B)).sqrt())); self.w = w
        if not bool(w.abs_upper() < 1): fail('%d/%d |w|<1 not certified' % (a, N))
        if not bool(((c**N)*w - (1 - w)**2).abs_upper() < arb('1e-25')): fail('w equation')
        self.xi = (1 - w).log()/N
        self.even = (N % 2 == 0); s = 2 if self.even else 1; self.s = s
        if not self.even: surv = lambda m: True
        elif N % 4 == 0: surv = lambda m: m % 2 == 0
        else: surv = lambda m: m % 2 == 1
        self.surv = surv
        n = min((m for m in range(-4*N-2, 4*N+3) if surv(m)), key=lambda m: abs(float((phi + 2*PI*(m + arb(s)/2)/N).mid())))
        self.n = n
        self.th = ((phi + 2*PI*(n + arb(s)/2)/N)/self.ell).atan()
        self.TH = self.th + arb(0, EPS_TH.upper())      # theta box
        self.delta = 1/(8*arb(N))
        self.C0 = (PI**2/6 + w.polylog(2).abs_upper())/N**2
        self.C1 = 2*(1 - w).log().abs_upper()/N
    def Lmu(self, mu): return self.L + 2*PI*I*mu/self.N
    def xs(self, mu): return self.Lmu(mu)/2 - self.xi
    def Om(self, x, mu):
        N = self.N
        return x*self.Lmu(mu) - x*x - (-2*N*x).exp().polylog(2)/N**2 + PI**2/(6*N**2)
    def dOm(self, x, mu):
        N = self.N
        return self.Lmu(mu) - 2*x - 2*(1 - (-2*N*x).exp()).log()/N
    def d2Om(self, x): return -2 - 4/((2*self.N*x).exp() - 1)
    def V(self, mu): return self.Om(self.xs(mu), mu)
    def Wup(self, X, mu, Vref):   # upper bound of Re((Omega_mu(X) - Vref) e^{-i TH}) over the box X
        if not bool(X.real.lower() > 0): return None
        xm = cball(X)
        v = ((self.Om(xm, mu) - Vref)*(-I*self.TH).exp()).real
        return up(v + radc(X)*self.dOm(X, mu).abs_upper())

def scan(f, lo, hi, thr, depth=0, stats=None):
    """certify f(interval) < thr on [lo,hi] (f returns arb upper bound or None); returns max upper bound found."""
    v = f(ball(lo, hi))
    if v is not None and bool(v < thr): return v
    if depth >= MAXDEPTH:
        return None
    m = (arb(lo) + arb(hi))/2
    v1 = scan(f, lo, m, thr, depth+1); 
    if v1 is None: return None
    v2 = scan(f, m, hi, thr, depth+1)
    if v2 is None: return None
    return v1.max(v2) if bool(v1 < v2) is False else v2.max(v1)

def target(f, lo, hi, thr, isdom, k=48):
    """threshold for the certified scan: min(thr, half the sampled maximum) -- only tightens, never weakens."""
    m = None
    for j in range(k+1):
        v = f(arb(lo) + (arb(hi) - arb(lo))*j/k)
        if v is None: fail('sample outside Re x > 0')
        m = v if m is None else m.max(v)
    if not bool(m < 0 if isdom else m < thr): fail('sampled maximum %s not below %s' % (m.str(5), thr.str(3)))
    return arb((m/2).upper()).min(thr) if not isdom else arb((m/2).upper())

def rho_pieces(C, k=4):
    d = C.delta; pts = [d/2 + (arb(2)*d - d/2)*j/k for j in range(k+1)]
    return [(pts[j], pts[j+1]) for j in range(k)]

def run(C, which):
    """which = 'B' or 'S'. returns dict of margins."""
    N = C.N; n = C.n; s = C.s
    if which == 'B':
        eps = -1 if N % 4 == 2 else 1
        dom = (n, n + s); ref = n; modeok = C.surv
    else:
        eps = 1 if N % 4 == 2 else -1
        dom = (n + 1,); ref = n + 1; modeok = lambda m: not C.surv(m)
    if not C.even:
        expl = list(range(-(2*N-1), 2*N+1)); rem = (-2*N, 2*N+1); dom = (n, n+1); ref = n; modeok = lambda m: True
    elif eps == 1:
        expl = list(range(-(4*N-2), 4*N+1, 2)); rem = (-4*N, 4*N+2)
    else:
        expl = list(range(-(4*N-1), 4*N, 2)); rem = (-4*N-1, 4*N+1)
    for m in dom:
        if m not in expl: fail('dominant mode %d not among the explicit modes' % m)
    for m in expl + list(rem) + list(dom):
        if not modeok(m): fail('%d/%d %s mode parity bookkeeping: mu=%d' % (C.a, N, which, m))
    Vref = C.V(ref); E = (-I*C.TH).exp()
    href = (Vref*E).real
    for m in dom:   # tie check: dominant heights equal at theta*
        if not bool(abs(float(((C.V(m) - Vref)*(-I*C.th).exp()).real.mid())) < 1e-20): fail('tie check %d' % m)
    # sanity: heights of all explicit modes <= href
    out = {'Tref': href}
    # head
    rhoN = 1 - (1/(4*arb(N)))*(1/(4*arb(N))).exp()/(2*(PI/N).sin())
    d = C.delta
    Hh = d*(C.ell + 2*(-(rhoN.log()))) + (2*d/N)*(1 + (1/(arb('1.8')*d)).log())
    mh = up(Hh - href)
    if not bool(mh < -ETA): fail('%d/%d %s head: H_head - h_ref = %s' % (C.a, N, which, mh.str(5)))
    out['head'] = mh
    worst_nd = arb(-100); worst_dq = arb(-100); worst_df = arb(-100); worst_rem = arb(-100)
    rps = rho_pieces(C)
    for mu in expl:
        xs = C.xs(mu); isdom = mu in dom
        Vr = C.V(mu) if isdom else Vref
        thr = arb(0) if isdom else -ETA
        dr = (I*C.TH/2).exp()
        if isdom:
            # dominant: polygon [x_A, P] U [P, x_mu] U ray, P = x_mu - lam e^{i theta/2}: the path crosses the saddle
            # along the steepest-descent line x_mu + v e^{i theta/2}, v in [-lam, oo).
            lam = arb((xs.real/(2*(C.TH/2).cos())).mid())
            def fq(vv):
                Y = xs + vv*dr
                return up(C.d2Om(Y).real) if bool(Y.real.lower() > 0) else None
            q = scan(fq, -V0, V0, target(fq, -V0, V0, arb(0), True))
            if q is None: fail('%d/%d %s dominant Taylor mu=%d' % (C.a, N, which, mu))
            worst_dq = worst_dq.max(q)
            f = lambda vv: C.Wup(xs - vv*dr, mu, Vr)
            v = scan(f, V0, lam, target(f, V0, lam, thr, True))
            if v is None: fail('%d/%d %s dominant descent line mu=%d' % (C.a, N, which, mu))
            worst_df = worst_df.max(v)
            Pm = xs - lam*dr
        for (r0, r1) in rps:
            XA = ball(r0, r1)*(I*C.TH).exp()
            tgt = Pm if isdom else xs
            f = lambda sg: C.Wup(tgt + sg*(XA - tgt), mu, Vr)
            v = scan(f, arb(0), arb(1), target(f, arb(0), arb(1), thr, isdom))
            if v is None: fail('%d/%d %s segment mu=%d rho=[%s,%s]' % (C.a, N, which, mu, r0.str(4), r1.str(4)))
            if isdom: worst_df = worst_df.max(v)
            else: worst_nd = worst_nd.max(v)
        lo = V0 if isdom else arb(0)
        hmu = up(((C.V(mu) - Vr)*E).real)
        V1 = arb(3)
        while True:
            tail = hmu + C.C0 + C.C1*V1 - V1**2
            if bool(V1 >= C.C1/2) and bool(tail < thr): break
            V1 = V1 + 1
            if bool(V1 > 50): fail('ray tail mu=%d' % mu)
        f = lambda vv: C.Wup(xs + vv*dr, mu, Vr)
        v = scan(f, lo, V1, target(f, lo, V1, thr, isdom))
        if v is None: fail('%d/%d %s ray mu=%d' % (C.a, N, which, mu))
        v = v.max(tail)
        if isdom: worst_df = worst_df.max(v)
        else: worst_nd = worst_nd.max(v)
        guard()
    # remainder rays
    for sgn, mu in ((-1, rem[0]), (1, rem[1])):
        be = C.TH + sgn*ALPHA          # direction theta -+ pi/8 : '-' for mu_-, '+' for mu_+
        dr = (I*be).exp()
        A2 = (C.TH + sgn*2*ALPHA).cos()
        if not bool(A2.lower() > 0) or not bool(be.cos().lower() > 0): fail('remainder ray geometry')
        for (r0, r1) in rps:
            XA = ball(r0, r1)*(I*C.TH).exp()
            A0 = up(((XA*C.Lmu(mu) - XA*XA)*E).real + PI**2/(3*N**2) - href)
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
            if v is None: fail('%d/%d %s remainder mu=%d rho=[%s,%s]' % (C.a, N, which, mu, r0.str(4), r1.str(4)))
            worst_rem = worst_rem.max(v).max(tail)
    out.update(nd=worst_nd, domq=worst_dq, domfar=worst_df, rem=worst_rem)
    return out

def fmt(v): return '%.4f' % float(v.upper()) if v is not None else '-'
if __name__ == '__main__':
    args = sys.argv[1:]
    if args[0] == 'range':
        N1, N2 = int(args[1]), int(args[2]); xlo = float(args[3]) if len(args) > 3 else 0.143
        cases = [(a, N) for N in range(N1, N2+1) for a in range(1, N) if gcd(a, N) == 1 and xlo <= a/N <= 1 - xlo and 2*a != N]
    else:
        cases = [tuple(int(t) for t in v.split('/')) for v in args]
    bad = []
    for a, N in cases:
      t0 = time.time()
      try:
        C = Case(a, N)
        parts = ['B'] + (['S'] if C.even else [])
        line = '%d/%d n=%d th*=%.3fdeg ell=%.4f |w|<=%.2e' % (a, N, C.n, float(C.th.mid())*180/3.141592653589793, float(C.ell.mid()), float(C.w.abs_upper()))
        okc = True
        for p in parts:
            try:
                o = run(C, p)
                line += ' | %s Tref=%.4f head-T<=%s nd<=%s domQ<=%s domfar<=%s rem<=%s' % (p, float(o['Tref'].mid()), fmt(o['head']), fmt(o['nd']), fmt(o['domq']), fmt(o['domfar']), fmt(o['rem']))
            except CertFail as ex:
                line += ' | %s FAILED: %s' % (p, ex); okc = False; bad.append('%d/%d:%s' % (a, N, p))
        print(line + ('  CERTIFIED' if okc else '  NOT CERTIFIED') + ' (%.1fs)' % (time.time() - t0), flush=True)
      except CertFail as ex:
        print('%d/%d CERT FAILED: %s' % (a, N, ex), flush=True); bad.append('%d/%d' % (a, N))
    if bad:
        print('CERT FAILED for %d of %d cases: %s' % (len(bad), len(cases), ' '.join(bad)), flush=True); sys.exit(1)
    print('ALL CERTIFIED: %d cases' % len(cases), flush=True)
