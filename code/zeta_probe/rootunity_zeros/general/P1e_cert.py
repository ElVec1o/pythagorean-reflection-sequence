# P1e_cert.py -- P1d_cert.py with a SHARPENED OUTER-RAY BOUND (P1e_lemma.tex, Lemma O): the crude r4 (one global A')
# is replaced by (a) a local A'_loc on |v|<=Vq, (b) A'_neg on the lower ray (|W|<=|W(t0)| there), (c) Arb enclosures of
# Re(F(t)-F(t0)) on NPC sub-balls of the upper ray [Vq, v_end].  Extra CLI arg: VQ (fraction of v_end), NPC.
# Original header:
# P1d_cert.py -- RIGOROUS (Arb ball arithmetic, python-flint) certificate of Lemma 5 (Lemma (1''-Delta)) of P1d_lemma.tex
# for one seed p/q and the side d = x - p/q in (0, r].  (The side d<0 at p/q is the side d>0 at (q-p)/q: Lemma 2, conjugation.)
#
# Certified statement, for every real x in (p/q, p/q + r] (a continuum, covered by the pieces below) and every N >= 151,
# every residue class of N mod 4, every a with x = a/N, gcd(a,N)=1:
#   |Z_N(x)/Main'(x) - 1| <= B      provided  Delta_N(x; rho_core) <= DELTA0  and  Delta_N(x; rho_eta) <= DELTA1,
# where Z_N = Sigma_N / (G*_N e^{-Phi_N(eps)}) (Theorem 1), Main'(x) = e^{i(alpha-pi/4)} sqrt(pi/(2A)) e^{F(t0)/d} S_amp,
# Delta_N(x;rho) = sum_{n>n2, n notin M(d), N not| n} (|u| rho)^n / (n |1-zeta^{-n}|)  (the deep-rational tail).
# It also prints N*: for 151 <= N <= N*, both Delta hypotheses hold automatically (|1-zeta^{-n}| >= 4/N), so the bound is
# unconditional there.  All inequalities are Lemmas 3-5 of P1d_lemma.tex; each Arb quantity is valid for ALL x in the piece.
#
# CLI: perl -e 'alarm 290; exec @ARGV' python3 P1d_cert.py p q r n2 eta V0 kappa npieces [DELTA0 DELTA1 KSEG]
import sys
from math import gcd
from dround import fdn, fup
from flint import arb, acb, ctx
ctx.prec = 160
PI = arb.pi(); I = acb(0, 1)
def e(x): return (2*PI*I*x).exp()
def aup(z): return arb(z.abs_upper())
def alo(z): return arb(z.abs_lower())
def pos(x): return bool(x > 0)
class Fail(Exception): pass
def need(c, msg):
    if not c: raise Fail(msg)

def li2_ball(W, M=60):   # Li2(W) for |W|<1 with rigorous tail
    s = acb(0); Wm = acb(1)
    for m in range(1, M+1): Wm = Wm*W; s += Wm/(m*m)
    w = aup(W); need(pos(1 - w), '|W|>=1 in Li2')
    t = w**(M+1)/((M+1)**2*(1 - w))
    return s + acb(arb(0, t.upper()), arb(0, t.upper()))

def setup_x(p, q, dlo, dhi, n2):
    dball = arb(dlo).union(arb(dhi))
    x = arb(p)/q + dball
    zeta = e(x); c = -2*(1 - zeta)
    l_lo = arb(c.abs_lower()).log(); need(bool(l_lo > arb('0.02')), 'need l >= 0.02 (Lemma W)')
    el = arb((0.1*(-151*l_lo).exp()).upper())          # Lemma W: |lam^2 - 1| <= 0.1 e^{-151 l} for N >= 151
    u = (1/c)*(1 + acb(arb(0, el), arb(0, el)))
    th = arb(acb(u.mid()).arg().mid())                # branch-safe log: log(u e^{-i th}) + i th, exp(n lu) = u^n
    lu = (u*(-I*th).exp()).log() + I*th; U = (q*lu).exp()
    cn = {}
    for n in range(1, n2+1):
        if n % q == 0: continue
        den = 1 - e(-n*x); need(pos(alo(den)), 'rational of height <= n2 in the x-ball (n=%d)' % n)
        cn[n] = (n*lu).exp()/n/den
    return x, u, U, cn

def krawczyk(q, U, center, rad):
    # unique zero of f(t) = pi i t + (1/q) log(1 - U e(-q t)) in the ball: K(B) inside B (interior)
    m = acb(center)
    B = acb(arb(m.real.mid(), rad), arb(m.imag.mid(), rad))
    WB = U*e(-q*B)
    if not pos(1 - aup(WB)): return None
    fpB = PI*I*(1 + WB)/(1 - WB)
    Wm = U*e(-q*m); fm = PI*I*m + (1 - Wm).log()/q
    Um = acb(U.mid()); Wmm = Um*e(-q*m); Y = 1/acb((PI*I*(1 + Wmm)/(1 - Wmm)).mid())
    K = m - Y*fm + (1 - Y*fpB)*(B - m)
    return B if B.contains_interior(K) else None

def find_t0(q, U, center=None, rad0=1e-14, maxit=80, grow=False):
    Um = acb(U.mid()); t = acb(0) if center is None else center
    for _ in range(100): t = (I/(PI*q))*(1 - Um*e(-q*t)).log()      # approximate fixed point (midpoint U)
    t = acb(t.mid()); rt = rad0
    for _ in range(maxit):
        B = krawczyk(q, U, t, rt)
        if B is not None:
            if not grow: return B
            for _ in range(40):          # enlarge while Krawczyk still succeeds (larger uniqueness ball)
                B2 = krawczyk(q, U, t, rt*2)
                if B2 is None: break
                B = B2; rt *= 2
            return B
        rt *= 2
    raise Fail('Krawczyk failed for t0')

def certify(p, q, r, n2, ETA, V0, KAPPA, NP, DELTA0=arb('1e-3'), DELTA1=arb(1), KSEG=48, verbose=True, VQ=0.3, NPC=64):
    VQ = arb(VQ)
    need(gcd(p, q) == 1 and 0 < p < q, 'bad seed')
    need(r <= 1.0/(2*n2) and n2 >= q, 'need r <= 1/(2 n2) and n2 >= q')
    ETA = arb(ETA); V0 = arb(V0); KAPPA = arb(KAPPA)
    gam = [sum((e(arb(((-nu*nu - k*nu)*p) % q)/q) for nu in range(q)), acb(0))/q for k in range(q)]
    # global saddle ball Bstar valid for all x in (p/q, p/q + r]: defines t0(x) = unique zero of F'_x in Bstar
    _, _, Uall, _ = setup_x(p, q, 0.0, r, n2)
    Bstar = find_t0(q, Uall, rad0=1e-6, grow=True)
    edges = [0.0] + [r/2**(NP - 1 - i) for i in range(NP)]
    Bmax = arb(0); Nmin = None; rows = []
    for ip in range(NP):
        dlo, dhi = edges[ip], edges[ip+1]; DH = arb(dhi)
        x, u, U, cn = setup_x(p, q, dlo, dhi, n2)
        ua = aup(u); Ua = aup(U)
        t0 = find_t0(q, U, center=acb(Bstar.mid()))
        need(Bstar.contains(t0), 'piece saddle ball not inside Bstar')
        W0 = U*e(-q*t0)
        F2 = PI*I*(1 + W0)/(1 - W0)
        A = alo(F2)/2; Aup = aup(F2)/2
        alpha = (PI - F2.arg())/2; sa, ca = alpha.sin(), alpha.cos()
        need(pos(sa) and pos(ca), 'alpha not in (0,pi/2)')
        L2t0 = aup(2*PI*I*W0/(1 - W0))
        Imt0_up = arb(t0.imag.upper())
        v0 = V0.min(KAPPA*(DH/A).sqrt())
        def Bk(k, t, deriv=False):
            Wt = U*e(-q*t)
            val = -(1 - Wt).log()/(2*q)
            d1 = -(2*PI*I*q*Wt/(1 - Wt))/(2*q)
            d2 = ((2*PI*I*q)**2*Wt/(1 - Wt)**2)/(2*q)
            for n, cc in cn.items():
                term = cc*e(arb((k*n*p) % q)/q)*e(-n*t)
                val += term
                if deriv: d1 += term*(-2*PI*I*n); d2 += term*(-2*PI*I*n)**2
            return (val, d1, d2) if deriv else val
        b0 = [Bk(k, t0).exp() for k in range(q)]
        S = sum((gam[k]*b0[k] for k in range(q)), acb(0))
        Slo = alo(S); need(pos(Slo), 'S_amp not bounded away from 0')
        ea = acb(ca, sa)
        wseg = None; K3 = arb(0); K4 = arb(0)
        Bm = [arb(0)]*q; Bd = [arb(0)]*q; Kb = [arb(0)]*q
        for j in range(KSEG):
            vb = (v0*(2*j - KSEG)/KSEG).union(v0*(2*j + 2 - KSEG)/KSEG)
            ts = t0 + ea*vb
            w = aup(U*e(-q*ts)); need(pos(1 - w), '|W|>=1 on core')
            wseg = w if wseg is None else wseg.max(w)
            K3 = K3.max(4*PI**2*q*w/(1 - w)**2/6)
            K4 = K4.max(8*PI**3*q**2*w*(1 + w)/(1 - w)**3/24)
            for k in range(q):
                v, d1, d2 = Bk(k, ts, True); ex = v.exp()
                Bm[k] = Bm[k].max(aup(ex)); Bd[k] = Bd[k].max(aup(d1*ex)); Kb[k] = Kb[k].max(aup((d2 + d1*d1)*ex)/2)
        need(pos(A/2 - K3*v0), 'need K3 v0 <= A/2')
        Imseg_up = Imt0_up + v0*sa
        rho_core = (2*PI*arb(Imseg_up.upper())).exp()
        KE = lambda w: (2*PI/9 + 2/PI + 1)*w/(1 - w)
        dc = DH*KE(wseg) + DELTA0
        rho_eta = (2*PI*ETA).exp()
        w_eta = Ua*(2*PI*q*ETA).exp(); need(pos(1 - w_eta), 'w_eta >= 1')
        S2 = 2*PI*w_eta/(1 - w_eta)
        Ap = A   # (unused: replaced by Lemma O below)
        Beta = (-(1 - w_eta).log()/(2*q) + sum((aup(cc)*rho_eta**n for n, cc in cn.items()), arb(0))).exp()
        de = DH*KE(w_eta) + DELTA1
        need(pos(ETA - Imseg_up), 'core must stay below eta')
        X1 = arb(t0.real.lower()) + (ETA - Imt0_up)*arb((ca/sa).lower())
        Lt0 = li2_ball(W0)/(2*PI*I*q*q)
        C0 = (w_eta + w_eta**2/(4*(1 - w_eta)))/(2*PI*q*q) + PI*t0.real*t0.imag - Lt0.real
        C0 = arb(C0.upper())
        # Lemma O(d): horizontal part split at X2; [X1,X2] by Arb enclosures of Re(F-F0), [X2,inf) by the crude gap.
        F0h = PI*I*t0*t0/2 + li2_ball(W0)/(2*PI*I*q*q)
        X2 = X1.max(2*C0.max(arb(0))/(PI*ETA) + arb('1e-12'))
        gap2 = PI*ETA*X2 - C0; need(pos(gap2), 'Gamma_2 gap <= 0')
        need(pos(2*gap2 - DH), 'Gamma_2 monotonicity needs d <= 2 gap')
        r5h = arb(0)
        if bool(X2 > X1):
            NPH = 64
            for jj in range(NPH):
                Xb = (X1 + (X2 - X1)*jj/NPH).union(X1 + (X2 - X1)*(jj + 1)/NPH)
                th_ = acb(Xb, ETA)
                Wt = U*e(-q*th_); need(pos(1 - aup(Wt)), '|W|>=1 on horizontal')
                Ft = PI*I*th_*th_/2 + li2_ball(Wt)/(2*PI*I*q*q)
                kap = arb((-(Ft - F0h).real).lower()); need(pos(kap), 'Re(F-F0) not < 0 on horizontal piece %d' % jj)
                need(pos(2*kap - DH), 'horizontal monotonicity')
                r5h += (X2 - X1)/NPH*(-kap/DH).exp()
            r5h = r5h*(Aup/(PI*DH)).sqrt()
        # ---- Lemma O: sharpened outer ray ----
        F0 = PI*I*t0*t0/2 + li2_ball(W0)/(2*PI*I*q*q)
        vend = arb(((ETA - t0.imag)/sa).upper())
        Vq = (VQ*vend).max(v0)
        wloc = aup(U*e(-q*(t0 + ea*Vq))); need(pos(1 - wloc), 'wloc>=1')
        K3loc = 4*PI**2*q*wloc/(1 - wloc)**2/6
        Aloc = A - K3loc*Vq; need(pos(Aloc), "A'_loc <= 0 (lower VQ)")      # Re(F-F0) <= -A v^2 + K3loc |v|^3 on |v|<=Vq
        r4a = (Aup/Aloc).sqrt()*(v0*(Aloc/DH).sqrt()).erfc()
        # lower ray: Arb pieces on [-Vneg,-Vq], then the quadratic tail bound (Lemma O(b))
        Vneg = (8*Vq).max(12*arb(t0.abs_upper())); r4c = arb(0)
        for jj in range(NPC):
            vb = (-Vq - (Vneg - Vq)*jj/NPC).union(-Vq - (Vneg - Vq)*(jj + 1)/NPC)
            tt = t0 + ea*vb; Wt = U*e(-q*tt)
            Ft = PI*I*tt*tt/2 + li2_ball(Wt)/(2*PI*I*q*q)
            kap = arb((-(Ft - F0).real).lower()); need(pos(kap), 'Re(F-F0) not < 0 on lower ray piece %d' % jj)
            need(pos(2*kap - DH), 'lower-ray monotonicity')
            r4c += (Vneg - Vq)/NPC*(-kap/DH).exp()
        r4c = r4c*(Aup/(PI*DH)).sqrt()
        w0u = aup(W0); Lmax = (w0u + w0u**2/(4*(1 - w0u)))/(2*PI*q*q)      # |Li2(W)| <= w + w^2/(4(1-w)) on |W| <= w0
        cq = PI*(2*alpha).sin()/2 - PI*arb(t0.abs_upper())/Vneg - 2*Lmax/Vneg**2
        need(pos(cq), 'lower-ray tail quadratic <= 0 (raise Vneg)')
        r4c += (Aup/cq).sqrt()*(Vneg*(cq/DH).sqrt()).erfc()/2
        r4b = arb(0); kmin = None
        if bool(Vq < vend):
            for jj in range(NPC):
                vb = (Vq + (vend - Vq)*jj/NPC).union(Vq + (vend - Vq)*(jj + 1)/NPC)
                tt = t0 + ea*vb
                Wt = U*e(-q*tt); need(pos(1 - aup(Wt)), '|W|>=1 on upper ray')
                Ft = PI*I*tt*tt/2 + li2_ball(Wt)/(2*PI*I*q*q)
                kap = arb((-(Ft - F0).real).lower()); need(pos(kap), 'Re(F-F0) not < 0 on upper ray piece %d' % jj)
                kmin = kap if kmin is None else kmin.min(kap)
                r4b += (vend - Vq)/NPC*(-kap/DH).exp()
            need(pos(2*kmin - DH), 'upper-ray monotonicity needs d <= 2 kappa')
            r4b = r4b*(Aup/(PI*DH)).sqrt()
        R4 = (r4a + r4c + r4b)*Beta*de.exp()
        tot = arb(0); parts = [arb(0)]*5
        for k in range(q):
            b0a = aup(b0[k])
            Kc = Kb[k]/(2*A) + 3*(b0a*K4 + K3*Bd[k])/(4*A**2) + arb(15)/16*arb(2)**arb(3.5)*K3**2*Bm[k]/A**3
            rr = [DH*Kc,
                  b0a*(v0*(A/DH).sqrt()).erfc(),
                  (dc.exp() - 1)*arb(2).sqrt()*Bm[k],
                  R4,
                  ((DH*Aup/PI).sqrt()/(PI*ETA)*(-gap2/DH).exp() + r5h)*Beta*de.exp()]
            tot += aup(gam[k])*sum(rr, arb(0))
            parts = [a.max(aup(gam[k])*b/Slo) for a, b in zip(parts, rr)]
        Bb = arb((tot/Slo).upper())
        def Nstar(rho, Dl):
            g = ua*rho; need(pos(1 - g), '|u| rho >= 1')
            return 4*Dl*(n2 + 1)*(1 - g)/g**(n2 + 1)
        Ns = Nstar(rho_core, DELTA0).min(Nstar(rho_eta, DELTA1))
        Bmax = Bmax.max(Bb); Nmin = Ns if Nmin is None else Nmin.min(Ns)
        row = 'piece d in [%.3e,%.3e]: B<=%s N*>=%s |S|>=%s A>=%s A\'>=%s v0=%s K3<=%s w_seg<=%s w_eta<=%s gap2>=%s parts=%s' % (
            dlo, dhi, fup(Bb, 3), fdn(Ns, 3), fdn(Slo, 4), fdn(A, 4),
            Ap.str(3, radius=False), v0.str(3, radius=False), K3.str(3, radius=False), wseg.str(3, radius=False),
            w_eta.str(3, radius=False), gap2.str(3, radius=False), [z.str(2, radius=False) for z in parts])
        rows.append(row)
        if verbose: print(row, flush=True)
    return Bmax, Nmin, Bstar, rows

if __name__ == '__main__':
    a = sys.argv
    p, q, r, n2 = int(a[1]), int(a[2]), float(a[3]), int(a[4])
    ETA, V0, KAPPA, NP = a[5], a[6], a[7], int(a[8])
    D0 = arb(a[9]) if len(a) > 9 else arb('1e-3'); D1 = arb(a[10]) if len(a) > 10 else arb(1)
    KS = int(a[11]) if len(a) > 11 else 48
    VQa = a[12] if len(a) > 12 else '0.3'; NPCa = int(a[13]) if len(a) > 13 else 64
    try:
        Bmax, Nmin, Bstar, rows = certify(p, q, r, n2, ETA, V0, KAPPA, NP, D0, D1, KS, VQ=VQa, NPC=NPCa)
        print('SEED %d/%d side d>0: r=%g n2=%d eta=%s V0=%s kappa=%s DELTA0=%s DELTA1=%s t0-ball=%s => B <= %s, N* >= %s' % (
            p, q, r, n2, ETA, V0, KAPPA, D0.str(3, radius=False), D1.str(3, radius=False), Bstar.str(5), fup(Bmax, 4), fdn(Nmin, 3)))
        print('CERTIFIED' if bool(Bmax < 1) else 'NOT CERTIFIED (B >= 1)')
    except Fail as ex:
        print('FAILED:', ex)
