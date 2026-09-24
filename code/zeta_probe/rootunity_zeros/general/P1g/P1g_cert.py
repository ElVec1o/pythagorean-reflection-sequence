# P1g_cert.py -- RIGOROUS (Arb) twisted single-saddle certificate (P1g Lemma Lap^pm) for Z^pm_N at a low seed p/q, side d>0,
# pieces d in [dlo, dhi] covering (0, r].  It is P1e_cert.certify (P1d Lemma lap + P1e Lemma O) with two changes (P1g Lemma F^pm):
#   (1) weights gam^s_k = (1/q) sum_nu zeta0^{-nu^2 - s nu - k nu}  (s = +1 for Z^+, s = -1 for Z^-);
#   (2) amplitude b^s_k(t) = e^{B_k(t)} e^{-s pi i t}; the factor |e^{-s pi i t}| = e^{s pi Im t} is enclosed exactly on the core
#       and bounded on each outer piece of the contour by its sup there (lower-ray tail: Gaussian with c_q halved, needs
#       Vneg >= 2 pi d / c_q).
# Certified, for every x = p/q + d in the piece, every N >= 151 with x = a/N, gcd(a,N)=1, under the Delta hypotheses of P1d Thm 9:
#   Z^s_N = C(x) S^s (1 + th_s),  |th_s| <= B_s,  C(x) = e(d/4) e^{i(alpha-pi/4)} sqrt(pi/2A) e^{F(t0)/d}  (common to s = +-1),
#   S^s = sum_k gam^s_k b^s_k(t0).   Hence omega = Z^-/(u0 Z^+) in S^-/(u0 S^+) (1+D(B_-))/(1+D(B_+)).
# Returns per piece: (dlo, dhi, S+, S-, B+, B-, u, x-ball, Aup, F0).
import sys
from math import gcd
sys.path.insert(0, '..')
from flint import arb, acb, ctx
from P1e_cert import setup_x, find_t0, li2_ball, e, PI, I, aup, alo, pos, Fail, need
ctx.prec = 160
def certify_pm(p, q, r, n2, ETA, V0, KAPPA, NP, DELTA0=arb('1e-3'), DELTA1=arb(1), KSEG=32, VQ='0.4', NPC=40, edges=None):
    ctx.prec = 160
    VQ = arb(VQ)
    need(gcd(p, q) == 1 and 0 < p < q, 'bad seed')
    need(r <= 1.0/(2*n2) and n2 >= q, 'need r <= 1/(2 n2) and n2 >= q')
    ETA = arb(ETA); V0 = arb(V0); KAPPA = arb(KAPPA)
    gam = {s: [sum((e(arb(((-nu*nu - s*nu - k*nu)*p) % q)/q) for nu in range(q)), acb(0))/q for k in range(q)] for s in (1, -1)}
    _, _, Uall, _ = setup_x(p, q, 0.0, r, n2)
    Bstar = find_t0(q, Uall, rad0=1e-6, grow=True)
    if edges is None: edges = [0.0] + [r/2**(NP - 1 - i) for i in range(NP)]
    out = []
    for ip in range(len(edges) - 1):
        dlo, dhi = edges[ip], edges[ip+1]; DH = arb(dhi)
        x, u, U, cn = setup_x(p, q, dlo, dhi, n2)
        Ua = aup(U)
        t0 = find_t0(q, U, center=acb(Bstar.mid()))
        need(Bstar.contains(t0), 'piece saddle ball not inside Bstar')
        W0 = U*e(-q*t0)
        F2 = PI*I*(1 + W0)/(1 - W0)
        A = alo(F2)/2; Aup = aup(F2)/2
        alpha = (PI - F2.arg())/2; sa, ca = alpha.sin(), alpha.cos()
        need(pos(sa) and pos(ca), 'alpha not in (0,pi/2)')
        Imt0_up = arb(t0.imag.upper()); t0a = aup(t0)
        v0 = V0.min(KAPPA*(DH/A).sqrt())
        def Bk(k, t, s, deriv=False):
            Wt = U*e(-q*t)
            val = -(1 - Wt).log()/(2*q) - s*PI*I*t
            d1 = -(2*PI*I*q*Wt/(1 - Wt))/(2*q) - s*PI*I
            d2 = ((2*PI*I*q)**2*Wt/(1 - Wt)**2)/(2*q)
            for n, cc in cn.items():
                term = cc*e(arb((k*n*p) % q)/q)*e(-n*t)
                val += term
                if deriv: d1 += term*(-2*PI*I*n); d2 += term*(-2*PI*I*n)**2
            return (val, d1, d2) if deriv else val
        S = {}; b0 = {}
        for s in (1, -1):
            b0[s] = [Bk(k, t0, s).exp() for k in range(q)]
            S[s] = sum((gam[s][k]*b0[s][k] for k in range(q)), acb(0))
            need(pos(alo(S[s])), 'S^%+d not bounded away from 0' % s)
        ea = acb(ca, sa)
        wseg = None; K3 = arb(0); K4 = arb(0)
        Bm = {s: [arb(0)]*q for s in (1, -1)}; Bd = {s: [arb(0)]*q for s in (1, -1)}; Kb = {s: [arb(0)]*q for s in (1, -1)}
        for j in range(KSEG):
            vb = (v0*(2*j - KSEG)/KSEG).union(v0*(2*j + 2 - KSEG)/KSEG)
            ts = t0 + ea*vb
            w = aup(U*e(-q*ts)); need(pos(1 - w), '|W|>=1 on core')
            wseg = w if wseg is None else wseg.max(w)
            K3 = K3.max(4*PI**2*q*w/(1 - w)**2/6)
            K4 = K4.max(8*PI**3*q**2*w*(1 + w)/(1 - w)**3/24)
            for s in (1, -1):
                for k in range(q):
                    v, d1, d2 = Bk(k, ts, s, True); ex = v.exp()
                    Bm[s][k] = Bm[s][k].max(aup(ex)); Bd[s][k] = Bd[s][k].max(aup(d1*ex)); Kb[s][k] = Kb[s][k].max(aup((d2 + d1*d1)*ex)/2)
        need(pos(A/2 - K3*v0), 'need K3 v0 <= A/2')
        Imseg_up = Imt0_up + v0*sa
        KE = lambda w: (2*PI/9 + 2/PI + 1)*w/(1 - w)
        dc = DH*KE(wseg) + DELTA0
        rho_eta = (2*PI*ETA).exp()
        w_eta = Ua*(2*PI*q*ETA).exp(); need(pos(1 - w_eta), 'w_eta >= 1')
        Beta = (-(1 - w_eta).log()/(2*q) + sum((aup(cc)*rho_eta**n for n, cc in cn.items()), arb(0))).exp()
        de = DH*KE(w_eta) + DELTA1
        need(pos(ETA - Imseg_up), 'core must stay below eta')
        X1 = arb(t0.real.lower()) + (ETA - Imt0_up)*arb((ca/sa).lower())
        Lt0 = li2_ball(W0)/(2*PI*I*q*q)
        C0 = (w_eta + w_eta**2/(4*(1 - w_eta)))/(2*PI*q*q) + PI*t0.real*t0.imag - Lt0.real
        C0 = arb(C0.upper())
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
        F0 = F0h
        vend = arb(((ETA - t0.imag)/sa).upper())
        Vq = (VQ*vend).max(v0)
        wloc = aup(U*e(-q*(t0 + ea*Vq))); need(pos(1 - wloc), 'wloc>=1')
        K3loc = 4*PI**2*q*wloc/(1 - wloc)**2/6
        Aloc = A - K3loc*Vq; need(pos(Aloc), "A'_loc <= 0 (lower VQ)")
        r4a = (Aup/Aloc).sqrt()*(v0*(Aloc/DH).sqrt()).erfc()
        Vneg = (8*Vq).max(12*t0a); r4c = arb(0)
        for jj in range(NPC):
            vb = (-Vq - (Vneg - Vq)*jj/NPC).union(-Vq - (Vneg - Vq)*(jj + 1)/NPC)
            tt = t0 + ea*vb; Wt = U*e(-q*tt)
            Ft = PI*I*tt*tt/2 + li2_ball(Wt)/(2*PI*I*q*q)
            kap = arb((-(Ft - F0).real).lower()); need(pos(kap), 'Re(F-F0) not < 0 on lower ray piece %d' % jj)
            need(pos(2*kap - DH), 'lower-ray monotonicity')
            r4c += (Vneg - Vq)/NPC*(-kap/DH).exp()
        r4c = r4c*(Aup/(PI*DH)).sqrt()
        w0u = aup(W0); Lmax = (w0u + w0u**2/(4*(1 - w0u)))/(2*PI*q*q)
        cq = PI*(2*alpha).sin()/2 - PI*t0a/Vneg - 2*Lmax/Vneg**2
        need(pos(cq), 'lower-ray tail quadratic <= 0 (raise Vneg)')
        need(bool(Vneg >= 2*PI*DH/cq), 'twist: Vneg < 2 pi d / c_q')
        r4ct = (2*Aup/cq).sqrt()*(Vneg*(cq/(2*DH)).sqrt()).erfc()/2     # tail with c_q halved (absorbs e^{pi v})
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
        # twist factors |e^{-s pi i t}| = e^{s pi Im t}; Im t0 in [t0.imag]
        Imlo, Imhi = arb(t0.imag.lower()), arb(t0.imag.upper())
        res = {}
        for s in (1, -1):
            def tw(lo_, hi_):   # sup of e^{s pi y} for y in [lo_, hi_]
                return (PI*(hi_ if s == 1 else -lo_)).exp()
            TWa = tw(Imlo - Vq*sa, Imhi + Vq*sa)                  # |v| <= Vq (r4a)
            TWc = tw(Imlo - Vneg*sa, Imhi - Vq*sa)                # lower ray pieces
            TWt = (PI*t0a).exp()                                  # lower-ray tail, after absorbing e^{pi |v| sin a}
            TWb = tw(Imlo + Vq*sa, ETA)                           # upper ray
            TWh = (s*PI*ETA).exp()                                # horizontal Im t = eta
            R4 = (r4a*TWa + r4c*TWc + r4ct*TWt + r4b*TWb)*Beta*de.exp()
            tot = arb(0)
            for k in range(q):
                b0a = aup(b0[s][k])
                Kc = Kb[s][k]/(2*A) + 3*(b0a*K4 + K3*Bd[s][k])/(4*A**2) + arb(15)/16*arb(2)**arb(3.5)*K3**2*Bm[s][k]/A**3
                rr = [DH*Kc, b0a*(v0*(A/DH).sqrt()).erfc(), (dc.exp() - 1)*arb(2).sqrt()*Bm[s][k], R4,
                      ((DH*Aup/PI).sqrt()/(PI*ETA)*(-gap2/DH).exp() + r5h)*TWh*Beta*de.exp()]
                tot += aup(gam[s][k])*sum(rr, arb(0))
            res[s] = arb((tot/alo(S[s])).upper())
        out.append((dlo, dhi, S[1], S[-1], res[1], res[-1], u, x, Aup, F0))
    return out
if __name__ == '__main__':
    from dround import fdn, fup
    a = sys.argv
    p, q, r, n2 = int(a[1]), int(a[2]), float(a[3]), int(a[4])
    rows = certify_pm(p, q, r, n2, a[5], a[6], a[7], int(a[8]))
    for (dlo, dhi, Sp, Sm, Bp, Bm_, u, x, Aup, F0) in rows:
        print('d in [%.3e,%.3e]: B+<=%s B-<=%s |S+|>=%s |S-|>=%s' % (dlo, dhi, fup(Bp, 3), fup(Bm_, 3), fdn(alo(Sp), 4), fdn(alo(Sm), 4)))
