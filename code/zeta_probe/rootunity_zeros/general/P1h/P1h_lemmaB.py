# P1h_lemmaB.py -- RIGOROUS (Arb): Lemma B / B' (P1e) and Lemma B^pm (P1g) on the NEW region R0 = [1/6, 1/5] with the
# region hazard base y0 = 0.52 (radius 2 y0^n/n^2 for 10<=n<=52, y0^n/(4 tau) for n>=53, tau = 1/50).
# Both the untwisted bound (P1e_lemmaB.bound, s=0, for Theorem M') and the twisted one (P1g_lemmaB.bound_pm, s=+-1, for
# Theorem main' of P1g) are evaluated.  FAILS LOUDLY (exit 1) on any side condition or E, R > 1/2.
# Region parameters by environment (defaults = R0): P1H_Y (hazard base y), P1H_G (sup|u0|), P1H_ETA (crude contour height).
# P1H_NOMARGIN=1: omega-margin failures are reported but not fatal (use for the Z-only Theorem M').
# Modes:
#   exact FILES...     every seed j/n (10<=n<=150) in the P1h_seeds files: exact beta,P1,P2 (m<=200), exact |Z^s_n|, env^s;
#                      prints per-n max E, R, rho and min(margin - sigma).
#   crude n1 n2 OMEGA  uniform region bound g = 0.5(1+1e-6), eta = 0.0062 (g e^{2 pi eta} <= y0 checked), induction
#                      hypothesis |Z^s_n| >= c0 e^{-kappa n}; prints E, R and partial sums of sigma(n), rho(n) (|omega_n|<=OMEGA).
import sys
from flint import arb, acb, ctx
sys.path.insert(0, '..'); sys.path.insert(0, '../P1g')
from dround import fdn, fup
from P1e_lemmaB import bound
from P1g_lemmaB import bound_pm, loss
ctx.prec = 200
PI = arb.pi()
import os
Y0 = arb(os.environ.get('P1H_Y', '0.52')); TAU = arb('0.02')
GREG = os.environ.get('P1H_G', '0.5'); EREG = os.environ.get('P1H_ETA', '0.0062')   # crude-mode region sup|u0| and contour height
def e(z): return (2*PI*acb(0, 1)*z).exp()
def radius(n, y=Y0, tau=TAU):
    return 2*y**n/n**2 if n <= 52 else y**n/(4*tau)
def eu_of(n, d, g, wb):
    R0 = wb/((1 - wb)*PI*n); Nmin = (1/(n*d)).max(arb(151))
    return (4*PI*d*g + arb('4.6')*(Nmin*g.log()).exp()/Nmin + arb('4.6')*g**n/n + 2*PI*R0*(2*PI*R0).exp()).expm1()
def fail(msg):
    print('LEMMAB_R0 FAILED ' + msg, flush=True); sys.exit(1)
if __name__ == '__main__':
    mode = sys.argv[1]; y = Y0; tau = TAU
    if mode == 'exact':
        rows = []
        for fn in sys.argv[2:]:
            for line in open(fn):
                t = line.split(); j, n = int(t[0]), int(t[1])
                if n >= 10: rows.append((j, n, [arb(v) for v in t[2:10]]))
        worst = {}; cnt = 0; minm = None; maxE0 = arb(0)
        for (j, n, (Z0, Zp, Zm, envp, envm, om, marg, env0)) in rows:
            x0 = arb(j)/n; r = radius(n)
            xb = x0 + arb(0, arb(r.upper()))
            cl = arb((-2*(1 - e(xb))).abs_lower()); ell = cl.log()
            g = (1/cl)*(1 + arb('0.1')*(-151*ell).exp())
            eta = (y/g).log()/(2*PI)
            M = 200; S0 = arb(0); S1 = arb(0); S2 = arb(0)
            for m in range(1, M + 1):
                if m % n == 0: continue
                den = arb((1 - e(arb((-m*j) % n)/n)).abs_lower()) - 2*PI*m*r
                if not bool(den > 0): fail('den at %d/%d' % (j, n))
                t_ = y**m/(m*den); S0 += t_; S1 += 2*PI*m*t_; S2 += (2*PI*m)**2*t_
            tl = y**(M + 1)/(1 - y)
            S0 += n/2*tl/(M + 1); S1 += PI*n*tl; S2 += 2*PI**2*n*(M + 1)*tl/(1 - y)
            wb = y**n
            bpp = ((wb/(2*n*(1 - wb)) + S0).exp(), PI*wb/(1 - wb) + S1, 2*PI**2*n*wb/(1 - wb)**2 + S2)
            # s = 0 (Theorem M', P1e Lemma B')
            Tlo0 = Z0*(1 + wb)**(-arb(1)/(2*n))
            E0, R0_, side0 = bound(n, g, eta, tau, arb(0), arb(1), ell, dover=r, bpp=bpp, Tenv=(Tlo0, env0))
            bad = [k for k, v in side0 if not v]
            if bad or not (bool(E0 <= 0.5) and bool(R0_ <= 0.5)): fail('s=0 at %d/%d: E=%s R=%s %s' % (j, n, E0.str(3), R0_.str(3), bad))
            maxE0 = maxE0.max(E0)
            Eb = None
            for s, (Zs, env) in ((1, (Zp, envp)), (-1, (Zm, envm))):
                Tlo = Zs*(1 + wb)**(-arb(1)/(2*n))
                E, R, rho1, side = bound_pm(n, g, eta, tau, ell, r, bpp=bpp, Tenv=(Tlo, env))
                bad = [k for k, v in side if not v]
                if bad or not (bool(E <= 0.5) and bool(R <= 0.5)): fail('s=%+d at %d/%d: E=%s R=%s %s' % (s, j, n, E.str(3), R.str(3), bad))
                Eb = (E, R) if Eb is None else (Eb[0].max(E), Eb[1].max(R))
            E, R = Eb
            eu = eu_of(n, r, g, wb)
            rho = (1 + eu/(1 - eu))*((1 + R)*(1 + E)/((1 - R)*(1 - E)))**2 - 1
            sg = loss(rho, om, r); mrem = marg - sg
            cnt += 1; minm = mrem if minm is None else minm.min(mrem)
            w = worst.setdefault(n, [arb(0), arb(0), arb(0), None, arb(0)])
            w[0] = w[0].max(E); w[1] = w[1].max(R); w[2] = w[2].max(rho); w[3] = mrem if w[3] is None else w[3].min(mrem); w[4] = w[4].max(E0)
            if not bool(mrem > 0.05):
                if os.environ.get('P1H_NOMARGIN'): nbadm = globals().get('nbadm', 0) + 1; globals()['nbadm'] = nbadm; print('MARGIN-ONLY failure (omega part, not Z) at %d/%d: margin %s loss %s' % (j, n, marg.str(4), sg.str(4)), flush=True)
                else: fail('margin at %d/%d' % (j, n))
        for n in sorted(worst):
            w = worst[n]
            print('n=%d  maxE0<=%s  maxE+-<=%s maxR+-<=%s max rho<=%s  min(margin-loss)>=%s' % (n, fup(w[4], 3), fup(w[0], 3), fup(w[1], 3), fup(w[2], 3), fdn(w[3], 4)), flush=True)
        print('LEMMAB_R0 EXACT PASSED: %d seeds (10<=n<=%d, y=%s), max E0<=%s, min(margin_n - loss)>=%s' % (cnt, max(r[1] for r in rows), Y0.str(3), fup(maxE0, 3), fdn(minm, 4)), flush=True)
    else:
        n1, n2, OM = int(sys.argv[2]), int(sys.argv[3]), arb(sys.argv[4])
        c0, kappa = arb('0.02'), arb('0.005')
        g = arb(GREG)*(1 + arb('1e-6')); eta = arb(EREG)
        if not bool(g*(2*PI*eta).exp() <= y): fail('g e^{2 pi eta} > y0')
        ell = (1/g).log()
        tot = arb(0); totr = arb(0); maxE = arb(0); maxE0 = arb(0)
        for n in range(n1, n2 + 1):
            d = radius(n)
            E0, R0_, side0 = bound(n, g, eta, tau, kappa, c0, ell, dover=d)
            bad = [k for k, v in side0 if not v]
            if bad or not (bool(E0 <= 0.5) and bool(R0_ <= 0.5)): fail('crude s=0 n=%d E=%s R=%s %s' % (n, E0.str(3), R0_.str(3), bad))
            E, R, rho, side = bound_pm(n, g, eta, tau, ell, d, c0=c0, kappa=kappa)
            bad = [k for k, v in side if not v]
            if bad or not (bool(E <= 0.5) and bool(R <= 0.5)): fail('crude s=+-1 n=%d E=%s R=%s %s' % (n, E.str(3), R.str(3), bad))
            maxE = maxE.max(E); maxE0 = maxE0.max(E0)
            sn = loss(rho, OM, d); tot += sn; totr += rho
            if n % 500 == 0 or n == n1 or n == n2:
                print('n=%d  E0<=%s R0<=%s  E+-<=%s  rho(n)<=%s  sigma(n)<=%s  sum sigma<=%s' % (n, fup(E0, 3), fup(R0_, 3), fup(E, 3), fup(rho, 3), fup(sn, 3), fup(tot, 3)), flush=True)
        print('LEMMAB_R0 CRUDE PASSED %d<=n<=%d: max E0<=%s, max E+-<=%s, sum sigma<=%s, sum rho<=%s' % (n1, n2, fup(maxE0, 3), fup(maxE, 3), fup(tot, 3), fup(totr, 3)), flush=True)
