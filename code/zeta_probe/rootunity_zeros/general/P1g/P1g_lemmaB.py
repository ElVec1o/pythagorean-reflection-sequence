# P1g_lemmaB.py -- RIGOROUS (Arb): the twisted deep-seed estimate (P1g Lemma B^pm) and the omega-inheritance loss (P1g Lemma I).
# It is P1e_lemmaB.bound with the twist b^s(t) = e^{B_k(t)} e^{-s pi i t} (s = +-1) of P1g Lemma F^pm:
#   * on the core and at t0 the factor |e^{-s pi i t}| <= e^{pi (R0+v0)} <= e^{pi eta};  P1 -> P1 + pi (b' = (B' - s pi i) b);
#   * outer ray: |e^{-s pi i t}| <= e^{pi R0} e^{pi |v|}, absorbed by halving the Gaussian (needs v0 >= 2 pi d / A');
#     r4 -> sqrt(2A/A') erfc(v0 sqrt(A'/(2d))) beta e^{pi R0} e^{delta_eta};
#   * horizontal part Im t = eta: factor e^{pi eta};
#   * Lemma R: S^s_amp = e^{-s pi i t0} (T^s + err),  |err| <= env^s (e^{delta_R} - 1),  |S^s| >= e^{-pi R0}(1-R^s)|T^s|.
# Output: E (>= |Z^s_N/Main^s - 1|), R, and the relative omega-loss
#   rho = (1 + eu/(1-eu)) (1+R)^2 (1+E)^2 / ((1-R)^2 (1-E)^2) - 1   >=  |omega_N/omega_n - 1|   (E, R = max over s).
# Modes:
#   exact FILES...        : every seed j/n (10 <= n <= 150) listed in the P1g_seeds output files; radius 2y^n/n^2 (n<=52),
#                           y^n/(4 tau) (n>=53); level-n data |Z^s_n|, env^s, |omega_n|, margin_n from the files.
#                           Prints per-n max E, R, rho and min (margin_n - sigma), sigma = 1.5|omega_n| rho + r (3 pi (1+|omega_n|)/2 + 4 pi).
#   crude n1 n2 OMEGA     : uniform bound at every region (g_i, eta_i of P1e), IH |Z^s_n| >= c0 e^{-kappa n}; prints E, R,
#                           rho, sigma(n) (with |omega_n| <= OMEGA) and the partial sums of sigma(n), rho(n).
# FAILS LOUDLY (exit 1) if a side condition fails or E, R > 1/2.
import sys
from math import gcd
from flint import arb, acb, ctx
sys.path.insert(0, '..')
from dround import fdn, fup
ctx.prec = 200
PI = arb.pi()
def e(z): return (2*PI*acb(0, 1)*z).exp()
def bound_pm(n, g, eta, tau, ell_lo, d, bpp=None, Tenv=None, c0=None, kappa=None):
    rho_ = (2*PI*eta).exp(); y = g*rho_
    assert bool(y < 1)
    wb = y**n
    L = -(1 - y).log()
    R0 = wb/((1 - wb)*PI*n)
    side = []
    side.append(('wb<1/3', bool(wb < arb(1)/3)))
    side.append(('R0<eta/4', bool(R0 < eta/4)))
    A = PI/2*(1 - wb)/(1 + wb); Aup = PI/2*(1 + wb)/(1 - wb)
    dal = 2*(wb/(1 - wb)).asin() if bool(wb/(1 - wb) < 1) else arb(10)
    alo = PI/4 - dal/2; side.append(('alpha ok', bool(alo > 0.5)))
    cot = (PI/4 + dal/2).cos()/(PI/4 + dal/2).sin()
    v0 = eta/2
    side.append(('core below eta', bool(R0 + v0 < eta)))
    K3 = 4*PI**2*n*wb/(1 - wb)**2/6; K4 = 8*PI**3*n**2*wb*(1 + wb)/(1 - wb)**3/24
    side.append(('K3 v0 <= A/2', bool(K3*v0 <= A/2)))
    beta = (wb/(2*n*(1 - wb)) + n*L/2).exp()
    P1 = PI*wb/(1 - wb) + PI*n*y/(1 - y)
    P2 = 2*PI**2*n*wb/(1 - wb)**2 + 2*PI**2*n*y/(1 - y)**2
    if bpp is not None: beta, P1, P2 = bpp
    TWc = (PI*eta).exp()                      # twist on core / at t0 / horizontal
    P1t = P1 + PI
    bc = beta*TWc
    Bd = P1t*bc; Kb = (P1t**2 + P2)*bc/2
    n2 = arb((1/(2*n*d)).lower()) - 1
    side.append(('n2 >= n', bool(n2 >= n)))
    Delta = tau/n2
    KE = lambda w: (2*PI/9 + 2/PI + 1)*w/(1 - w)
    dc = d*KE(wb) + Delta
    r1 = d*(Kb/(2*A) + 3*(bc*K4 + K3*Bd)/(4*A**2) + arb(15)/16*arb(2)**arb(3.5)*K3**2*bc/A**3)
    r2 = bc*(v0*(A/d).sqrt()).erfc()
    r3 = dc.expm1()*arb(2).sqrt()*bc
    S2 = 2*PI*wb/(1 - wb); L2 = 2*PI*wb/(1 - wb)
    Ap = A - (S2 + L2)/2; side.append(("A'>0", bool(Ap > 0)))
    side.append(('v0 >= 2 pi d/Ap (twist)', bool(v0 >= 2*PI*d/Ap)))
    r4 = (2*Aup/Ap).sqrt()*(v0*(Ap/(2*d)).sqrt()).erfc()*beta*(PI*R0).exp()*dc.exp()
    X1 = -R0 + (eta - R0)*cot
    C0 = (wb + wb**2/(4*(1 - wb)))/(2*PI*n*n) + PI*R0*R0 + (wb + wb**2/(4*(1 - wb)))/(2*PI*n*n)
    gap = PI*eta*X1 - C0; side.append(('gap>0, d<=2gap', bool(gap > 0) and bool(2*gap > d)))
    r5 = (d*Aup/PI).sqrt()/(PI*eta)*(-gap/d).exp()*beta*TWc*dc.exp()
    Nmin = (1/(n*d)).max(arb(151))
    lamN = arb('4.6')*(Nmin*g.log()).exp()/Nmin
    lamn = arb('4.6')*g**n/n
    side.append(('n ell >= 3', bool(n*ell_lo >= 3)))
    cq = 4*PI*d*g
    et = 2*PI*R0*(2*PI*R0).exp()
    eu = (cq + lamN + lamn + et).expm1()
    yp = (1 + eu)*g
    dR = (wb/(1 - wb) + wb/(1 - wb))/(2*n) + n/2*eu*yp/(1 - yp) + PI/4*n**2*d*g/(1 - g) + n/4*((n2 + 1)*g.log()).exp()/((n2 + 1)*(1 - g))
    if Tenv is None:
        Zlo = c0*(-kappa*n).exp()*(1 - wb)**(arb(1)/(2*n)); env = (2*n)**0.5*beta
    else:
        Zlo, env = Tenv
    R = env*dR.expm1()/Zlo
    Samp_lo = (-PI*R0).exp()*(1 - R)*Zlo
    E = (2*n)**0.5*(r1 + r2 + r3 + r4 + r5)/Samp_lo if bool(R < 1) else arb('inf')
    if bool(eu < 1) and bool(E < 1) and bool(R < 1):
        rho = (1 + eu/(1 - eu))*((1 + R)*(1 + E)/((1 - R)*(1 - E)))**2 - 1
    else: rho = arb('inf')
    return E, R, rho, side
REG = [(0.2, 0.25, '0.42535', '0.0257'), (0.25, 1/3, '0.35357', '0.055'), (1/3, 0.4, '0.28869', '0.087'), (0.4, 0.5, '0.26288', '0.102')]
def radius(n, y=arb('0.5'), tau=arb('0.02')):
    return 2*y**n/n**2 if n <= 52 else y**n/(4*tau)
def loss(rho, om, r):
    return 1.5*om*rho + r*(3*PI*(1 + om)/2 + 4*PI)
if __name__ == '__main__':
    mode = sys.argv[1]; tau = arb('0.02'); y = arb('0.5')
    if mode == 'exact':
        rows = []
        for fn in sys.argv[2:]:
            for line in open(fn):
                t = line.split(); j, n = int(t[0]), int(t[1])
                if n >= 10: rows.append((j, n, [arb(v) for v in t[2:9]]))
        worst = {}; cnt = 0; minm = None
        for (j, n, (Z0, Zp, Zm, envp, envm, om, marg)) in rows:
            x0 = arb(j)/n; r = radius(n)
            xb = x0 + arb(0, arb(r.upper()))
            cl = arb((-2*(1 - e(xb))).abs_lower()); ell = cl.log()
            g = (1/cl)*(1 + arb('0.1')*(-151*ell).exp())
            eta = (y/g).log()/(2*PI)
            # exact beta, P1, P2 as P1e_lemmaBp (sums over m <= 200; |1-zeta^{-m}| >= |1-zeta0^{-m}| - 2 pi m r)
            M = 200; S0 = arb(0); S1 = arb(0); S2 = arb(0)
            for m in range(1, M + 1):
                if m % n == 0: continue
                den = arb((1 - e(arb((-m*j) % n)/n)).abs_lower()) - 2*PI*m*r
                if not bool(den > 0): print('LEMMAB FAILED den at %d/%d' % (j, n)); sys.exit(1)
                t_ = y**m/(m*den); S0 += t_; S1 += 2*PI*m*t_; S2 += (2*PI*m)**2*t_
            tl = y**(M + 1)/(1 - y)
            S0 += n/2*tl/(M + 1); S1 += PI*n*tl; S2 += 2*PI**2*n*(M + 1)*tl/(1 - y)
            wb = y**n
            bpp = ((wb/(2*n*(1 - wb)) + S0).exp(), PI*wb/(1 - wb) + S1, 2*PI**2*n*wb/(1 - wb)**2 + S2)
            Eb = None
            for s, (Zs, env) in ((1, (Zp, envp)), (-1, (Zm, envm))):
                Tlo = Zs*(1 + wb)**(-arb(1)/(2*n))
                E, R, rho1, side = bound_pm(n, g, eta, tau, ell, r, bpp=bpp, Tenv=(Tlo, env))
                bad = [k for k, v in side if not v]
                if bad or not (bool(E <= 0.5) and bool(R <= 0.5)):
                    print('LEMMAB FAILED at %d/%d s=%+d: E=%s R=%s %s' % (j, n, s, E.str(3), R.str(3), bad), flush=True); sys.exit(1)
                Eb = (E, R) if Eb is None else (Eb[0].max(E), Eb[1].max(R))
            E, R = Eb
            # recompute eu exactly as in bound_pm for the omega loss
            d = r; R0 = wb/((1 - wb)*PI*n); Nmin = (1/(n*d)).max(arb(151))
            eu = (4*PI*d*g + arb('4.6')*(Nmin*g.log()).exp()/Nmin + arb('4.6')*g**n/n + 2*PI*R0*(2*PI*R0).exp()).expm1()
            rho = (1 + eu/(1 - eu))*((1 + R)*(1 + E)/((1 - R)*(1 - E)))**2 - 1
            sg = loss(rho, om, r)
            mrem = marg - sg
            cnt += 1; minm = mrem if minm is None else minm.min(mrem)
            w = worst.setdefault(n, [arb(0), arb(0), arb(0), None])
            w[0] = w[0].max(E); w[1] = w[1].max(R); w[2] = w[2].max(rho); w[3] = mrem if w[3] is None else w[3].min(mrem)
            if not bool(mrem > 0.05):
                print('LEMMAB FAILED margin at %d/%d: margin %s - loss %s' % (j, n, marg.str(4), sg.str(4)), flush=True); sys.exit(1)
        for n in sorted(worst):
            w = worst[n]
            print('n=%d  maxE<=%s maxR<=%s max rho<=%s  min(margin-loss)>=%s' % (n, fup(w[0], 3), fup(w[1], 3), fup(w[2], 3), fdn(w[3], 4)), flush=True)
        print('LEMMAB EXACT PASSED: %d seeds, min(margin_n - loss) >= %s' % (cnt, fdn(minm, 4)), flush=True)
    else:
        n1, n2, OM = int(sys.argv[2]), int(sys.argv[3]), arb(sys.argv[4])
        c0, kappa = arb('0.02'), arb('0.005')
        tot = arb(0); totr = arb(0); maxE = arb(0)
        for n in range(n1, n2 + 1):
            sn = arb(0); rn = arb(0)
            for (xl, xh, gs, es) in REG:
                g, eta = arb(gs)*(1 + arb('1e-6')), arb(es)     # g_i enlarged by 1e-6 (hazard discs are 1e-15 wide)
                ell = (1/g).log()
                d = radius(n)
                E, R, rho, side = bound_pm(n, g, eta, tau, ell, d, c0=c0, kappa=kappa)
                side.append(('g e^{2 pi eta} <= y', bool(g*(2*PI*eta).exp() <= y)))
                bad = [k for k, v in side if not v]
                if bad or not (bool(E <= 0.5) and bool(R <= 0.5)):
                    print('LEMMAB FAILED crude n=%d region %s: E=%s R=%s %s' % (n, gs, E.str(3), R.str(3), bad), flush=True); sys.exit(1)
                maxE = maxE.max(E)
                sn = sn.max(loss(rho, OM, d)); rn = rn.max(rho)
            tot += sn; totr += rn
            if n % 100 == 0 or n == n1 or n == n2:
                print('n=%d  E<=%s  rho(n)<=%s  sigma(n)<=%s  sum sigma<=%s  sum rho<=%s' % (n, fup(E, 3), fup(rn, 3), fup(sn, 3), fup(tot, 3), fup(totr, 3)), flush=True)
        print('LEMMAB CRUDE PASSED %d<=n<=%d: max E<=%s, sum_{n} sigma(n) <= %s, sum rho(n) <= %s' % (n1, n2, fup(maxE, 3), fup(tot, 3), fup(totr, 3)), flush=True)
