# P1e_lemmaB.py -- evaluates (in Arb, rigorously) the explicit error bound of Lemma B (P1e_lemma.tex): the uniform-in-n
# single-saddle estimate at a DEEP seed j/n in the hazard regime 0 < |d| <= eps_n = y^n/(4 tau), y = g*rho, rho = e^{2 pi eta}.
# Inputs: g (upper bound for |u0| on the arc piece), eta, tau, kappa, c0 (the inductive lower bound |Z_n(j/n)| >= c0 e^{-kappa n}),
#         ell_lo (lower bound for ell on the piece, for Lemma W), n range.
# Output per n: the bound  E(n) >= |Z_N/Main'_Z - 1|  and the ratio  R(n) = sqrt(2n) beta (e^{deltaR}-1) / (c0 e^{-kappa n}|1-w|^{-1/2n})
# used for |S_amp| >= (1 - R)|1-w_n|^{-1/2n} |Z_n|.  Lemma B holds at n if E(n) <= 1/2 and R(n) <= 1/2 and the side conditions pass.
# Every bound is monotone in d, so it is evaluated at d = eps_n.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1e_lemmaB.py g eta tau kappa c0 ell_lo n1 n2
import sys
from flint import arb, ctx
ctx.prec = 200
PI = arb.pi()
def bound(n, g, eta, tau, kappa, c0, ell_lo, dover=None, bpp=None, Tenv=None):
    # dover: radius (replaces eps_n); bpp: (beta, P1, P2) exact per-seed bounds; Tenv: (|T| lower, env upper) exact level-n data
    rho = (2*PI*eta).exp(); y = g*rho
    assert bool(y < 1)
    d = y**n/(4*tau) if dover is None else dover   # worst case d = radius (all terms increase with d)
    wb = y**n                               # |W| <= y^n on Im t <= eta
    L = -(1 - y).log()
    R0 = wb/((1 - wb)*PI*n)                 # |t0| <= R0 (contraction lemma)
    side = []
    side.append(('wb<1/3', bool(wb < arb(1)/3)))
    side.append(('R0<eta/4', bool(R0 < eta/4)))
    A = PI/2*(1 - wb)/(1 + wb); Aup = PI/2*(1 + wb)/(1 - wb)
    dal = 2*(wb/(1 - wb)).asin() if bool(wb/(1 - wb) < 1) else arb(10)     # |alpha - pi/4| <= |arg((1+W)/(1-W))|/2 <= asin(w/(1-w))
    alo = PI/4 - dal/2; sa = alo.sin(); side.append(('alpha ok', bool(alo > 0.5)))
    cot = (PI/4 + dal/2).cos()/(PI/4 + dal/2).sin()
    v0 = eta/2
    side.append(('core below eta', bool(R0 + v0 < eta)))
    K3 = 4*PI**2*n*wb/(1 - wb)**2/6; K4 = 8*PI**3*n**2*wb*(1 + wb)/(1 - wb)**3/24
    side.append(('K3 v0 <= A/2', bool(K3*v0 <= A/2)))
    beta = (wb/(2*n*(1 - wb)) + n*L/2).exp()
    P1 = PI*wb/(1 - wb) + PI*n*y/(1 - y)
    P2 = 2*PI**2*n*wb/(1 - wb)**2 + 2*PI**2*n*y/(1 - y)**2
    if bpp is not None: beta, P1, P2 = bpp
    Bd = P1*beta; Kb = (P1**2 + P2)*beta/2
    n2 = arb((1/(2*n*d)).lower()) - 1          # any n2 <= 1/(2nd) is admissible; only a lower bound is used
    side.append(('n2 >= n', bool(n2 >= n)))
    Delta = tau/n2                           # Delta_N(x;rho) <= sum_{m>n2} tau/m^2 <= tau/n2  (hazard lemma H)
    KE = lambda w: (2*PI/9 + 2/PI + 1)*w/(1 - w)
    dc = d*KE(wb) + Delta
    r1 = d*(Kb/(2*A) + 3*(beta*K4 + K3*Bd)/(4*A**2) + arb(15)/16*arb(2)**arb(3.5)*K3**2*beta/A**3)
    r2 = beta*(v0*(A/d).sqrt()).erfc()
    r3 = dc.expm1()*arb(2).sqrt()*beta
    S2 = 2*PI*wb/(1 - wb); L2 = 2*PI*wb/(1 - wb)
    Ap = A - (S2 + L2)/2; side.append(("A'>0", bool(Ap > 0)))
    r4 = (Aup/Ap).sqrt()*(v0*(Ap/d).sqrt()).erfc()*beta*dc.exp()
    X1 = -R0 + (eta - R0)*cot
    C0 = (wb + wb**2/(4*(1 - wb)))/(2*PI*n*n) + PI*R0*R0 + (wb + wb**2/(4*(1 - wb)))/(2*PI*n*n)
    gap = PI*eta*X1 - C0; side.append(('gap>0, d<=2gap', bool(gap > 0) and bool(2*gap > d)))
    r5 = (d*Aup/PI).sqrt()/(PI*eta)*(-gap/d).exp()*beta*dc.exp()
    # renormalisation defect deltaR (Lemma R, quantitative)
    # Lemma W at level N: |lam_N^2-1| <= 4.6 |c|^{-N}/N, and in the hazard regime N >= 1/(n d) >= Nmin = 4 tau/(n y^n)
    Nmin = (1/(n*d)).max(arb(151))                  # x = a/N != j/n  =>  d >= 1/(nN)
    lamN = arb('4.6')*(Nmin*g.log()).exp()/Nmin
    lamn = arb('4.6')*g**n/n                                   # Lemma W at level n: needs |c0|^n >= e^3
    side.append(('n ell >= 3', bool(n*ell_lo >= 3)))
    cq = 4*PI*d*g                                              # |c0/c - 1| <= 4 pi d/|c| <= 4 pi d g
    et = 2*PI*R0*(2*PI*R0).exp()
    eu = (cq + lamN + lamn + et).expm1()          # prod(1+a_i) - 1 <= e^{sum a_i} - 1
    yp = (1 + eu)*g
    dR = (wb/(1 - wb) + wb/(1 - wb))/(2*n) + n/2*eu*yp/(1 - yp) + PI/4*n**2*d*g/(1 - g) + n/4*((n2 + 1)*g.log()).exp()/((n2 + 1)*(1 - g))
    if Tenv is None:
        Zlo = c0*(-kappa*n).exp()*(1 - wb)**(arb(1)/(2*n))      # |1-w_n|^{-1/2n} |Z_n| >= this
        R = (2*n)**0.5*beta*dR.expm1()/Zlo
    else:
        Zlo, env = Tenv
        R = env*dR.expm1()/Zlo
    Samp_lo = (1 - R)*Zlo
    E = (2*n)**0.5*(r1 + r2 + r3 + r4 + r5)/Samp_lo if bool(R < 1) else arb('inf')
    return E, R, side
if __name__ == '__main__':
    g, eta, tau, kappa, c0, ell = [arb(s) for s in sys.argv[1:7]]
    n1, n2 = int(sys.argv[7]), int(sys.argv[8])
    yh = arb(sys.argv[9]) if len(sys.argv) > 9 else None     # hazard base: radius eps_n = yh^n/(4 tau)
    first = None
    for n in range(n1, n2 + 1):
        E, R, side = bound(n, g, eta, tau, kappa, c0, ell, dover=None if yh is None else yh**n/(4*tau))
        if yh is not None: side.append(('g e^{2 pi eta} <= yh', bool(g*(2*PI*eta).exp() <= yh)))
        ok = all(v for _, v in side) and bool(E <= 0.5) and bool(R <= 0.5)
        bad = [k for k, v in side if not v]
        print('n=%d  E(n)<=%s  R(n)<=%s  %s %s' % (n, E.str(3, radius=False), R.str(3, radius=False), 'OK' if ok else 'fail', bad), flush=True)
