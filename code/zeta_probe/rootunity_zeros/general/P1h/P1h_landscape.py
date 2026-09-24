# P1h_landscape.py -- RIGOROUS (Arb) evaluation of the displayed estimates of P1f Lemmas LS and LSp (landscape) and Lemma
# head, with ell >= ell1 (instead of ell >= ell0 = 0.85483) and N >= N1.  Every estimate of the P1f proofs is written as an
# explicit function of (ell, N); the ell-dependence is monotone (see P1h_lemma.tex, Lemma LS(ell1)): the height-type
# margins T(ell) - 2 delta ell, T - W_{D<0}, T - H_head increase with ell for ell > 1/(2N), and the size bounds |L_mu|,
# |x - x_mu| are taken at ell_max = log 4.  So it suffices to evaluate heights at ell = ell1 and sizes at ell = log 4.
# Checks, for every N in [N1, N2] and s in {1,2} (N odd / even):
#   theta_max = atan(pi s/(N ell1)) < pi/4, quadratic coefficient cos(theta_max + pi/4) > 0, remainder linear coefficient < 0;
#   (a)  non-dominant: (2 pi^2 s^2 cos - C_R)/N^2 > 0  and  W_{D<0} < T;  (a') even: (4 pi^2 cos - C_R)/N^2 > 0, W_{D<0} < T';
#   (b)  dominant: D > 0, D - c_Taylor > 0, -D/4 + C_R/N^2 < 0;  (b') same with T' and D' = ell^2/4 - 2 delta ell;
#   (c)  remainder: 2 delta ell + pi^2/(3N^2) < T;   head: H_head < T;   Lemma W: N ell1 >= 3.
# Prints the minimal margin; FAILS LOUDLY (exit 1) if any check fails.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1h_landscape.py ell1 N1 N2      (ell1 as a decimal string or 'log2')
#        ... python3 P1h_landscape.py scan   : minimal N1(ell1) on a grid of ell1 (VERIFIED table; each row checked to N1+4000)
import sys
from flint import arb, ctx
ctx.prec = 120
PI = arb.pi(); LMAX = arb(4).log()
def checks(ell1, N):
    out = []
    N = arb(N); delta = 1/(8*N)
    wb = 2*(-N*ell1).exp()                       # |w| <= 2 |c|^{-N}
    eps_w = (arb('1.1')*wb/N)**2 + arb('1.1')*wb/N**2   # |xi|^2 + |Li2(w)|/N^2
    CR = PI**2/6 + arb('1.1')*wb*(1 + 30*N)       # crude N^2 |R_mu| (|x - x_mu| <= 15)
    for s in (1, 2):
        tmax = PI*s/(N*ell1); th = tmax.atan(); cs = th.cos()
        out.append(('theta<pi/4 s=%d' % s, PI/4 - th))
        out.append(('quad coeff s=%d' % s, (th + PI/4).cos()))
        T = ell1**2/4 - PI**2*s*s/(4*N**2) + PI**2*cs/(6*N**2) - eps_w
        Tp = ell1**2/4 + PI**2*cs/(6*N**2) - eps_w if s == 2 else None
        WDneg = 2*delta*ell1 + PI**2/(3*N**2) + 2*CR/N**2
        out.append(('(a) D>=0 s=%d' % s, (2*PI**2*s*s*cs - CR)/N**2))
        out.append(('(a) D<0 s=%d' % s, T - WDneg))
        D = T - PI**2/(6*N**2) - 2*delta*ell1 - arb('1e-6')
        out.append(('(b) D>0 s=%d' % s, D))
        Lmu = (LMAX**2 + (LMAX*tmax + 2*PI/N)**2).sqrt()
        Delta = Lmu/2 + arb('1.1')*wb/N + 2*delta
        Rey = ell1/4 - arb('1e-7')
        cT = 2*Delta**2/((2*N*Rey).exp() - 1)
        out.append(('(b) quad s=%d' % s, D - cT))
        out.append(('(b) far s=%d' % s, D/4 - CR/N**2))
        out.append(('(c) s=%d' % s, T - 2*delta*ell1 - PI**2/(3*N**2)))
        Hh = delta*(ell1 + arb('0.0837')) + 2*delta/N*(1 + (1/(arb('1.8')*delta)).log())
        out.append(('head s=%d' % s, T - Hh))
        if s == 2:
            out.append(("(a') D>=0", (4*PI**2*cs - CR)/N**2))
            out.append(("(a') D<0", Tp - WDneg))
            Dp = ell1**2/4 - 2*delta*ell1 - arb('1e-6')
            Lp = LMAX/cs; Dl = Lp/2 + arb('1.1')*wb/N + 2*delta
            out.append(("(b') quad", Dp - 2*Dl**2/((2*N*Rey).exp() - 1)))
            out.append(("(b') far", Dp/4 - CR/N**2))
    out.append(('(c) lin coeff', 3*PI*(PI/8).sin() - LMAX*(PI/8).cos()))
    out.append(('Lemma W', N*ell1 - 3))
    return out
def ok(ell1, N):
    return all(bool(v > 0) for _, v in checks(ell1, N))
if __name__ == '__main__':
    if sys.argv[1] == 'scan':
        for l1s in ('0.693147', '0.6', '0.5', '0.4', '0.3', '0.2', '0.12', '0.1', '0.05', '0.02'):
            l1 = arb(l1s); N = 3
            while not ok(l1, N): N += 1
            # confirm on a window above N1 (monotone in N in the regime; VERIFIED, not proved, for the table)
            bad = [M for M in range(N, N + 4000, 7) if not ok(l1, M)]
            print('ell1=%s  N1=%d  N1*ell1=%.2f  window-check %s' % (l1s, N, N*float(l1s), 'OK' if not bad else 'FAIL at %s' % bad[:3]), flush=True)
        sys.exit(0)
    l1 = arb(2).log() if sys.argv[1] == 'log2' else arb(sys.argv[1])
    N1, N2 = int(sys.argv[2]), int(sys.argv[3])
    worst = {}
    for N in range(N1, N2 + 1):
        for k, v in checks(l1, N):
            if not bool(v > 0):
                print('LANDSCAPE FAILED at N=%d: %s = %s' % (N, k, v.str(5)), flush=True); sys.exit(1)
            if k not in worst or bool(v < worst[k][0]): worst[k] = (v, N)
    for k in worst: print('  %-18s min %s at N=%d' % (k, worst[k][0].str(4, radius=False), worst[k][1]))
    print('LANDSCAPE PASSED ell1=%s, %d<=N<=%d' % (sys.argv[1], N1, N2), flush=True)
