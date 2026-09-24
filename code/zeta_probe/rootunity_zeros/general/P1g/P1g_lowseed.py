# P1g_lowseed.py -- RIGOROUS (Arb): low-seed certificates for Z^+ and Z^- (P1g Prop. L) and the omega-margin in the
# single-saddle regime.  For seed p/q, side d>0, pieces d in [e_{i}, e_{i+1}] (geometric, e_i = r 2^{i-NP}, first piece [0, e_1]):
#   B_s (s=+-1) from P1g_cert.certify_pm, |S^s| lower,  c^s_seed = (1-B_s) sqrt(pi/(2 Aup)) |S^s|,  kappa_seed = q max(0,-Re F0),
#   omega in S^-/(u S^+) * (1+D(B_-))/(1+D(B_+))  (D(b) = complex square of half-width b), margins |G_i| of P1g Def. G.
# Prints one line per piece; 'RPRIME' = largest edge up to which every piece has B_+-,<1 and certified margin > MREQ.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1g_lowseed.py p q r eta V0 kappa NP MREQ
import sys
sys.path.insert(0, '..')
from flint import arb, acb
from dround import fdn, fup
from P1g_cert import certify_pm, PI, alo, aup
from P1g_seeds import Gfactors
from P1e_cert import e
p, q, r = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
eta, V0, ka, NP, MREQ = sys.argv[4], sys.argv[5], sys.argv[6], int(sys.argv[7]), arb(sys.argv[8])
rows = certify_pm(p, q, r, 60, eta, V0, ka, NP)
rprime = 0.0; ok = True; allB = True
for (dlo, dhi, Sp, Sm, Bp, Bm, u, x, Aup, F0) in rows:
    z = e(x)
    line = 'CERTPM %d/%d d in [%.4e,%.4e]: B+<=%s B-<=%s |S+|>=%s |S-|>=%s' % (p, q, dlo, dhi, fup(Bp, 3), fup(Bm, 3), fdn(alo(Sp), 4), fdn(alo(Sm), 4))
    cs = [(1 - arb(B.upper()))*arb((PI/(2*Aup)).sqrt().lower())*alo(S) for B, S in ((Bp, Sp), (Bm, Sm))]
    kap = q*(-F0.real).max(arb(0))
    line += ' c+>=%s c->=%s kappa<=%s' % (fdn(cs[0], 4), fdn(cs[1], 4), fup(arb(kap.upper()), 3))
    if not (bool(Bp < 1) and bool(Bm < 1)): allB = False
    if bool(Bp < 1) and bool(Bm < 1):
        th = lambda B: acb(arb(0, B.upper()), arb(0, B.upper()))
        om = Sm/(u*Sp)*(1 + th(Bm))/(1 + th(Bp))
        t1 = -(1 + om)/2
        G = Gfactors(z, t1, e(x/2))
        mg = alo(G[0])
        for g in G[1:]: mg = mg.min(alo(g))
        line += ' margin>=%s |omega|<=%s' % (fdn(mg, 4), fup(aup(om), 4))
        if ok and bool(mg > MREQ): rprime = dhi
        else: ok = False
    else: ok = False
    print(line, flush=True)
print('SEED %d/%d r=%g: all pieces B+-<1: %s ; RPRIME=%.6g (margin > %s on (0,RPRIME])' % (p, q, r, allB, rprime, MREQ.str(3)))
