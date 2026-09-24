# P1e_lowseed.py -- low-height seeds for the middle-arc theorem (P1e_lemma.tex, Theorem M): rigorous Theorem-5-type certificate
# (P1e_cert.certify, with the sharpened outer contour) at seed p/q, side d>0, with contour height eta <= eta_region (so that the
# Delta-hypothesis follows from the hazard lemma with y = 0.5) and n2 = 60.  Tries radii from RMAX downwards; prints the first success,
# plus the constants c_seed = (1-B) sqrt(pi/(2 A_up)) |S_amp|_lo and kappa_seed = q * max(0, -Re F(t0)) needed for the induction.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1e_lowseed.py p q eta RMIN [RSTART]
import sys, time
from math import log, pi
from flint import arb, acb
from dround import fdn, fup
from P1e_cert import certify, Fail, setup_x, find_t0, e, PI, I, aup, li2_ball
p, q, eta = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]); RMIN = float(sys.argv[4]); RSTART = float(sys.argv[5]) if len(sys.argv) > 5 else 1.0
_, _, U, _ = setup_x(p, q, 0.0, 1e-9, q)
t0 = find_t0(q, U, rad0=1e-10); im0 = float(t0.imag.mid())
T0 = time.time()
for r in (0.0083, 0.006, 0.004, 0.003, 0.002, 0.0015, 0.001, 7e-4, 5e-4, 3e-4, 2e-4, 1e-4, 5e-5, 2e-5, 1e-5):
    if r < RMIN: break
    if r > RSTART: continue
    for ka, V0f in ((3.0, 0.85), (4.0, 0.6)):
        V0 = V0f*(eta - im0)/0.72
        try:
            B, Ns, Bs, rows = certify(p, q, r, 60, '%.6g' % eta, '%.6g' % V0, ka, 6, verbose=False, KSEG=32, VQ='0.4', NPC=40)
        except Fail as ex:
            print('  r=%g ka=%g: FAIL %s [%.0fs]' % (r, ka, ex, time.time() - T0), flush=True); continue
        if bool(B < 0.9):
            # induction constants over the whole disc (0, r]
            _, u, Ua, _ = setup_x(p, q, 0.0, r, 60)
            tb = find_t0(q, Ua, rad0=1e-6, grow=False)
            W0 = Ua*e(-q*tb); F2 = PI*I*(1 + W0)/(1 - W0); Aup = arb(F2.abs_upper())/2
            F0 = PI*I*tb*tb/2 + li2_ball(W0)/(2*PI*I*q*q)
            kap = q*(-F0.real).max(arb(0))
            import re
            Svals = [re.search(r'\|S\|>=([0-9.e+-]+)', rw).group(1) for rw in rows]
            Smin_s = min(Svals, key=float)
            # Smin is parsed from rows printed by fdn (directed DOWN), so it is a rigorous lower bound; all arithmetic below is Arb.
            Sm = arb(Smin_s)
            cseed = (1 - arb(B.upper()))*arb((PI/(2*Aup)).sqrt().lower())*Sm
            print('CERT %d/%d d>0 r=%g eta=%g n2=60 V0=%.6g kappa=%g: B<=%s N*>=%s  ReF0 in %s  kappa_seed<=%s  sqrt(pi/2A)>=%s  min|S_amp|>=%s  c_seed>=%s' % (
                p, q, r, eta, V0, ka, fup(B, 4), fdn(Ns, 3), F0.real.str(4), fup(arb(kap.upper()), 3),
                fdn((PI/(2*Aup)).sqrt(), 4), fdn(Sm, 4), fdn(cseed, 4)), flush=True)
            sys.exit(0)
        print('  r=%g ka=%g: B=%s' % (r, ka, B.str(3, radius=False)), flush=True)
print('NONE %d/%d eta=%g' % (p, q, eta))
