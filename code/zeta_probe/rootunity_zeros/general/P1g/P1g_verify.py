# P1g_verify.py -- VERIFIED (floating; not part of any proof): end-to-end checks of the twisted single-saddle model.
# For x = a/N near a low seed p/q (d>0), compares the direct omega_N (exact finite formula, numpy, P1g_scope.data) with the
# certified model enclosure S^-/(u S^+) of P1g_cert.certify_pm on the piece containing d, and |Z^s_N|/|C S^s| - 1.
import sys, numpy as np
sys.path.insert(0, '..')
from math import gcd
from P1g_scope import data
from P1g_cert import certify_pm
from flint import acb
for (p, q, r, eta, V0, Ns) in [(1, 3, 0.004, '0.087', '0.102817', (400, 1000, 2500)), (3, 4, 0.0007, '0.0257', '0.0288367', (2000, 3001)),
                               (2, 5, 0.003, '0.102', '0.120417', (500, 1500))]:
    rows = certify_pm(p, q, r, 60, eta, V0, '3', 8)
    for N in Ns:
        a = (p*N)//q + 1
        while gcd(a, N) != 1: a += 1
        d = a/N - p/q
        if d > r: continue
        z, u, Z, Zp, Zm = data(a, N)
        om = Zm/(u*Zp)
        for (dlo, dhi, Sp, Sm, Bp, Bm, uu, x, Aup, F0) in rows:
            if dlo <= d <= dhi:
                mod = Sm/(uu*Sp); mc = complex(float(mod.real.mid()), float(mod.imag.mid()))
                print('%d/%d at %d/%d d=%.2e: omega_direct=%s  omega_model(mid)=%s  |diff|=%.2e  (certified B+=%.3g B-=%.3g)' % (
                    p, q, a, N, d, np.round(om, 6), np.round(mc, 6), abs(om - mc), float(Bp.mid()), float(Bm.mid())), flush=True)
# --- check of the refined direct formula (P1g_caseA) against the direct value at exact x = a/N (sign conventions) ---
from fractions import Fraction as Fr
import P1g_caseA as CA
from flint import arb
for (a, N) in [(71, 301), (97, 400), (133, 401), (180, 499)]:
    z, u, Z, Zp, Zm = data(a, N)
    res, why = CA.evaluate(Fr(a, N), Fr(a, N), 40, arb(0), arb(0))
    om = Zm/(u*Zp)
    # recompute P^s with the module's internals is not exposed; compare |Z^pm| lower bound and omega bound instead
    print('caseA check %d/%d: direct |Z+|=%.5f |Z-|=%.5f omega=%s ; certified min|Z^pm|>=%s, |omega|<=%s (%s)' % (
        a, N, abs(Zp), abs(Zm), np.round(om, 5), res[0].str(5) if res else None, res[2].str(5) if res else None, why))
