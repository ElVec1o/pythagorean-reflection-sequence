#!/usr/bin/env python3
"""
TASK A driver: T2 two ways at tau in {0.3,0.2,0.1}.
Way 1 (direct) vs Way 2 (Abel-Plana bulk integral with EXACT B).

The integrand -Im psi(iy)/sinh(pi y) is convergent & oscillatory up to ~ the saddle
y*=W/2, then DIVERGES because Re B_{iy} -> -inf makes g_{iy}=1-e^{-B_iy} ~ e^{|Re B|}.
So we integrate the BULK panel-by-panel (fixed Gauss-Legendre per panel; no adaptive
blow-up) and report the partial integral vs the truncation point ymax, comparing to
the true T2 to see how close the convergent bulk gets and where the optimal cut is.
"""
import mpmath as mp
from abelplana_verify import integrand, S1_bulk, B_exact

mp.mp.dps = 50

def T2_direct(tau):
    q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    S1 = S1_bulk(q)
    return S1 - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W)), w, W

# fixed Gauss-Legendre on a panel via mpmath's non-adaptive quadgl
_GL = mp.calculus.quadrature.GaussLegendre(mp.mp)
def gl_panel(f, a, b, deg=6):
    # non-adaptive fixed-degree Gauss-Legendre (deg sets ~3*2^deg nodes)
    return mp.quadgl(f, [a, b], maxdegree=deg)

def bulk_partial(tau, ymax, panel=mp.mpf('0.25'), order=20):
    """Integrate integrand over (0,ymax) in fixed panels of width 'panel'."""
    q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    f = lambda y: integrand(y, W, tau)
    total = mp.mpf(0); y = mp.mpf(0)
    partials = {}
    targets = set(int(round(t/ float(panel)))*float(panel) for t in ymax) if hasattr(ymax,'__iter__') else None
    ymax_max = max(ymax) if hasattr(ymax,'__iter__') else ymax
    record_at = sorted(ymax) if hasattr(ymax,'__iter__') else [ymax]
    ri = 0
    while y < ymax_max - mp.mpf('1e-12'):
        b = min(y+panel, mp.mpf(ymax_max))
        total += gl_panel(f, y, b)
        y = b
        while ri < len(record_at) and y >= mp.mpf(record_at[ri]) - mp.mpf('1e-9'):
            partials[record_at[ri]] = total
            ri += 1
    return partials

if __name__ == "__main__":
    for tau in [mp.mpf('0.3'), mp.mpf('0.2'), mp.mpf('0.1')]:
        T2t, w, W = T2_direct(tau)
        ystar = W/2
        print(f"\n===== tau={float(tau)} : w={float(w):.5f} W={float(W):.5f} y*=W/2={float(ystar):.5f} =====")
        print(f"  T2_direct (Way 1) = {mp.nstr(T2t, 16)}")
        rec = [1,2,3,4,5,6,7,8]
        parts = bulk_partial(tau, rec, panel=mp.mpf('0.2'), order=20)
        print("   ymax    AP bulk partial (Way 2)        diff to T2_direct")
        best = None
        for ym in rec:
            if ym in parts:
                I = parts[ym]; d = abs(I-T2t)
                if best is None or d < best[1]: best = (ym, d, I)
                print(f"   {ym:>4}   {mp.nstr(I,16):>24}   {mp.nstr(d,5):>12}")
        if best:
            print(f"  >>> closest at ymax={best[0]}: AP={mp.nstr(best[2],14)}  |AP-T2|={mp.nstr(best[1],5)}"
                  f"  rel={mp.nstr(best[1]/abs(T2t),4)}  digits={float(-mp.log10(best[1]/abs(T2t))):.2f}")
