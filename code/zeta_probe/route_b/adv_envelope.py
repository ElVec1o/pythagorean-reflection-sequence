#!/usr/bin/env python3
"""
Envelope of |T2|/sqrt(tau) as tau->0, and verification of the asymptotic constant.

Two things:
(A) Confirm the small-tau envelope of |T2|/sqrt(tau) tends to sqrt(2)/36 = 0.0392837...
    by scanning each oscillation lobe at progressively smaller tau and taking the
    per-lobe max (envelope).
(B) Verify the SADDLE leading-coefficient claim B_{s*} = -i(sqrt2/36)sqrt(tau)+O(tau),
    s* = iW/2, B_{s*}=(tau^2/9)(iW/2)^3 + O(tau), independently.
"""
import mpmath as mp
from adv_verify import T2_direct, B_int

def envelope_max(tau_lo, tau_hi, npts, dps):
    """max of |T2|/sqrt(tau) over a tau-window (one or more oscillation lobes)."""
    mp.mp.dps = dps
    m = mp.mpf(0); arg=None
    for j in range(npts):
        tau = tau_lo + (tau_hi-tau_lo)*mp.mpf(j)/(npts-1)
        r = abs(T2_direct(tau))/mp.sqrt(tau)
        if r>m: m=r; arg=tau
    return m, arg

if __name__ == "__main__":
    print("="*80)
    print("(A) small-tau envelope of |T2|/sqrt(tau) -> sqrt(2)/36 ?")
    sq2_36 = mp.sqrt(2)/36
    print(f"    target sqrt(2)/36 = {mp.nstr(sq2_36,10)}")
    print("="*80)
    # Each window spans ~ a couple oscillation periods; density chosen to resolve them.
    # period in tau ~ 2pi*2 tau^{3/2}/sqrt2. At tau=1e-3 -> ~3e-4. At 1e-4 -> ~9e-6.
    windows = [
        (mp.mpf('0.004'), mp.mpf('0.006'), 800, 110),
        (mp.mpf('0.0009'), mp.mpf('0.0012'), 1500, 140),
        (mp.mpf('0.00018'), mp.mpf('0.00022'), 2500, 170),
        (mp.mpf('0.00004'), mp.mpf('0.00005'), 3000, 200),
    ]
    for lo, hi, n, dps in windows:
        m, arg = envelope_max(lo, hi, n, dps)
        cen = (lo+hi)/2
        print(f"  tau~{float(cen):.5g}: envelope max |T2|/sqrt(tau) = {mp.nstr(m,9)}  "
              f"(ratio to sqrt2/36 = {mp.nstr(m/sq2_36,7)})")

    print("\n" + "="*80)
    print("(B) saddle leading coeff: B_{s*}, s*=iW/2 (W on-shell), vs -i sqrt2/36 sqrt(tau)")
    print("="*80)
    # Use the EXACT analytic B at s*=iW/2 via colleague's continuation as one estimate,
    # but ALSO an independent check via the leading cubic (tau^2/9)(iW/2)^3.
    from abelplana_verify import B_exact
    for tau in [mp.mpf('0.02'), mp.mpf('0.005'), mp.mpf('0.001'), mp.mpf('0.0002')]:
        mp.mp.dps = 80
        w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
        sstar = mp.mpc(0,1)*W/2
        # leading cubic prediction
        B_cubic = (tau**2/9)*sstar**3
        pred = -mp.mpc(0,1)*sq2_36*mp.sqrt(tau)
        # exact analytic B at s* (colleague continuation)
        Bex,_ = B_exact(sstar, tau)
        print(f"  tau={float(tau):8.5f}: B_cubic={mp.nstr(B_cubic,8)}  "
              f"pred=-i*sqrt2/36*sqrt(tau)={mp.nstr(pred,8)}  "
              f"B_exact(s*)={mp.nstr(Bex,8)}")
        print(f"            |B_cubic - pred|={mp.nstr(abs(B_cubic-pred),3)}  "
              f"|B_exact - B_cubic|={mp.nstr(abs(Bex-B_cubic),3)}")
