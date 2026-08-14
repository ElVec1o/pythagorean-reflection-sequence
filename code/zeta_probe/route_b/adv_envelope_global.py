#!/usr/bin/env python3
"""
Global envelope sweep: confirm on-shell |T2|/sqrt(tau) never exceeds ~0.0538 anywhere
in (0,0.3], i.e. the peak at tau~0.224 is the GLOBAL sup and the small-tau envelope
decreases monotonically toward sqrt2/36=0.0393. Scan many small-tau windows, each
densely (resolving the oscillation), report per-window envelope max.
"""
import mpmath as mp
from adv_verify import T2_direct

def window_max(lo, hi, npts, dps):
    mp.mp.dps=dps
    m=mp.mpf(0); arg=None
    for j in range(npts):
        tau=lo+(hi-lo)*mp.mpf(j)/(npts-1)
        r=abs(T2_direct(tau))/mp.sqrt(tau)
        if r>m: m=r; arg=tau
    return m,arg

if __name__=="__main__":
    sq2_36=mp.sqrt(2)/36
    print(f"sqrt2/36 = {mp.nstr(sq2_36,8)}; global moderate peak ~ 0.05384 at tau~0.224")
    print("="*80)
    # windows covering small tau down to 1e-5, each ~1 decade-fraction with dense pts
    wins = [
        (mp.mpf('0.05'),  mp.mpf('0.10'),  800, 70),
        (mp.mpf('0.02'),  mp.mpf('0.05'),  1500, 80),
        (mp.mpf('0.008'), mp.mpf('0.02'),  2500, 95),
        (mp.mpf('0.003'), mp.mpf('0.008'), 3500, 105),
        (mp.mpf('0.001'), mp.mpf('0.003'), 4000, 120),
        (mp.mpf('0.0004'),mp.mpf('0.001'), 4000, 140),
        (mp.mpf('0.0001'),mp.mpf('0.0004'),4500, 160),
    ]
    gmax=mp.mpf(0); garg=None
    for lo,hi,n,dps in wins:
        m,arg=window_max(lo,hi,n,dps)
        if m>gmax: gmax=m; garg=arg
        flag = "  <-- exceeds 0.0538!" if m>mp.mpf('0.0539') else ""
        print(f"  tau in [{float(lo):.5f},{float(hi):.5f}]: env max = {mp.nstr(m,7)} at tau={mp.nstr(arg,6)}{flag}")
    print("="*80)
    print(f"max small-tau envelope over [1e-4,0.1] = {mp.nstr(gmax,7)} at tau={mp.nstr(garg,6)}")
    print(f"Stays below moderate peak 0.05384? {'YES' if gmax<mp.mpf('0.05385') else 'NO'}")
    print(f"Stays below 0.06 bound? {'YES' if gmax<mp.mpf('0.06') else 'NO'}")
