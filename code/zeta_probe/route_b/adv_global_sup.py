#!/usr/bin/env python3
"""
Global on-shell sup of |T2|/sqrt(tau) over tau in (0, 0.3].
We do a dense scan, then refine around local maxima, to find the true sup and
check it stays below 0.06. The on-shell ratio oscillates rapidly at small tau
(phase w=sqrt(2/tau)), so we scan finely.
"""
import mpmath as mp
from adv_verify import T2_direct

def scan(lo, hi, npts, dps=80):
    mp.mp.dps = dps
    sup = mp.mpf(0); arg=None
    vals=[]
    for j in range(npts):
        tau = lo + (hi-lo)*mp.mpf(j)/(npts-1)
        r = abs(T2_direct(tau))/mp.sqrt(tau)
        vals.append((tau, r))
        if r>sup: sup=r; arg=tau
    return sup, arg, vals

if __name__ == "__main__":
    # Coarse scan over the whole moderate range with enough density to catch oscillation.
    # Oscillation period in tau near tau0: w=sqrt(2/tau), dw/dtau = -sqrt(2)/(2 tau^{3/2}).
    # One cos-period is dw=2pi => dtau ~ 2pi * 2 tau^{3/2}/sqrt(2). At tau=0.25 that's ~ 2.2,
    # so the oscillation is SLOW (under-one-period) near tau=0.25; finer needed at small tau.
    print("Region A: tau in [0.1, 0.3] (slow oscillation), 400 pts")
    supA, argA, _ = scan(mp.mpf('0.1'), mp.mpf('0.3'), 400, dps=70)
    print(f"  supA = {mp.nstr(supA,8)} at tau={mp.nstr(argA,8)}")

    print("Region B: tau in [0.02, 0.1], 1200 pts")
    supB, argB, _ = scan(mp.mpf('0.02'), mp.mpf('0.1'), 1200, dps=90)
    print(f"  supB = {mp.nstr(supB,8)} at tau={mp.nstr(argB,8)}")

    print("Region C: tau in [0.003, 0.02], 3000 pts (faster oscillation)")
    supC, argC, _ = scan(mp.mpf('0.003'), mp.mpf('0.02'), 3000, dps=110)
    print(f"  supC = {mp.nstr(supC,8)} at tau={mp.nstr(argC,8)}")

    g = max([supA, supB, supC])
    print(f"\n  GLOBAL on-shell sup over [0.003,0.3] ~ {mp.nstr(g,8)}")
    print(f"  0.06 bound holds? {'YES' if g < mp.mpf('0.06') else 'NO'}  (margin {mp.nstr(mp.mpf('0.06')-g,4)})")

    # refine around argA (the dominant peak near tau~0.22-0.25)
    print("\nRefine around dominant peak:")
    lo = argA - mp.mpf('0.01'); hi = argA + mp.mpf('0.01')
    supR, argR, _ = scan(lo, hi, 400, dps=70)
    print(f"  refined sup = {mp.nstr(supR,10)} at tau={mp.nstr(argR,10)}")
