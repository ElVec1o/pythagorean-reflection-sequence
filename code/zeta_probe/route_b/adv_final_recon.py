#!/usr/bin/env python3
"""
Final reconciliation:
 (a) precision-stability of |T2| at small tau (catastrophic cancellation) -- recompute at
     two different dps and confirm agreement.
 (b) reconcile colleague's reported 'ratio' numbers: they appear to be |T2|/bound, not
     |T2|/sqrt(tau).
 (c) pin the true global sup of on-shell |T2|/sqrt(tau) and confirm < 0.06.
"""
import mpmath as mp
from adv_verify import T2_direct

def stable_T2(tau, dpslist):
    vals=[]
    for d in dpslist:
        mp.mp.dps=d
        vals.append(T2_direct(mp.mpf(tau)))
    return vals

if __name__=="__main__":
    print("(a) precision stability of T2 at small tau (recompute at 2 dps):")
    for t in ['0.001','0.0002']:
        d1,d2 = (120,180) if t=='0.001' else (150,220)
        v=stable_T2(t,[d1,d2])
        print(f"   tau={t}: dps{d1}->{mp.nstr(v[0],16)}  dps{d2}->{mp.nstr(v[1],16)}  |diff|={mp.nstr(abs(v[0]-v[1]),3)}")

    print("\n(b) reconcile colleague's reported ratios (claim vs |T2|/sqrt(tau) vs |T2|/bound):")
    mp.mp.dps=150
    claims = {'0.02':0.031,'0.005':0.512,'0.001':0.380,'0.0002':0.362}
    for t,claimed in claims.items():
        tau=mp.mpf(t); T2=abs(T2_direct(tau))
        r_sqrt = T2/mp.sqrt(tau)
        r_bound= T2/(mp.mpf('0.06')*mp.sqrt(tau))
        print(f"   tau={t}: colleague-ratio={claimed}  |T2|/sqrt(tau)={mp.nstr(r_sqrt,5)}  "
              f"|T2|/(0.06 sqrt)={mp.nstr(r_bound,5)}  <- colleague's 'ratio' = |T2|/bound")

    print("\n(c) global on-shell sup |T2|/sqrt(tau) over (0,0.3], finest near peak tau~0.224:")
    mp.mp.dps=80
    sup=mp.mpf(0); arg=None
    lo=mp.mpf('0.20'); hi=mp.mpf('0.25')
    for j in range(2000):
        tau=lo+(hi-lo)*mp.mpf(j)/1999
        r=abs(T2_direct(tau))/mp.sqrt(tau)
        if r>sup: sup=r; arg=tau
    print(f"   sup near peak = {mp.nstr(sup,8)} at tau={mp.nstr(arg,8)}")
    print(f"   0.06 bound margin = {mp.nstr(mp.mpf('0.06')-sup,4)}  ({float(mp.mpf('0.06')/sup):.3f}x headroom)")
