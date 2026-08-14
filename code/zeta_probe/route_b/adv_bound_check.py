#!/usr/bin/env python3
"""
ADVERSARIAL check of the central numeric claim:
   |T2| <= 0.06 sqrt(tau)  at tau in {0.02, 0.005, 0.001, 0.0002}
and a dense scan of sup_w |T2|/sqrt(tau).

Catastrophic cancellation: at small tau the alternating sum has terms ~1e15 but
the result is ~1e-4. Need dps >= 120 for tau <= 1e-3. We verify T2_altsum against
T2_direct (bulk) at each tau as an internal consistency check.
"""
import mpmath as mp
from adv_verify import T2_direct, T2_altsum, B_int

def check(tau, dps):
    mp.mp.dps = dps
    tau = mp.mpf(tau)
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    td = T2_direct(tau)
    ta, N = T2_altsum(tau)
    sq = mp.sqrt(tau)
    ratio = abs(td)/sq
    bound = mp.mpf('0.06')*sq
    return dict(tau=float(tau), W=float(W), T2=td, absT2=abs(td),
                sq=sq, ratio=float(ratio), bound=bound,
                ok=abs(td) <= bound, diff=abs(td-ta), N=N)

if __name__ == "__main__":
    print("="*92)
    print("CLAIM: |T2| <= 0.06 sqrt(tau) at the four requested tau")
    print("="*92)
    cfg = [('0.02', 80), ('0.005', 100), ('0.001', 140), ('0.0002', 160)]
    for t, dps in cfg:
        r = check(t, dps)
        print(f"tau={r['tau']:9.5f} (dps={dps})  |T2|={mp.nstr(r['absT2'],6):>14}  "
              f"bound=0.06*sqrt={mp.nstr(r['bound'],6):>12}  ratio |T2|/sqrt={r['ratio']:.6f}  "
              f"{'OK' if r['ok'] else 'FAIL'}   internal|direct-altsum|={mp.nstr(r['diff'],2)}")

    print("\n" + "="*92)
    print("DENSE SCAN: sup over tau of |T2|/sqrt(tau) (single phase, q=e^{-tau})")
    print("="*92)
    # NOTE: at fixed tau, w is determined (w=sqrt(2/tau)); there is no free phase here.
    # The 'phase sweep' the colleague mentions varies w INDEPENDENTLY of tau. We test BOTH:
    # (A) the on-shell w=sqrt(2/tau) scan:
    mp.mp.dps = 120
    taus = [mp.mpf(10)**(mp.mpf(e)/4) for e in range(-16, -4)]  # 1e-4 .. ~3e-2
    extra = ['0.05','0.1','0.15','0.2','0.25','0.3']
    taus += [mp.mpf(x) for x in extra]
    sup = mp.mpf(0); argsup=None
    for tau in sorted(set(taus)):
        td = T2_direct(tau)
        r = abs(td)/mp.sqrt(tau)
        if r > sup: sup=r; argsup=float(tau)
        print(f"  tau={float(tau):10.6f}  |T2|/sqrt(tau)={mp.nstr(r,8)}")
    print(f"\n  on-shell sup |T2|/sqrt(tau) = {mp.nstr(sup,8)}  at tau={argsup}")
