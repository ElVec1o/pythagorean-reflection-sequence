#!/usr/bin/env python3
"""
Independent verification of LEMMAS 1, 2, 3.

LEMMA 1: 0 <= phi(y) <= y^2/24 for all real y, phi(y)=log(sinh(y/2)/(y/2)).
  Lower: each product-term log(1+(y/2pik)^2) >= 0. (trivially true)
  Upper: log(1+u)<=u => phi(y) <= sum (y/2pik)^2 = (y^2/4pi^2) zeta(2) = y^2/24.
  CHECK: scan y, confirm 0 <= phi(y) <= y^2/24 and the ratio phi/(y^2/24)->1 as y->0.

LEMMA 2: B_i >= 0 and B_i <= (tau^2/24) sum_{x=0}^{i-1}[(2x+2)^2+(2x+1)^2].
  Lower: b(x)=phi((2x+2)t)+phi((2x+1)t)-phi(t); since phi increasing on [0,inf) and
         (2x+1)t >= t for x>=0, phi((2x+1)t)>=phi(t), and phi((2x+2)t)>=0, so b(x)>=0.
  Upper: drop -phi(t)<=0 and bound the two positive phi by L1.
  CHECK: B_i >= 0 (yes by construction), B_ub >= B_true, AND 1-e^{-B}<=B (g_i<=B_i).

LEMMA 3: tail sum_{i>N} a_i g_i < tail, N=2W. a_i=W^{2i}/(2i)!.
  g_i<1 so tail <= sum_{i>N} a_i. Ratio a_{i+1}/a_i = W^2/((2i+2)(2i+1)).
  At i>=N=2W: W^2/((2i+2)(2i+1)) <= W^2/((4W)(4W)) = 1/16 < 1, super-geometric.
  CHECK: numeric tail at N=2W at tau=0.001.
"""
import mpmath as mp

def phi(y):
    if y == 0: return mp.mpf(0)
    y = mp.mpf(y)
    return mp.log(mp.sinh(y/2)/(y/2))

if __name__ == "__main__":
    mp.mp.dps = 50
    print("="*80)
    print("LEMMA 1: 0 <= phi(y) <= y^2/24")
    print("="*80)
    worst_ratio = mp.mpf(0); worst_y=None
    viol_low=False; viol_high=False
    # scan y from tiny to large
    ys = [mp.mpf('1e-6')] + [mp.mpf(k)/10 for k in range(1,200)] + [mp.mpf(k) for k in range(20,400)]
    for y in ys:
        p = phi(y); ub = y**2/24
        if p < -mp.mpf('1e-40'): viol_low=True
        if p > ub + mp.mpf('1e-40'): viol_high=True; print(f"   UPPER VIOLATION at y={float(y)}: phi={p} > {ub}")
        r = p/ub
        if r > worst_ratio: worst_ratio=r; worst_y=y
    print(f"  lower bound 0<=phi violated? {viol_low}")
    print(f"  upper bound phi<=y^2/24 violated? {viol_high}")
    print(f"  max ratio phi/(y^2/24) = {mp.nstr(worst_ratio,12)} at y={float(worst_y)} (->1 as y->0)")
    # limit check
    print(f"  phi(1e-8)/((1e-8)^2/24) = {mp.nstr(phi(mp.mpf('1e-8'))/((mp.mpf('1e-8'))**2/24),12)}")

    print("\n" + "="*80)
    print("LEMMA 2: B_i bounds and g_i <= B_i")
    print("="*80)
    def b_int(x, tau): return phi((2*x+2)*tau)+phi((2*x+1)*tau)-phi(tau)
    def B_int(i, tau): return mp.fsum(b_int(x,tau) for x in range(i))
    for tau in [mp.mpf('0.3'), mp.mpf('0.05'), mp.mpf('0.005')]:
        print(f"  tau={float(tau)}:")
        bad_ub=False; bad_g=False; minmarg=mp.inf
        for i in range(1, 60):
            Btrue = B_int(i, tau)
            Bub = (tau**2/24)*mp.fsum((2*x+2)**2+(2*x+1)**2 for x in range(i))
            g = 1 - mp.e**(-Btrue)
            if Btrue < -mp.mpf('1e-40'): print(f"     B_{i} < 0 !!");
            if Bub < Btrue - mp.mpf('1e-30'): bad_ub=True; print(f"     UB FAIL at i={i}: Bub={Bub} < Btrue={Btrue}")
            if g > Btrue + mp.mpf('1e-30'): bad_g=True; print(f"     g>B FAIL at i={i}")
            marg = Bub/Btrue if Btrue>0 else mp.inf
            minmarg=min(minmarg,marg)
        print(f"     B_i>=0 OK, upper-bound fails? {bad_ub}, g_i<=B_i fails? {bad_g}; min(Bub/Btrue)={mp.nstr(minmarg,6)}")

    print("\n" + "="*80)
    print("LEMMA 3: factorial tail beyond N=2W")
    print("="*80)
    for tau in [mp.mpf('0.001'), mp.mpf('0.0002')]:
        w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
        N = int(mp.ceil(2*W))
        # tail bound sum_{i>N} a_i  (g_i<1)
        tail = mp.mpf(0)
        i = N+1
        while True:
            ai = W**(2*i)/mp.factorial(2*i)
            tail += ai
            if ai < mp.mpf('1e-200') and i>N+5: break
            i += 1
            if i > N+200: break
        print(f"  tau={float(tau)}: W={float(W):.3f}, N=2W={N}, tail(sum a_i, i>N) = {mp.nstr(tail,4)}  "
              f"(/sqrt(tau)={mp.nstr(tail/mp.sqrt(tau),4)})")
