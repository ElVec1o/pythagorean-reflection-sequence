"""
High-precision re-test of the SHARP bound  sup_[0,w]|D_p| <= (w/2)^p e^{p^2/(2w)}.
dps scaled with w to defeat catastrophic cancellation (terms ~ W^{2k}/(2k)! ~ e^{...w}).
We need dps > ~ (2/ln10) * w  roughly (since max term magnitude ~ e^{2 w} near W~2k).
Use dps = max(40, int(1.2*w) + 40).
"""
import mpmath as mp

def Dp(p, W, K):
    s = mp.mpf(0)
    for k in range(K+1):
        kp = (mp.mpf(0) if p > 0 else mp.mpf(1)) if k == 0 else mp.mpf(k)**p
        t = (-1)**k * kp * W**(2*k) / mp.factorial(2*k)
        s += t
        if k > float(W)+20 and abs(t) < mp.mpf('1e-30')*max(abs(s), mp.mpf(1)): break
    return s
def supDp(p, w, N):
    best = mp.mpf(0)
    K = int(2*float(w)) + 60
    for ii in range(N+1):
        Wv = w*mp.mpf(ii)/N
        v = (mp.mpf(0) if p > 0 else mp.mpf(1)) if Wv == 0 else abs(Dp(p, Wv, K))
        if v > best: best = v
    return best

print("HIGH-PRECISION: sup_[0,w]|D_p| <= (w/2)^p e^{p^2/(2w)} ?  (dps scaled with w)")
print(f"  {'w':>5} {'p':>4} {'sup/RHS':>12}")
worst = mp.mpf(0); wat = None
for wv in [1, 3, 7, 13, 21, 33, 55, 100, 200]:
    mp.mp.dps = max(40, int(1.3*wv) + 40)
    w = mp.mpf(wv)
    # sample p values (full 0..50 is expensive at high dps for large w); use representative set
    pset = [0, 1, 2, 4, 8, 12, 16, 20, 25, 30, 40, 50]
    N = 300 if wv >= 55 else 500
    rowworst = mp.mpf(0); rowp = None
    for p in pset:
        lhs = supDp(p, w, N)
        rhs = (w/2)**p * mp.e**(mp.mpf(p*p)/(2*w))
        r = lhs/rhs
        if r > rowworst: rowworst = r; rowp = p
        if r > worst: worst = r; wat = (wv, p)
    print(f"  {wv:>5} {rowp:>4} {float(rowworst):>12.5f}   <- worst p this w")
print(f"\n  OVERALL worst LHS/RHS = {float(worst):.6f} at (w,p)={wat}")
print(f"  => SHARP bound (C_D=1) {'HOLDS' if worst <= mp.mpf('1.0001') else 'VIOLATED'}")
