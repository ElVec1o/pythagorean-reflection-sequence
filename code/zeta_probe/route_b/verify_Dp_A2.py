"""
Part 2: test the SHARP bound, the RIGOROUS family bound, and the J bound.
"""
import mpmath as mp
mp.mp.dps = 40

def Dp_series(p, W, K=600):
    s = mp.mpf(0)
    for k in range(0, K+1):
        kp = (mp.mpf(0) if p > 0 else mp.mpf(1)) if k == 0 else mp.mpf(k)**p
        t = (-1)**k * kp * W**(2*k) / mp.factorial(2*k)
        s += t
        if k > float(W)+10 and abs(t) < mp.mpf('1e-40')*max(abs(s), mp.mpf(1)):
            break
    return s

def supDp(p, w, N=1500):
    best = mp.mpf(0); arg = mp.mpf(0)
    for ii in range(N+1):
        Wv = w*mp.mpf(ii)/N
        v = (mp.mpf(0) if p > 0 else mp.mpf(1)) if Wv == 0 else abs(Dp_series(p, Wv))
        if v > best: best = v; arg = Wv
    return best, arg

# ---------- (2) SHARP bound  sup_[0,w]|D_p| <= (w/2)^p e^{p^2/(2w)} ----------
print("="*70)
print("(2) SHARP: sup_[0,w]|D_p| <= (w/2)^p e^{p^2/(2w)}  (claim: worst ratio <= 1)")
print("="*70)
worst = mp.mpf(0); worst_at = None
for w in [mp.mpf(x) for x in ['1','1.5','3','7','13','21','33','55','100','200']]:
    for p in range(0, 51):
        lhs, _ = supDp(p, w)
        rhs = (w/2)**p * mp.e**(mp.mpf(p*p)/(2*w))
        r = lhs/rhs
        if r > worst:
            worst = r; worst_at = (float(w), p, float(r))
print(f"  worst LHS/RHS over w in grid, p<=50 = {float(worst):.6f}  at (w,p)={worst_at}")

# deep regime p >> w
print("  deep regime p>>w (w in 1,1.5,2,3, p<=45):")
worstd = mp.mpf(0); worstd_at = None
for w in [mp.mpf(x) for x in ['1','1.5','2','3']]:
    for p in range(0, 46):
        lhs, _ = supDp(p, w)
        rhs = (w/2)**p * mp.e**(mp.mpf(p*p)/(2*w))
        r = lhs/rhs
        if r > worstd: worstd = r; worstd_at = (float(w), p, float(r))
print(f"  worst = {float(worstd):.6f}  at (w,p)={worstd_at}")

# pointwise version |D_p(W)| <= (W/2)^p e^{p^2/(2W)}
print()
print("  pointwise |D_p(W)| <= (W/2)^p e^{p^2/(2W)} (claim worst ~0.9912):")
worstp = mp.mpf(0); worstp_at = None
for Wi in range(1, 101):
    W = mp.mpf(Wi)/2
    for p in range(0, 51):
        lhs = abs(Dp_series(p, W))
        rhs = (W/2)**p * mp.e**(mp.mpf(p*p)/(2*W))
        r = lhs/rhs
        if r > worstp: worstp = r; worstp_at = (float(W), p, float(r))
print(f"  worst pointwise = {float(worstp):.6f} at (W,p)={worstp_at}")

# ---------- empirical alpha in log(sup/(w/2)^p) ~ alpha p^2/(2w) ----------
print()
print("  empirical alpha:  log(sup|D_p|/(w/2)^p) ~ alpha * p^2/(2w)")
for w in [mp.mpf('20'), mp.mpf('40'), mp.mpf('80')]:
    p = 30
    lhs, _ = supDp(p, w)
    val = mp.log(lhs/(w/2)**p)
    alpha = val / (mp.mpf(p*p)/(2*w))
    print(f"   w={float(w):.0f} p={p}: alpha = {float(alpha):.4f}")
