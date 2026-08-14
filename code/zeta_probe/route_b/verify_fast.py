"""Fast consolidated verification of colleague's (A) claims. Unbuffered, coarser grids."""
import mpmath as mp, sympy as sp, sys
mp.mp.dps = 30
def pr(*a): print(*a); sys.stdout.flush()

def Dp(p, W, K=400):
    s = mp.mpf(0)
    for k in range(0, K+1):
        kp = (mp.mpf(0) if p > 0 else mp.mpf(1)) if k == 0 else mp.mpf(k)**p
        t = (-1)**k * kp * W**(2*k) / mp.factorial(2*k)
        s += t
        if k > float(W)+8 and abs(t) < mp.mpf('1e-32')*max(abs(s), mp.mpf(1)): break
    return s
def supDp(p, w, N=400):
    best = mp.mpf(0)
    for ii in range(N+1):
        Wv = w*mp.mpf(ii)/N
        v = (mp.mpf(0) if p > 0 else mp.mpf(1)) if Wv == 0 else abs(Dp(p, Wv))
        if v > best: best = v
    return best

pr("="*68); pr("(2) SHARP sup_[0,w]|D_p| <= (w/2)^p e^{p^2/(2w)}, worst ratio <=1 ?"); pr("="*68)
worst = mp.mpf(0); wat = None
for w in [mp.mpf(x) for x in ['1','3','7','13','21','33','55','100','200']]:
    for p in range(0, 41):
        lhs = supDp(p, w); rhs = (w/2)**p * mp.e**(mp.mpf(p*p)/(2*w))
        r = lhs/rhs
        if r > worst: worst = r; wat = (float(w), p)
pr(f"  worst LHS/RHS = {float(worst):.6f} at (w,p)={wat}")

pr(""); pr("  deep regime p>>w (w=1,1.5,2,3, p<=40):")
wd = mp.mpf(0); wdat = None
for w in [mp.mpf(x) for x in ['1','1.5','2','3']]:
    for p in range(0, 41):
        lhs = supDp(p, w); rhs = (w/2)**p * mp.e**(mp.mpf(p*p)/(2*w))
        r = lhs/rhs
        if r > wd: wd = r; wdat = (float(w), p)
pr(f"  worst = {float(wd):.6f} at (w,p)={wdat}")

pr(""); pr("  empirical alpha (log(sup/(w/2)^p) ~ alpha p^2/(2w)), p=30:")
for w in [mp.mpf('20'), mp.mpf('40'), mp.mpf('80')]:
    lhs = supDp(30, w); a = mp.log(lhs/(w/2)**30)/(mp.mpf(900)/(2*w))
    pr(f"   w={float(w):.0f}: alpha={float(a):.4f}")

pr(""); pr("="*68); pr("(5) Touchard 2^-p T_p(w) <= colleague sharp (w/2)^p e^{p^2/(2w)} ?")
pr("    (= Poisson moment E[N^p] <= w^p e^{p^2/(2w)})"); pr("="*68)
def Tp(p, w): return sum(int(sp.functions.combinatorial.numbers.stirling(p, r, kind=2))*w**r for r in range(p+1))
allok = True; firstviol = None
for w in [mp.mpf('5'), mp.mpf('20'), mp.mpf('80')]:
    for p in range(0, 40):
        if Tp(p, w) > w**p * mp.e**(mp.mpf(p*p)/(2*w))*(1+mp.mpf('1e-20')):
            allok = False; firstviol = (float(w), p); break
pr(f"  E[N^p] <= w^p e^(p^2/2w): {'HOLDS' if allok else 'FAILS at '+str(firstviol)}")

pr(""); pr("  And: does Touchard 2^-p T_p(w) DOMINATE true sup_[0,w]|D_p|? (rigorous bound)")
domok = True
for w in [mp.mpf('20')]:
    for p in range(0, 25):
        s = supDp(p, w); tb = Tp(p, w)/mp.mpf(2)**p
        if tb < s*(1-mp.mpf('1e-9')): domok = False; pr(f"   VIOL p={p}")
pr(f"  2^-p T_p(w) >= sup_[0,w]|D_p| (w=20,p<25): {'HOLDS' if domok else 'FAILS'}")
