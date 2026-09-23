#!/usr/bin/env python3
"""Summarize wt_growth runs: first deviation depth n_T, deficits, ratios, rate
extrapolation, and rational/algebraic/P-recurrence exclusions (guess.py).
Small arithmetic only (sequences of <= 60 integers)."""
import sys, glob, math
sys.path.insert(0, '.')
import guess

U = [int(l) for l in open('univ43.txt')]

def load(fn):
    return [int(l.split()[1]) if len(l.split())>1 else int(l) for l in open(fn) if not l.startswith('#') and l.strip()]

for fn in sys.argv[1:]:
    w = load(fn)
    nT = next((n for n in range(min(len(w), len(U))) if w[n] != U[n]), None)
    print(f"=== {fn}: {len(w)} terms (d<= {len(w)-1}), first deviation n_T = {nT}")
    print("   tail:", w[-4:])
    r = [w[n] / w[n - 1] for n in range(1, len(w))]
    r2 = [math.sqrt(w[n] / w[n - 2]) for n in range(2, len(w))]
    print("   last ratios u_n/u_{n-1}:", [round(x, 5) for x in r[-6:]])
    print("   last sqrt(u_n/u_{n-2}):", [round(x, 5) for x in r2[-6:]])
    # linear-in-1/n extrapolation of the 2-step ratio on the last 8 points
    xs = [1.0 / n for n in range(len(w) - 8, len(w))]
    ys = r2[-8:]
    mx = sum(xs) / 8; my = sum(ys) / 8
    b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    print(f"   rate extrapolation (a + b/n fit, last 8): beta_T ~ {my - b * mx:.4f}  (slope {b:.3f})")
    m = min(len(w), len(U))
    if nT is not None:
        dfc = [U[n] - w[n] for n in range(nT, m)]
        print("   deficits U-W:", dfc)
        print("   deficit/U:", [f"{(U[n]-w[n])/U[n]:.3f}" for n in range(nT, m)][-6:])
    dmax = -1
    for d in range(0, len(w)):
        rr = guess.rational_excluded(w, d, d)
        if rr is None: break
        if rr: dmax = d
        else:
            print(f"   rational type ({d},{d}) NOT excluded"); break
    alg = []
    for k in range(1, 5):
        mm = -1
        for mdeg in range(0, 40):
            rr = guess.algebraic_excluded(w, k, mdeg)
            if rr is None: break
            if rr: mm = mdeg
            else: break
        alg.append((k, mm))
    pr = []
    for o in range(1, 8):
        mm = -1
        for mdeg in range(0, 40):
            rr = guess.dfinite_excluded(w, o, mdeg)
            if rr is None: break
            if rr: mm = mdeg
            else: break
        pr.append((o, mm))
    print(f"   EXCLUDED: rational (d,d) d<={dmax}; algebraic (deg,deg_x<=):{alg}; P-rec (order,deg<=):{pr}")
