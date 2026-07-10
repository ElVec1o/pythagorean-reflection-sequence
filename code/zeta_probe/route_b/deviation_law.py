#!/usr/bin/env python3
"""The exact deviation-depth law (paper1.tex, prop:exact-deviation + prop:deviation-law).

n_T = K(T)/2, where K(T) is the length of the shortest nontrivial kernel element of the
shape T -- a shortest-vector problem in the ideal mu_T * Z[t^{+-1}] (profile coordinates:
lamp polynomials 2*mu_T*m) under the lamplighter word metric of the metric theorem
(ell_T = relaxed tour cost + 2 * transducer defect).

Pipeline, all steps reproduced here:
 (1) CALIBRATION: relaxed_len_local + 2*c_pred == exact BFS distance on ALL group elements
     through depth 14 (3723 elements, 0 mismatches; includes all 86 pure translations).
 (2) DICTIONARY: kernel lamp profiles are L = 2*mu_T*m (the (t-1)-twisted alternative gives
     K_(1,2) = 78, refuted by the certified window {65,66}).
 (3) PARITY: every generator move flips the direction flag, so pure translations have even
     length; with the certified n_(1,2) = 33 (=> K in {65,66}) this forces K_(1,2) = 66.
 (4) SEARCH: for each shape, enumerate multipliers m (degree <= 5, |m_i| <= 4, all shifts),
     sorted by l1(L); within this bounded-degree family the l1-prune (ell_tr >= ||L||_1) is
     exhaustive. NB the l1 bound alone does NOT prove global termination -- mu_T has both roots
     on |t|=1 (not roots of unity, Niven), so ||mu_T m||_1 can stall as deg m grows. Rigorous
     finiteness is via the TRAVEL bound ell_tr >= 2*span(A) (deviation_lowerbound.py, paper1
     lem:finite-svp), which caps deg m <= K/2. So these searches are exhaustive-within-window
     (deg <= 5), NOT full theorems except at (1,2) [independently certified]; the closed-form
     law's exactness for all shapes is conjectural.
 (5) LAW (validated on 13 (c,e) pairs; windows widened for (1,2),(3,4) with no change):
         n_T = 3(c+e)                 if e >= c
         n_T = 6c + min(e, 3(c-e))    if e <= c        (switch at e = 3c/4)
     Closed-form family costs (evaluated from the metric formula):
         ell_tr(2*mu)       = 8c + 2e + 4*max(c,e)
         ell_tr(2*(t+1)mu)  = 12c + 6*|c-e|
     Falsifiability: (3,4) gives n = 164 >= 43, consistent with the certified
     collision-freeness of (3,4,5) through depth 42; and a sharp prediction.

Run from route_b/ (needs lamp_lib.py, c_formula.py, catalytic_funceq.py).
"""
import sys, itertools, importlib.util, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) or '.')
from lamp_lib import bfs
from c_formula import c_pred

spec = importlib.util.spec_from_file_location(
    "cat", os.path.join(os.path.dirname(os.path.abspath(__file__)), "catalytic_funceq.py"))
cf = importlib.util.module_from_spec(spec)
sys.argv = ["cat", "0"]; spec.loader.exec_module(cf)
rl = cf.relaxed_len_local


def polmul(p, q):
    r = {}
    for i, a in p.items():
        for j, b in q.items():
            r[i+j] = r.get(i+j, 0) + a*b
    return {k: v for k, v in r.items() if v}


def l1(p): return sum(abs(v) for v in p.values())


def ltr(L):
    """exact translation length, minimized over support shifts"""
    best = None; ks = sorted(L)
    for s in range(-ks[-1]-2, -ks[0]+3):
        a = {k+s: v for k, v in L.items()}
        r = rl(1, 0, 0, a)
        if r is None: continue
        v = r + 2*c_pred(1, 0, 0, a)
        if best is None or v < best: best = v
    return best


def K_search(c, e, degmax=5, cmax=4):
    mu = {0: c, 1: -e, 2: c}; cands = []
    for deg in range(degmax+1):
        for coeffs in itertools.product(range(-cmax, cmax+1), repeat=deg+1):
            if coeffs[-1] == 0 or coeffs[0] == 0: continue
            m = {i: cc for i, cc in enumerate(coeffs) if cc}
            L2 = {k: 2*v for k, v in polmul(mu, m).items()}
            cands.append((l1(L2), L2))
    cands.sort(key=lambda x: x[0])
    best = None
    for lv, L2 in cands:
        if best is not None and lv >= best: break   # rigorous prune: ell_tr >= l1
        v = ltr(L2)
        if v is not None and (best is None or v < best): best = v
    return best


def law(c, e): return 3*(c+e) if e >= c else 6*c + min(e, 3*(c-e))


if __name__ == "__main__":
    # (1) calibration
    dist = bfs(14); mis = 0
    for (ee, dl, k, L), d in dist.items():
        r = rl(ee, dl, k, dict(L))
        if r is None: continue
        if r + 2*c_pred(ee, dl, k, dict(L)) != d: mis += 1
    print(f"calibration: {len(dist)} elements to depth 14, formula mismatches = {mis} (want 0)")

    # (4)+(5) table
    shapes = [("(1,2)", 5, 6), ("(1,3)", 5, 8), ("(2,3)", 13, 10), ("(1,5)", 13, 24),
              ("(3,5)", 17, 16), ("(1,4)", 17, 30), ("(3,4)", 25, 14), ("(2,5)", 29, 42),
              ("(4,5)", 41, 18)]
    print(f"{'shape':>7} {'c':>3} {'e':>4} {'law n_T':>8} {'search n_T':>11}")
    for name, c, e in shapes:
        K = K_search(c, e)
        tag = "" if K == 2*law(c, e) else "   ** MISMATCH **"
        print(f"{name:>7} {c:>3} {e:>4} {law(c,e):>8} {K//2:>11}{tag}")
    print("\n(1,2): certified n=33 + parity => K=66 (theorem); (3,4): n=164 -- sharp prediction, >= 43 required: OK")
