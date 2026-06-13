#!/usr/bin/env python3
"""
ROUTE B: high-precision beta_2 = lim u_{n+1}/u_n for A396406, plus inverse symbolic.
"""
from fractions import Fraction as Fr
import mpmath as mp

mp.mp.dps = 60

u = [1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,
     11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,
     1127236,1697179,2554961,3848384,5777651,8679441,13031206,19574659,
     29338781,43997388,65932461,98849591,147969934]
N = len(u)
print(f"N terms = {N}")

# ---- exact ratios as Fractions, then to mpf ----
ratios = [Fr(u[i+1], u[i]) for i in range(N-1)]   # length 42
r = [mp.mpf(x.numerator)/mp.mpf(x.denominator) for x in ratios]
print(f"raw last ratio u42/u41 = {mp.nstr(r[-1], 20)}")
print(f"raw u41/u40           = {mp.nstr(r[-2], 20)}")

# =====================================================================
# (1a) Repeated Aitken / Shanks transformation
# =====================================================================
def aitken(seq):
    out = []
    for i in range(len(seq)-2):
        a, b, c = seq[i], seq[i+1], seq[i+2]
        denom = (c - 2*b + a)
        if denom == 0:
            out.append(b)
        else:
            out.append(c - (c-b)**2/denom)
    return out

def repeated_aitken(seq, rounds):
    s = list(seq)
    history = []
    for k in range(rounds):
        if len(s) < 3:
            break
        s = aitken(s)
        history.append(s[-1])
    return s, history

acc, hist = repeated_aitken(r, 18)
print("\n=== Repeated Aitken (last value after each round) ===")
for k, v in enumerate(hist, 1):
    print(f" round {k:2d}: {mp.nstr(v, 22)}")
shanks_val = hist[-1] if hist else None

# =====================================================================
# (1b) Wynn's epsilon algorithm (rho/epsilon) -> Shanks via better impl
# =====================================================================
def wynn_epsilon(seq):
    n = len(seq)
    # e[k][i]; e[-1]=0, e[0]=seq
    e_prev = [mp.mpf(0)]*(n+1)   # epsilon_{-1}
    e_cur  = [mp.mpf(0)]*n       # epsilon_0
    for i in range(n):
        e_cur[i] = seq[i]
    table_best = []
    k = 0
    cols = [e_prev, e_cur]
    while True:
        prev = cols[-2]
        cur = cols[-1]
        m = len(cur) - 1
        if m < 1:
            break
        nxt = []
        for i in range(m):
            d = cur[i+1] - cur[i]
            if d == 0:
                nxt.append(mp.mpf('inf'))
            else:
                # prev is shifted: epsilon_{k-1} at index i+1
                nxt.append(prev[i+1] + 1/d)
        cols.append(nxt)
        k += 1
        if len(nxt) == 0:
            break
    # the even columns (k even) hold the accelerated approximants
    # collect last finite entry of each even column
    results = []
    for kk in range(2, len(cols), 2):
        col = cols[kk]
        # find last finite
        for v in reversed(col):
            if mp.isfinite(v):
                results.append((kk-1, v))  # kk index -> epsilon_{kk-1}? keep track
                break
    return cols, results

cols, wynn_results = wynn_epsilon(r)
print("\n=== Wynn epsilon (last finite entry of each even column) ===")
wynn_val = None
for idx, v in wynn_results:
    print(f" eps col idx {idx:2d}: {mp.nstr(v, 22)}")
    if mp.isfinite(v):
        wynn_val = v

# =====================================================================
# (1c) Richardson extrapolation assuming r_n ~ beta + C * lambda^n  (geometric)
#      Use the model r_n = beta + C * t^n. Estimate via three consecutive.
#      Equivalent to one Aitken step; also do Richardson on 1/n powers as a cross-check.
# =====================================================================
# Geometric-decay aware: fit beta from successive Aitken already done.
# Cross-check: assume error ~ C/n^p is wrong (error is geometric), so Aitken/Shanks is right tool.

# Direct estimate of the subdominant ratio lambda (rate of convergence of r_n)
diffs = [r[i+1]-r[i] for i in range(len(r)-1)]
lam_est = [diffs[i+1]/diffs[i] for i in range(len(diffs)-1)]
print("\n=== Estimated convergence rate lambda = d_{n+1}/d_n (last few) ===")
for v in lam_est[-6:]:
    print("  ", mp.nstr(v, 12))

# =====================================================================
# Consolidate a best value + error bar
# =====================================================================
print("\n=========== CONSOLIDATED ESTIMATES ===========")
candidates = {}
if shanks_val is not None:
    candidates['repeated_Aitken_last'] = shanks_val
if wynn_val is not None:
    candidates['Wynn_epsilon_last'] = wynn_val

# Take a stable plateau from the Aitken history: look where successive rounds agree most
print("Aitken history pairwise |delta|:")
for k in range(1, len(hist)):
    d = abs(hist[k]-hist[k-1])
    print(f"  round {k} vs {k+1}: |delta| = {mp.nstr(d, 6)}")

# Choose the round minimizing the change to the next round (most converged before noise)
best_k = None
best_d = None
for k in range(1, len(hist)):
    d = abs(hist[k]-hist[k-1])
    if best_d is None or d < best_d:
        best_d = d
        best_k = k
plateau_val = hist[best_k]
print(f"\nMost-converged Aitken plateau at round {best_k+1}: {mp.nstr(plateau_val, 25)}")
print(f"  change to neighbor (error proxy): {mp.nstr(best_d, 6)}")

vals = list(candidates.values()) + [plateau_val]
vmin = min(vals); vmax = max(vals)
spread = vmax - vmin
center = (vmin+vmax)/2
print(f"\nMethod spread: vmin={mp.nstr(vmin,18)} vmax={mp.nstr(vmax,18)}")
print(f"Spread (method disagreement) = {mp.nstr(spread, 6)}")
print(f"Center = {mp.nstr(center, 18)}")

beta = plateau_val
err = max(spread, best_d)
print(f"\n>>> BEST beta_2 = {mp.nstr(beta, 18)}")
print(f">>> honest error bar ~ {mp.nstr(err, 4)}")
trust_digits = int(-mp.log10(err)) if err>0 else 99
print(f">>> trustworthy decimal digits ~ {trust_digits}")

# =====================================================================
# (2) Inverse symbolic
# =====================================================================
print("\n=========== INVERSE SYMBOLIC ===========")
print(f"3/2 = 1.5 ; beta - 3/2 = {mp.nstr(beta - mp.mpf(3)/2, 8)}")

# 1 + 2 cos(2 pi / k) for small k
print("\n1 + 2cos(2pi/k):")
for k in range(5, 25):
    val = 1 + 2*mp.cos(2*mp.pi/k)
    if abs(val-beta) < 0.01:
        print(f"  k={k}: {mp.nstr(val,12)}  diff={mp.nstr(val-beta,6)}")

# quadratic roots x^2 + a x + b with small integer a,b near beta
print("\nQuadratic x^2+ax+b roots near beta (|a|,|b|<=12):")
best_quad = []
for a in range(-12,13):
    for b in range(-12,13):
        disc = a*a - 4*b
        if disc < 0:
            continue
        root = (-a + mp.sqrt(disc))/2
        if abs(root-beta) < 5e-4:
            best_quad.append((abs(root-beta), a, b, root))
best_quad.sort()
for d,a,b,root in best_quad[:12]:
    print(f"  x^2+({a})x+({b})=0 root={mp.nstr(root,14)} diff={mp.nstr(d,4)}")

# Cubic via small integer poly search using PSLQ on [1, beta, beta^2, beta^3]
print("\nPSLQ integer-relation search [1,beta,...,beta^d]:")
for deg in (2,3,4):
    basis = [beta**i for i in range(deg+1)]
    rel = mp.pslq(basis, maxcoeff=10**6, maxsteps=10**6)
    if rel:
        # reconstruct value
        poly = " + ".join(f"({rel[i]})*x^{i}" for i in range(deg+1))
        # evaluate residual
        resid = sum(rel[i]*basis[i] for i in range(deg+1))
        height = max(abs(c) for c in rel)
        print(f"  deg {deg}: coeffs {rel}  height={height}  residual={mp.nstr(resid,4)}")
    else:
        print(f"  deg {deg}: no relation found (maxcoeff 1e6)")

# mpmath.identify
print("\nmpmath.identify(beta):")
try:
    ident = mp.identify(beta)
    print("  ", ident)
except Exception as e:
    print("  identify error:", e)

print("\nmpmath.identify(beta) with constants [sqrt(2),sqrt(3),sqrt(5)]:")
for c in ['sqrt(2)','sqrt(3)','sqrt(5)','pi']:
    try:
        idd = mp.identify(beta, [c])
        print(f"   with {c}: {idd}")
    except Exception as e:
        print(f"   with {c}: err {e}")

# =====================================================================
# (3) Can we distinguish 3/2 from a nearby algebraic number?
# =====================================================================
print("\n=========== HONESTY CHECK ===========")
gap_to_32 = abs(beta - mp.mpf(3)/2)
print(f"|beta - 3/2|      = {mp.nstr(gap_to_32, 6)}")
print(f"error bar         = {mp.nstr(err, 6)}")
if gap_to_32 < err:
    print("=> 3/2 is WITHIN the error bar: cannot exclude exactly 3/2, but cannot confirm it either.")
else:
    print("=> 3/2 is OUTSIDE the error bar by", mp.nstr(gap_to_32/err,4), "sigma (tentative).")
print(f"\nNote: only {N} terms; geometric error decays like lambda^n with lambda ~ {mp.nstr(lam_est[-1],6)}")
