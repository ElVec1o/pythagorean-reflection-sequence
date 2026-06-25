#!/usr/bin/env python3
# Analyze u5b_out.txt: extrapolate rel/tau (the U5b reflection constant) as tau->0,
# determine the convergence exponent p (rel/tau = C + a*tau^p), and identify C.
import mpmath as mp
mp.mp.dps = 50

rows = []
with open("/Users/vico/Documents/elvec1o/u5b/u5b_out.txt") as f:
    for line in f:
        t = line.split()
        if len(t) < 8:
            continue
        m = int(t[0]); tau = mp.mpf(t[1]); dev = mp.mpf(t[2])
        defect = mp.mpf(t[3]); cube = mp.mpf(t[4])
        dev_ost = mp.mpf(t[5]); rel = mp.mpf(t[6]); rel_ot = mp.mpf(t[7])
        # keep only CLEAN rows: dev/sqrt(tau) must be ~ sqrt2/36 = 0.0392837
        if mp.mpf("0.0388") < dev_ost < mp.mpf("0.0396"):
            rows.append((m, tau, dev, defect, cube, dev_ost, rel, rel_ot))

rows.sort()
print(f"clean rows: {len(rows)}  (m={rows[0][0]}..{rows[-1][0]}, tau {mp.nstr(rows[0][1],3)}..{mp.nstr(rows[-1][1],3)})")
sqrt2_36 = mp.sqrt(2)/36
print(f"sqrt2/36 = {mp.nstr(sqrt2_36,12)}   (dev/sqrtT target)")
print()

# ---- 1) local convergence exponent p of rel/tau, from consecutive triples ----
# assume f(tau) = C + a*tau^p; with three points solve for p via ratios.
print("local exponent p (rel/tau = C + a*tau^p), from triples spaced by factor ~2 in tau:")
taus  = [r[1] for r in rows]
relot = [r[7] for r in rows]
# pick a geometric-ish subsequence by index
idx = list(range(0, len(rows)))
def triple_exponent(i, j, k):
    t1,t2,t3 = taus[i],taus[j],taus[k]
    f1,f2,f3 = relot[i],relot[j],relot[k]
    # (f2-f1)/(f3-f2) = (t2^p - t1^p)/(t3^p - t2^p); solve for p numerically
    try:
        g = lambda p: (f2-f1)*(t3**p - t2**p) - (f3-f2)*(t2**p - t1**p)
        p = mp.findroot(g, mp.mpf("0.5"))
        return p
    except Exception:
        return None
n = len(rows)
for frac in [0.3, 0.45, 0.6, 0.75, 0.9]:
    i = int(frac*n); j = min(i+8, n-1); k = min(i+16, n-1)
    if k < n and i < j < k:
        p = triple_exponent(i,j,k)
        if p is not None:
            print(f"  tau~{mp.nstr(taus[i],3)}: p = {mp.nstr(p,6)}")
print()

# ---- 2) extrapolate C assuming p=1/2 and p=1, Richardson on the tail ----
def extrap_fixed_p(p):
    # C = (f2 - f1*(t2/t1)^p? ) -- use pairs: f = C + a tau^p
    #   C = (f1*t2^p - f2*t1^p)/(t2^p - t1^p)
    Cs = []
    step = 6
    for i in range(len(rows)-step):
        t1,t2 = taus[i],taus[i+step]
        f1,f2 = relot[i],relot[i+step]
        C = (f1*t2**p - f2*t1**p)/(t2**p - t1**p)
        Cs.append((taus[i], C))
    return Cs

for p in [mp.mpf("0.5"), mp.mpf("1.0")]:
    Cs = extrap_fixed_p(p)
    print(f"extrapolated C with p={mp.nstr(p,3)} (tail should stabilize):")
    for tau,C in Cs[::max(1,len(Cs)//8)]:
        print(f"   tau~{mp.nstr(tau,3)}:  C = {mp.nstr(C,10)}")
    print(f"   --> last: C = {mp.nstr(Cs[-1][1],12)}")
    print()

# ---- 3) free fit of (C,a,p) on the tail via least squares over a grid of p ----
print("free fit C+a*tau^p on tail (last ~40 clean points), scan p:")
tail = rows[-40:] if len(rows) >= 40 else rows
tt = [r[1] for r in tail]; ff = [r[7] for r in tail]
best = None
p = mp.mpf("0.30")
while p <= mp.mpf("1.21"):
    # linear LS for C,a given p:  f = C + a*x, x=tau^p
    xs = [t**p for t in tt]
    n2 = len(xs)
    sx = sum(xs); sxx = sum(x*x for x in xs); sf = sum(ff); sxf = sum(x*f for x,f in zip(xs,ff))
    det = n2*sxx - sx*sx
    a = (n2*sxf - sx*sf)/det
    C = (sf - a*sx)/n2
    resid = sum((C + a*x - f)**2 for x,f in zip(xs,ff))
    if best is None or resid < best[0]:
        best = (resid, p, C, a)
    p += mp.mpf("0.01")
resid,p,C,a = best
print(f"  best p = {mp.nstr(p,4)},  C = {mp.nstr(C,14)},  a = {mp.nstr(a,8)},  resid = {mp.nstr(resid,3)}")
print()

# ---- 4) identify C ----
print(f"==> reflection constant  C (rel/tau limit) ~ {mp.nstr(C,14)}")
print("identify attempts:")
for label,val in [("C", C)]:
    r = mp.identify(val)
    print(f"  identify({label}={mp.nstr(val,12)}) = {r}")
    # try common forms
    for desc,expr in [("C*7", C*7),("C/sqrt2",C/mp.sqrt(2)),("C*sqrt2",C*mp.sqrt(2)),
                      ("C*3",C*3),("C*36/sqrt2 (=C/(sqrt2/36))",C*36/mp.sqrt(2)),
                      ("C - 7",C-7),("C*pi",C*mp.pi),("C/pi",C/mp.pi)]:
        print(f"    {desc:28s} = {mp.nstr(expr,12)}   identify={mp.identify(expr)}")
# named-constant candidates (turning-point constants tend to involve pi)
print("  named-constant candidates near C:")
cands = [("22/3", mp.mpf(22)/3), ("7pi/3", 7*mp.pi/3), ("2pi+1", 2*mp.pi+1),
         ("51/7", mp.mpf(51)/7), ("16pi/7", 16*mp.pi/7), ("4+pi", 4+mp.pi),
         ("3+sqrt2*3", 3+3*mp.sqrt(2)), ("pi^2*3/4", mp.pi**2*mp.mpf(3)/4),
         ("9*sqrt2/sqrt3", 9*mp.sqrt(2)/mp.sqrt(3)), ("73/10", mp.mpf(73)/10)]
for name,val in cands:
    print(f"    {name:16s} = {mp.nstr(val,10)}   (C - this = {mp.nstr(C-val,4)})")
# rational guesses
print("  nearby simple rationals:")
for den in range(2,40):
    num = mp.nint(C*den)
    if abs(C - num/den) < mp.mpf("0.01"):
        print(f"    {int(num)}/{den} = {mp.nstr(num/den,10)}  (err {mp.nstr(abs(C-num/den),3)})")
