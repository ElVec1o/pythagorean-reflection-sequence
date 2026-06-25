#!/usr/bin/env python3
# Sharper pin of the U5b reflection constant C = lim rel/tau.
# Uses C + a*sqrt(tau) + b*tau (+ c*tau^{3/2}) least squares, and iterated Richardson,
# on the clean rows of the m<=200 backup.
import mpmath as mp
mp.mp.dps = 60

def load(path):
    rows = []
    with open(path) as f:
        for line in f:
            t = line.split()
            if len(t) < 8: continue
            dev_ost = mp.mpf(t[5])
            if mp.mpf("0.0388") < dev_ost < mp.mpf("0.0396"):
                rows.append((int(t[0]), mp.mpf(t[1]), mp.mpf(t[7])))  # m, tau, rel/tau
    rows.sort()
    return rows

rows = load("/Users/vico/Documents/elvec1o/u5b/u5b_out_m200.bak")
print(f"clean rows: {len(rows)}  m={rows[0][0]}..{rows[-1][0]}")
taus = [r[1] for r in rows]; f = [r[2] for r in rows]

# ---- multi-parameter LS: f = sum_j c_j * tau^{p_j} ----
def ls_fit(powers, lo_idx):
    # use rows[lo_idx:]
    xs = [[t**p for p in powers] for t in taus[lo_idx:]]
    ys = f[lo_idx:]
    k = len(powers); N = len(ys)
    # normal equations A c = b
    A = [[sum(xs[r][i]*xs[r][j] for r in range(N)) for j in range(k)] for i in range(k)]
    b = [sum(xs[r][i]*ys[r] for r in range(N)) for i in range(k)]
    c = mp.lu_solve(mp.matrix(A), mp.matrix(b))
    resid = sum((sum(c[i]*xs[r][i] for i in range(k)) - ys[r])**2 for r in range(N))
    return [c[i] for i in range(k)], resid

for powers in [[0, mp.mpf("0.5")],
               [0, mp.mpf("0.5"), 1],
               [0, mp.mpf("0.5"), 1, mp.mpf("1.5")]]:
    for lo in [0, len(rows)//3, len(rows)//2]:
        c, resid = ls_fit(powers, lo)
        plabel = "+".join(f"t^{mp.nstr(p,3)}" for p in powers)
        print(f"  powers[{plabel}] rows>={rows[lo][0]:3d}:  C = {mp.nstr(c[0],12)}   resid={mp.nstr(resid,3)}")
print()

# ---- iterated Richardson assuming error ~ sqrt(tau) then ~tau ----
# Stage 1: eliminate sqrt(tau).  tau roughly halves every ~ sqrt2 in m index; use fixed index step.
def richardson(seq_tau, seq_f, p):
    out_t, out_f = [], []
    step = 8
    for i in range(len(seq_f)-step):
        t1,t2 = seq_tau[i], seq_tau[i+step]
        f1,f2 = seq_f[i], seq_f[i+step]
        C = (f1*t2**p - f2*t1**p)/(t2**p - t1**p)
        out_t.append(t1); out_f.append(C)
    return out_t, out_f

t1,f1 = richardson(taus, f, mp.mpf("0.5"))   # kill sqrt(tau)
t2,f2 = richardson(t1, f1, mp.mpf("1.0"))    # kill tau
t3,f3 = richardson(t2, f2, mp.mpf("1.5"))    # kill tau^{3/2}
print("iterated Richardson (kill sqrt(tau), then tau, then tau^{3/2}):")
print(f"   after stage1 (last 3): {[mp.nstr(x,11) for x in f1[-3:]]}")
print(f"   after stage2 (last 3): {[mp.nstr(x,11) for x in f2[-3:]]}")
print(f"   after stage3 (last 3): {[mp.nstr(x,11) for x in f3[-3:]]}")
Cstar = f3[-1]
print(f"\n==> best estimate C = {mp.nstr(Cstar,12)}")
print(f"    reflection coeff c_r = C*sqrt2/36 = {mp.nstr(Cstar*mp.sqrt(2)/36,12)}")
print("\nidentify on tightened C and on c_r:")
for nm,v in [("C",Cstar),("c_r",Cstar*mp.sqrt(2)/36),("C/pi",Cstar/mp.pi),("C*3/pi",Cstar*3/mp.pi)]:
    print(f"   {nm} = {mp.nstr(v,12)}  identify={mp.identify(v)}")
# pslq against a small basis
print("\npslq [C, 1, pi, sqrt2, sqrt3, 1/3] :", mp.pslq([Cstar, mp.mpf(1), mp.pi, mp.sqrt(2), mp.sqrt(3)], maxcoeff=10**6, maxsteps=10**5))
