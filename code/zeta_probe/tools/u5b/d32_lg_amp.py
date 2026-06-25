#!/usr/bin/env python3
# ROUTE D3.2 -- discrete Liouville-Green amplitude/phase invariant.
#
# For z_{n+1} + z_{n-1} = b_n z_n with b_n = 2 cos k_n (oscillatory, |b_n|<2),
# the discrete-LG (Wong-Li / Spigler-Vianello / Olver discrete WKB) ansatz is
#   z_n ~ (sin k_n)^{-1/2} exp( +- i sum_{j} k_j )  [leading order]
# so the AMPLITUDE invariant is  A_n := |z_n| (sin k_n)^{1/2}  -> const  along a
# true oscillatory solution, and the PHASE increment per step is k_n.
#
# We integrate the recursion forward from a generic initial condition (which excites
# BOTH WKB solutions, giving a real standing wave |z_n| that wobbles), and ALSO build
# the two complex WKB-tracking solutions to check the amplitude law cleanly.
#
# Cleanest test of the LG amplitude law: take the TWO independent real solutions
# c_n (cos-like) and s_n (sin-like), form W_n = c_n s_{n+1} - c_{n+1} s_n (the discrete
# Wronskian, EXACTLY constant for z_{n+1}+z_{n-1}=b_n z_n since coefficient of z_{n+1}
# and z_{n-1} are both 1 => Wronskian const). Then the "envelope" of any solution is
# governed by A_n. We verify:
#   (i)  discrete Wronskian is exactly constant (sanity of the symmetric form),
#   (ii) the LG amplitude E_n := (c_n^2 + s_n^2 - b_n c_n s_n)/?  ... use the proper
#        invariant for symmetric recursions.
#
# PROPER amplitude invariant for z_{n+1}+z_{n-1}=2 cos k_n z_n:
#   Define the "energy" of the pair (z_n, z_{n-1}):
#     I_n = z_n^2 + z_{n-1}^2 - b_n z_n z_{n-1}   (= z_n^2+z_{n-1}^2 - 2cos k_n z_n z_{n-1}).
#   For CONSTANT k this is exactly conserved (it's the standard 2-term quadratic invariant
#   = |amplitude|^2 sin^2 k). For slowly varying k_n it drifts; the LG claim is that the
#   normalized amplitude R_n with R_n^2 ~ I_n / sin^2 k_n tracks a constant up to the
#   error-control total variation. We test R_n sqrt(sin k_n) law via I_n.
#
# Actually the textbook statement (Olver, discrete): the two LG solutions satisfy
#   z_n^{+-} = (prod_{j=1}^{n} (something)) , and  |z_n| ~ C (sin k_n)^{-1/2}.
# So  |z_n|^2 sin k_n ~ const, i.e. I_n / sin k_n ~ const (since I_n ~ |z_n|^2 sin^2 k_n
# for the oscillatory invariant amplitude => I_n/sin k_n ~ |z_n|^2 sin k_n ~ const? )
# We just MEASURE I_n and I_n/sin k_n and I_n * sin k_n and report which is flattest.

import mpmath as mp
mp.mp.dps = 40

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))

def run(tau, Nmax=None, verbose=True):
    q = mp.e**(-tau)
    # turning point estimate
    cosh_term = 2*mp.cosh(mp.mpf("1.5")*tau)
    ratio = (cosh_term-2)/(2*(1-q)*q**mp.mpf("0.5"))
    nstar = mp.log(ratio)/(2*mp.log(q)) if 0<ratio<1 else mp.mpf(50)
    N = Nmax if Nmax else int(min(float(nstar)*0.85, 4000))
    # forward recursion from a generic real start
    z = [mp.mpf("1.0"), mp.mpf("1.3")]   # z_0, z_1 generic
    for n in range(1, N+1):
        bn = bcoef(n, q)
        z.append(bn*z[n] - z[n-1])
    # invariants
    rows=[]
    for n in range(1, N):
        bn = bcoef(n, q)
        if abs(bn) >= 2:  # left oscillatory region
            break
        kn = mp.acos(bn/2)
        sk = mp.sin(kn)
        I = z[n]**2 + z[n-1]**2 - bn*z[n]*z[n-1]   # quadratic invariant
        rows.append((n, kn, sk, I))
    if not rows:
        return None
    # report flatness of I, I/sin k, I*sin k across the bulk (skip first few, last few)
    lo = max(2, len(rows)//10); hi = len(rows) - max(2, len(rows)//10)
    sub = rows[lo:hi]
    def stats(vals):
        vmin=min(vals); vmax=max(vals); vmean=sum(vals)/len(vals)
        return vmin, vmax, (vmax-vmin)/vmean
    Iv   = [r[3] for r in sub]
    Iosk = [r[3]/r[2] for r in sub]
    Ixsk = [r[3]*r[2] for r in sub]
    if verbose:
        print(f"tau={float(tau):.4f} q={mp.nstr(q,6)}  N_osc={len(rows)} (n*~{mp.nstr(nstar,5)})")
        for nm, vv in [("I_n        ", Iv), ("I_n/sin k  ", Iosk), ("I_n*sin k  ", Ixsk)]:
            mn,mx,sp = stats(vv)
            print(f"   {nm}: min={mp.nstr(mn,7)} max={mp.nstr(mx,7)} relspread={mp.nstr(sp,5)}")
        # sample k_n, sin k_n trend
        print(f"   k_1={mp.nstr(rows[0][1],6)} k_mid={mp.nstr(rows[len(rows)//2][1],6)} k_last={mp.nstr(rows[-1][1],6)}")
        print()
    return rows

for tau in [mp.mpf("0.1"), mp.mpf("0.05"), mp.mpf("0.02"), mp.mpf("0.01")]:
    run(tau)
