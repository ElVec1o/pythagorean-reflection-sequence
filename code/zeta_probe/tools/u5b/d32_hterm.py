#!/usr/bin/env python3
# ROUTE D3.2 -- is the per-term control h_j NON-oscillatory (=> absolute bound legit),
# and what is the true tau-scaling of H? Decompose H into "bulk" + "endpoint" pieces.
#
# h_j (phase part) = |Delta^2 k_j| / sin k_j.  With k_j ~ sqrt(2tau) q^j (smooth, monotone
# DECREASING), Delta^2 k_j = k_{j+1}-2k_j+k_{j-1} ~ sqrt(2tau) q^j (q-1)^2 ~ sqrt(2tau) tau^2 q^j,
# and sin k_j ~ k_j ~ sqrt(2tau) q^j, so h_j ~ tau^2  PER TERM, summed over ~1/tau? No:
# sum_j tau^2 = tau^2 * (number of terms). But the terms where sin k_j is SMALL (near the
# turning point, k_j->0) make h_j BLOW UP (divide by small sin). That's the endpoint issue.
#
# So: h_j is smooth & non-oscillatory (no sign changes from a phase), BUT it has an
# INTEGRABLE-LOOKING singularity as j->n* (k->0). The sum near the turning point is the
# delicate part -- precisely where the LG approximation breaks and the Bessel/Airy
# connection takes over. We quantify: split sum at j where k_j drops below sqrt(tau)
# (the LG/connection boundary) and report bulk vs near-turning contributions.

import mpmath as mp
mp.mp.dps = 50

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))
def kfun(n, q):
    bn = bcoef(n, q)
    if abs(bn) >= 2: return None
    return mp.acos(bn/2)

def analyze(tau):
    q = mp.e**(-tau)
    ks=[]; n=0
    while True:
        kn=kfun(n,q)
        if kn is None: break
        ks.append(kn); n+=1
        if n>400000: break
    N=len(ks)
    sk=[mp.sin(k) for k in ks]
    # per-term h_j, check sign of Delta^2 k (non-oscillatory <=> constant sign)
    d2=[ks[j+1]-2*ks[j]+ks[j-1] for j in range(1,N-1)]
    signs=set(1 if x>0 else (-1 if x<0 else 0) for x in d2)
    h=[abs(d2[j-1])/sk[j] for j in range(1,N-1)]   # aligned with j=1..N-2
    # split: "near turning" = last few where k<sqrt(tau); "bulk" = rest
    thr=mp.sqrt(tau)
    Hbulk=mp.mpf(0); Hturn=mp.mpf(0); jturn=None
    for idx,j in enumerate(range(1,N-1)):
        if ks[j] < thr:
            Hturn += h[idx]
            if jturn is None: jturn=j
        else:
            Hbulk += h[idx]
    # endpoint at n=0 (left edge): the LG breaks at small n too? k_0 = max k (largest),
    # sin k_0 is largest, so left endpoint is benign. The issue is the RIGHT (turning).
    return tau, N, signs, Hbulk, Hturn, jturn, ks[0], ks[-1]

print("=== per-term control h_j: sign of Delta^2 k (non-oscillatory?), bulk vs turning ===")
for tau in [mp.mpf("0.02"),mp.mpf("0.01"),mp.mpf("0.005"),mp.mpf("0.002"),mp.mpf("0.001")]:
    tau,N,signs,Hb,Ht,jt,k0,klast=analyze(tau)
    print(f"tau={float(tau):.4f} N={N}: Delta^2 k signs={signs}  (single sign => non-oscillatory)")
    print(f"    H_bulk(k>=sqrt(tau))={mp.nstr(Hb,6)}   H_turning(k<sqrt(tau))={mp.nstr(Ht,6)}  jturn={jt}")
    print(f"    H_bulk/sqrt(tau)={mp.nstr(Hb/mp.sqrt(tau),5)}   k_0={mp.nstr(k0,5)} k_last={mp.nstr(klast,5)}")
    print()

# Interpretation: if Delta^2 k has CONSTANT sign, the control function is the sum of a
# NON-NEGATIVE, NON-OSCILLATORY sequence => an ABSOLUTE (triangle) bound IS the exact sum,
# no cancellation possible or needed. The remaining question is the TURNING-POINT block,
# which is handled by the EXPLICIT half-integer Bessel connection (NOT by LG, NOT by an
# absolute bound on h). That block is O(1) by the elementary J_{3/2} connection formula.
