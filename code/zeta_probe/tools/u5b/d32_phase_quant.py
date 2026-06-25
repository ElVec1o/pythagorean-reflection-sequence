#!/usr/bin/env python3
# ROUTE D3.2 -- PHASE / QUANTIZATION via discrete LG, and the per-step defect accumulation.
#
# Two questions decisive for Poincare validity:
#  (Q1) Does the accumulated LG PHASE  Phi(tau) = sum_{n=1}^{n*} k_n  (+ connection const)
#       reproduce the known pole law  w_m ~ (m+1/2)pi - sqrt2/36 sqrt(tau) - ...?
#       i.e. is the *integrated* phase the right asymptotic object, with corrections
#       that are themselves an asymptotic series in tau?
#  (Q2) Does the per-step LG defect d_n (the amount by which the exact solution fails the
#       leading LG ansatz) sum to something BOUNDED, and does sum d_n admit an asymptotic
#       expansion in tau (Poincare), or is there irreducible oscillatory cancellation?
#
# Phase budget:  sum_{n>=0} k_n  with k_n = arccos(b_n/2).  Memory claims
#   (1/24) sum k_n^3 = sqrt2/36 sqrt(tau)  (the sharp phase correction, Euler-Maclaurin).
# We verify the LEADING phase sum and the cube-sum correction here, scalar.
#
# k_n = arccos( cosh(1.5 tau) - (1-q) q^{2n+1/2} ).  Near tau=0:
#   let x = q^n (continuous), b/2 ~ 1 - (1-q) q^{1/2} x^2 + (9/8)tau^2 ...
#   k ~ sqrt(2(1-q) q^{1/2}) x = sqrt(2 tau) x (1+O(tau)).  => sum k_n ~ INT_0^inf sqrt(2tau) q^n dn
#       = sqrt(2tau)/(-ln q) * 1 ... = sqrt(2tau)/tau = sqrt(2/tau) = w. (LEADING phase = w!)
# So Phi_lead = w, matching confluence 1-cos w.  Corrections give the c_k.

import mpmath as mp
mp.mp.dps = 45

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))

def kfun(n, q):
    bn = bcoef(n, q)
    if abs(bn) >= 2:
        return None
    return mp.acos(bn/2)

def phase_sums(tau):
    q = mp.e**(-tau)
    S1 = mp.mpf(0); S3 = mp.mpf(0); n=0
    ks=[]
    while True:
        kn = kfun(n,q)
        if kn is None:
            break
        ks.append(kn); S1 += kn; S3 += kn**3
        n+=1
        if n>200000: break
    w = mp.sqrt(2/tau)
    return q, w, S1, S3, len(ks)

print("=== (Q1) phase budget sum k_n vs w, and (1/24) sum k_n^3 vs sqrt2/36 sqrt(tau) ===")
sqrt2_36 = mp.sqrt(2)/36
for tau in [mp.mpf("0.05"), mp.mpf("0.02"), mp.mpf("0.01"), mp.mpf("0.005"), mp.mpf("0.002")]:
    q,w,S1,S3,N = phase_sums(tau)
    cube_corr = S3/24
    print(f"tau={float(tau):.4f}: sum k = {mp.nstr(S1,10)}  w={mp.nstr(w,10)}  (sumk - w)={mp.nstr(S1-w,6)}")
    print(f"            (1/24)sum k^3 = {mp.nstr(cube_corr,8)}   sqrt2/36 sqrt(tau)={mp.nstr(sqrt2_36*mp.sqrt(tau),8)}   ratio={mp.nstr(cube_corr/(sqrt2_36*mp.sqrt(tau)),7)}")
    # The discrete-LG sharp phase is  Phi = sum k_n - (1/24) sum k_n^3 + ...  (Euler-Maclaurin
    # endpoint + curvature correction). Memory: (m+1/2)pi - w_m == (1/24) sum k^3.
    # Here at a GENERIC tau the relevant combo for the pole law is sum k - (1/24)sum k^3:
    Phi = S1 - cube_corr
    print(f"            Phi = sum k - (1/24)sum k^3 = {mp.nstr(Phi,10)}   (sum k - w)+? ; (Phi-w)={mp.nstr(Phi-w,6)}")
    print()

# Now: at a TRAVEL POLE w_m, the quantization is Phi(tau_m) = (m+1/2) pi  (standing wave).
# Memory's verified identity: (m+1/2)pi - w_m = (1/24) sum k_n^3 -> sqrt2/36 sqrt(tau).
# i.e. sum_{n} k_n  (the full phase) hits (m+1/2)pi at the pole, and the correction
# between "w" (continuum phase) and "sum k_n" (discrete phase) is EXACTLY the EM cube term.
# Let's verify THAT directly at a few poles by root-finding Sigma=... no, we use the
# recursion's own pole condition is heavy; instead verify (sumk - w) ~ ? expansion in tau.
print("=== (sum k_n - w) asymptotics: is it an analytic series in sqrt(tau)? ===")
def sk_minus_w(tau):
    q,w,S1,S3,N = phase_sums(tau)
    return S1 - w
# fit (S1-w) = a*tau^p ... measure local exponent
taus=[mp.mpf("0.02")/2**i for i in range(6)]
vals=[sk_minus_w(t) for t in taus]
for i in range(len(taus)):
    print(f"  tau={mp.nstr(taus[i],4)}  sumk-w={mp.nstr(vals[i],8)}  (sumk-w)/sqrt(tau)={mp.nstr(vals[i]/mp.sqrt(taus[i]),7)}  (sumk-w)/tau={mp.nstr(vals[i]/taus[i],7)}")
