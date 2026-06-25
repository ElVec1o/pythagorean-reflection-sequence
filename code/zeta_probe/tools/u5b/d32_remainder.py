#!/usr/bin/env python3
# ROUTE D3.2 -- the DECISIVE remainder question.
#
# We have established (numerically, high precision):
#   Phase law:  sum_{n>=0} k_n = w - 3pi/4 + a1 sqrt(tau) + ...   (exponent EXACTLY 1/2)
#   Cube corr:  (1/24) sum k_n^3 -> sqrt2/36 sqrt(tau)            (EM curvature)
#
# The discrete-LG theory (Wong-Li, Math.Comp 72 (2003) 1675; Spigler-Vianello) gives,
# for z_{n+1}+z_{n-1}=b_n z_n in an oscillatory range, an EXACT representation
#     z_n = (sin k_n)^{-1/2} [ A exp(i sum_{j<n} k_j) (1+eps_n^+) + c.c. ]
# where the RELATIVE error eps_n satisfies  |eps_n| <= exp(V_n) - 1,  V_n = the
# error-control total variation  = sum_{j>=n} |h_j|, with h_j an EXPLICIT second-difference
# of the LG phase/amplitude (the "error-control function").  The Poincare-validity of the
# whole asymptotic expansion reduces to:
#   (R)  V := sum_{j=0}^{n*} |h_j|  is BOUNDED uniformly in tau  AND admits its own
#        asymptotic expansion in sqrt(tau).
#
# We test (R) by computing the *actual* relative LG error eps_n along the recursion and
# its accumulation, and by checking whether the next phase coefficient a1 is a fixed
# number (Poincare) rather than oscillating.
#
# CRUCIAL DISTINCTION for the honesty report:
#   - An ABSOLUTE bound on V gives a bound on the REMAINDER of the LG series, i.e. it
#     proves the expansion is ASYMPTOTIC (Poincare) -- IF V and its refinements are
#     each O(tau^{k}) so that truncating the LG series at order K leaves O(tau^{K+1}).
#   - It does NOT by itself require oscillatory cancellation, BECAUSE the LG ansatz has
#     ALREADY extracted the oscillation exp(i sum k). The error-control function h_j is
#     NON-oscillatory (it is |second difference of slowly-varying amplitude/phase|), so
#     an absolute (triangle-inequality) bound suffices. THIS is the key claim to test:
#     is h_j genuinely non-oscillatory and summable to O(1) with sqrt(tau) refinements?

import mpmath as mp
mp.mp.dps = 50

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))
def kfun(n, q):
    bn = bcoef(n, q)
    if abs(bn) >= 2: return None
    return mp.acos(bn/2)

# The Wong-Li error-control function for y_{n+1}-2 a_n y_n + y_{n-1}=0 (a_n=cos k_n):
# Define the LG phase increment and amplitude. The standard control function (Olver-type,
# adapted by Wong-Li) is
#    F_n = sum_{j=n}^{N} | (1/ (4) ) * second-difference-related term |.
# Practically the dominant control term is
#    h_n = | Delta^2 (k_n) | / sin k_n   +   (amplitude curvature) | Delta^2 log sqrt(sin k_n) |.
# We compute BOTH the practical control sum AND, independently, the *measured* relative
# error of the leading LG ansatz against the exact recursion.

def measure(tau, report=True):
    q = mp.e**(-tau)
    # collect oscillatory k_n
    ks=[]; n=0
    while True:
        kn=kfun(n,q)
        if kn is None: break
        ks.append(kn); n+=1
        if n>400000: break
    N=len(ks)
    # ----- control function (non-oscillatory, second differences) -----
    Hphase=mp.mpf(0); Hamp=mp.mpf(0)
    sk=[mp.sin(k) for k in ks]
    logamp=[ -mp.mpf("0.5")*mp.log(s) for s in sk ]  # log of (sin k)^{-1/2}
    for j in range(1,N-1):
        Hphase += abs(ks[j+1]-2*ks[j]+ks[j-1])/sk[j]
        Hamp   += abs(logamp[j+1]-2*logamp[j]+logamp[j-1])
    Hctrl = Hphase + Hamp
    # ----- measured relative error of leading LG ansatz -----
    # Build exact complex solution Z_n with Z_0=1, Z_1=e^{i k_0} (local plane wave seed at n=0)
    # Compare |Z_n| to predicted C*(sin k_n)^{-1/2}; the *fluctuation* of |Z_n| sqrt(sin k_n)
    # around its mean is the measured LG amplitude error. (Cleaner than before: seed at n=0.)
    Z=[mp.mpf(1), mp.e**(1j*ks[0])]
    for m in range(1,N+1):
        bn=bcoef(m,q)
        if abs(bn)>=2: break
        Z.append(bn*Z[m]-Z[m-1])
    M=len(Z)-1
    inv=[]
    for m in range(0,min(M,N)):
        km=ks[m] if m<N else None
        if km is None: break
        inv.append(abs(Z[m])*mp.sqrt(mp.sin(km)))   # = |Z| (sin k)^{1/2}  ~ const (LG)
    lo=max(2,len(inv)//8); hi=len(inv)-max(3,len(inv)//8)
    sub=inv[lo:hi]
    mean=sum(sub)/len(sub)
    fluct=max(abs(v-mean) for v in sub)/mean   # relative LG amplitude fluctuation
    if report:
        print(f"tau={float(tau):.4f}  N_osc={N}")
        print(f"   control fn  H = Hphase+Hamp = {mp.nstr(Hphase,6)} + {mp.nstr(Hamp,6)} = {mp.nstr(Hctrl,6)}")
        print(f"   measured rel LG amp fluctuation (|Z|sqrt(sin k) about mean) = {mp.nstr(fluct,5)}")
        print(f"   exp(H)-1 (LG error bound) = {mp.nstr(mp.e**Hctrl-1,5)}   [should DOMINATE fluct]")
    return tau, N, Hphase, Hamp, Hctrl, fluct

print("=== (R) error-control fn H vs measured LG error, scaling in tau ===")
res=[]
for tau in [mp.mpf("0.05"),mp.mpf("0.02"),mp.mpf("0.01"),mp.mpf("0.005"),mp.mpf("0.002"),mp.mpf("0.001")]:
    res.append(measure(tau))
    print()

print("=== scaling table ===")
print(" tau       Hphase      Hamp       Hctrl      fluct     Hctrl/sqrt(tau)  Hamp(const?)")
for r in res:
    tau,N,Hp,Ha,Hc,fl=r
    print(f" {float(tau):.4f}  {mp.nstr(Hp,5):>9}  {mp.nstr(Ha,5):>8}  {mp.nstr(Hc,5):>8}  {mp.nstr(fl,4):>8}  {mp.nstr(Hc/mp.sqrt(tau),5):>10}   {mp.nstr(Ha,6)}")
