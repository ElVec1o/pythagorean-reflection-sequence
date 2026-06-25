#!/usr/bin/env python3
# ROUTE D3.2 -- the TURNING-POINT block.  Verify:
#  (T1) near n*, b_n/2 - 1 is LINEAR in (n-n*)  => Airy-type turning point (generic),
#       BUT the relevant connection for THIS problem is the elementary one because the
#       continuum limit is J_{1/2}/J_{3/2} (half-integer). Check the local profile.
#  (T2) the connection contributes a FIXED phase; decompose the -3pi/4 as
#       (left endpoint EM half-step) + (turning-point connection -pi/4 or -3pi/4).
#
# Concretely: the WKB/LG phase accumulated from n=0 to the turning point, PLUS the
# standard turning-point connection phase (-pi/4 for a simple Airy turning point), should
# match the measured offset.  We test by computing
#     Phi_LG(tau) = sum_{n: k_n real} k_n     (already = w - 3pi/4 + a sqrt(tau))
# and comparing the DISCRETE sum to the CONTINUUM WKB integral INT_0^{n*} k(n) dn plus
# Euler-Maclaurin endpoint corrections, isolating the constant.
#
# Continuum: k(n) = arccos( cosh(1.5 tau) - (1-q) q^{1/2} q^{2n} ).  Let x=q^n in (0,1].
# At n=0, x=1: k(0)=arccos(cosh(1.5tau)-(1-q)q^{1/2}) = k_0 (largest).
# At turning x_*=q^{n*}: argument =1, k=0.
# WKB integral  I = INT_{0}^{n*} k(n) dn.  Change var x=q^n, dn = dx/(x ln q) = -dx/(x*tau):
#   I = INT_{x_*}^{1} k(x) * dx/(x*tau)   (sign: as n:0->n*, x:1->x_*, dn>0 => -dx)
#     = (1/tau) INT_{x_*}^{1} arccos(C - D x^2) dx/x,  C=cosh(1.5tau), D=(1-q)q^{1/2}.
# We compute I numerically and compare sum k_n vs I, extracting the EM constant.

import mpmath as mp
mp.mp.dps = 50

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))
def kfun(n, q):
    bn = bcoef(n, q)
    if abs(bn) >= 2: return None
    return mp.acos(bn/2)

def analyze(tau):
    q=mp.e**(-tau)
    C=mp.cosh(mp.mpf("1.5")*tau); D=(1-q)*q**mp.mpf("0.5")
    # turning x_* where C - D x_*^2 = 1 => x_*^2=(C-1)/D
    xstar=mp.sqrt((C-1)/D)
    # WKB continuum integral I = (1/tau) INT_{x_*}^{1} arccos(C-D x^2) dx/x
    f=lambda x: mp.acos(C - D*x**2)/x
    I=mp.quad(f,[xstar,1])/tau
    # discrete sum
    S=mp.mpf(0); n=0
    while True:
        kn=kfun(n,q)
        if kn is None: break
        S+=kn; n+=1
        if n>400000: break
    w=mp.sqrt(2/tau)
    # (T1) local linearity near turning: b_n/2-1 vs (n-n*)
    nstar=mp.log(xstar)/mp.log(q)
    # sample b/2-1 at n=floor(nstar)-2..+1
    n0=int(float(nstar))
    prof=[]
    for nn in range(max(0,n0-3),n0+2):
        prof.append((nn-float(nstar), float(bcoef(nn,q)/2-1)))
    return tau, S, I, w, xstar, nstar, prof

print("=== turning block: discrete sum k vs continuum WKB integral I; EM constant ===")
print("    (sum k - w) -> -3pi/4 ; (sum k - I) should isolate EM half-step etc.")
m3pi4=-3*mp.pi/4; mpi4=-mp.pi/4
for tau in [mp.mpf("0.02"),mp.mpf("0.01"),mp.mpf("0.005"),mp.mpf("0.002")]:
    tau,S,I,w,xstar,nstar,prof=analyze(tau)
    print(f"tau={float(tau):.4f}: sum k={mp.nstr(S,10)}  I(WKB)={mp.nstr(I,10)}  w={mp.nstr(w,8)}")
    print(f"    sum k - w = {mp.nstr(S-w,8)}  (->-3pi/4={mp.nstr(m3pi4,8)})")
    print(f"    sum k - I = {mp.nstr(S-I,8)}    I - w = {mp.nstr(I-w,8)}")
    print(f"    (I-w)/sqrt(tau)={mp.nstr((I-w)/mp.sqrt(tau),6)}   (sum k - I)/?  endpoint")
    print(f"    nstar={mp.nstr(nstar,6)}  local b/2-1 vs (n-nstar): {[(round(a,3),mp.nstr(b,3)) for a,b in prof]}")
    print()

# The continuum WKB integral I itself: does I = w + (something)*sqrt(tau) + const?
# And the discrete-minus-continuum (sum k - I) = EM endpoint series. The -3pi/4 splits as
# (I - w) [a sqrt(tau)->0 piece + maybe const] + (sum k - I)[EM half-step k_0/2 + ...].
print("=== is (I - w) -> 0 or a constant? (decides if -3pi/4 is from EM or from WKB integral) ===")
for tau in [mp.mpf("0.01")/2**i for i in range(5)]:
    tau,S,I,w,xstar,nstar,prof=analyze(tau)
    print(f"  tau={mp.nstr(tau,5)}: I-w={mp.nstr(I-w,8)}  (I-w)/sqrt(tau)={mp.nstr((I-w)/mp.sqrt(tau),6)}   sumk-I={mp.nstr(S-I,8)}")
