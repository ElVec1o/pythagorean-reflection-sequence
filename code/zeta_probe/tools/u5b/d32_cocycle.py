#!/usr/bin/env python3
# ROUTE D3.2 -- discrete Liouville-Green on the Sigma cocycle.
# Step 0: verify the recursion, Sigma as a cocycle solution, b_n, k_n, turning point.
#
# The 3-term recursion (cocycle):  y_{n+1} = (1+q^3 - 2(1-q) q^{2n+2}) y_n - q^3 y_{n-1}
# rescale z_n = q^{-3n/2} y_n  =>  z_{n+1} + z_{n-1} = b_n z_n,
#   b_n = q^{-3/2}(1+q^3) - 2(1-q) q^{-3/2} q^{2n+2}
#       = (q^{3/2}+q^{-3/2}) - 2(1-q) q^{2n+1/2}.
# As tau->0: q^{3/2}+q^{-3/2} -> 2 + (9/4)tau^2 ...; the n-dependent part is the well.
# k_n = arccos(b_n/2); oscillatory where |b_n|<2.
import mpmath as mp
mp.mp.dps = 40

def setup(tau):
    q = mp.e**(-tau)
    return q

def b(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))

# --- Verify: does the *actual Sigma summand* live on this recursion? ---
# Sigma = sum_k u_k with u_{k+1}/u_k = -2(1-q) q^{2k+3} / [(1-q^{2k+4})(1-q^{2k+3})].
# That is a 3-term contiguous relation; the homogeneous cocycle is the y-recursion.
# We check the b_n turning structure and that k_n ~ sqrt(2 tau) q^n in the bulk.

for tau in [mp.mpf("0.2"), mp.mpf("0.1"), mp.mpf("0.05"), mp.mpf("0.02")]:
    q = setup(tau)
    w = mp.sqrt(2/tau)
    # b_0:
    b0 = b(0, q)
    # find approx turning point n* where b_n = 2 (b decreasing in n for small n? check)
    # b_n = 2cosh(1.5 tau) - 2(1-q) q^{2n+1/2}; the second term ->0 as n->inf,
    # so b_n -> 2cosh(1.5 tau) > 2 as n->inf (classically forbidden at large n!).
    # And at n=0 the second term is biggest (most negative correction). So OSCILLATORY
    # region is SMALL n, turning point at LARGE n where b crosses 2.
    cosh_term = 2*mp.cosh(mp.mpf("1.5")*tau)
    # b_n = 2  =>  2(1-q) q^{2n+1/2} = cosh_term - 2
    rhs = cosh_term - 2
    # 2(1-q) q^{1/2} q^{2n} = rhs => q^{2n} = rhs/(2(1-q) q^{1/2})
    ratio = rhs/(2*(1-q)*q**mp.mpf("0.5"))
    if ratio > 0 and ratio < 1:
        nstar = mp.log(ratio)/(2*mp.log(q))
    else:
        nstar = mp.nan
    # k_n at n=0,1,2:
    ks = []
    for n in range(4):
        bn = b(n,q)
        if abs(bn) <= 2:
            ks.append(mp.acos(bn/2))
        else:
            ks.append(mp.nan)
    # predicted k_n ~ sqrt(2tau) q^n  -- check WKB wavenumber claim from MEMORY
    pred = [mp.sqrt(2*tau)*q**n for n in range(4)]
    print(f"tau={float(tau):.3f} w={float(w):.3f}  b0={mp.nstr(b0,8)}  2cosh(1.5t)={mp.nstr(cosh_term,8)}")
    print(f"   n* (b=2) = {mp.nstr(nstar,6)}   [memory log(8/(9tau))/(2tau)={mp.nstr(mp.log(8/(9*tau))/(2*tau),6)}]")
    print(f"   k_n (n=0..3): {[mp.nstr(x,6) for x in ks]}")
    print(f"   sqrt(2t)q^n : {[mp.nstr(x,6) for x in pred]}")
    print()
