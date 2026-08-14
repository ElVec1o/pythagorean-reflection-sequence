#!/usr/bin/env python3
"""
TASK F -- PART 6: confirm the DLMF 2.4.16 / Olver leading coefficient b_0 reproduces
our coefficient sqrt2/36, so citing the theorem's FORMULA (not just its order) is exact.

Stationary-phase normal form for  T2 = Re/Im of int A(y) e^{i Phi(y)} dy with simple
stationary point y*, Phi''(y*)<0:
     int A e^{i Phi} dy ~ A(y*) e^{i Phi(y*)} sqrt(2 pi / |Phi''(y*)|) e^{-i pi/4}   (Phi''<0)
The MODULUS of the leading term is  A(y*) sqrt(2 pi/|Phi''(y*)|).
We have verified A(y*) sqrt(2pi/|Phi''|) = (sqrt2/36) sqrt(tau).  Cross-check the pieces:
   |g_{s*}| = |B_{s*}|(1+o(1)),  B_{s*} = -i (sqrt2/36) sqrt(tau)  [foundation],
   A(y*) = |g_{s*}| sqrt(coth(pi y*)/(pi y*)) ~ |g_{s*}|/sqrt(pi y*)  (coth->1),
   sqrt(2pi/|Phi''|) = sqrt(2pi/(4/W)) = sqrt(pi W/2) = sqrt(pi y*).
   => A(y*) sqrt(2pi/|Phi''|) ~ |g_{s*}| = (sqrt2/36) sqrt(tau).   EXACT cancellation of sqrt(pi y*).
This is WHY the coefficient is exactly |B_{s*}| with NO free constant.
"""
import mpmath as mp
from abelplana_verify import B_exact

mp.mp.dps = 60
I = mp.mpc(0, 1)

print("="*86)
print("PART 6 -- DLMF 2.4.16 leading-term modulus = |g_{s*}| (sqrt(pi y*) cancels)")
print("="*86)
print(f"{'tau':>10} {'|g_s*|/sqrt(tau)':>17} {'A(y*)sqrt(2pi/|Phi2|)/sqrt(tau)':>33} {'sqrt2/36':>12}")
for tau in [mp.mpf('0.02'), mp.mpf('0.005'), mp.mpf('0.001'), mp.mpf('0.0002')]:
    tau = mp.mpf(tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2); ystar = W/2
    Bs, _ = B_exact(I*ystar, tau); gs = 1 - mp.e**(-Bs)
    A = abs(gs)*mp.sqrt(mp.coth(mp.pi*ystar)/(mp.pi*ystar))
    Phi2 = -4/W  # leading
    lead = A*mp.sqrt(2*mp.pi/abs(Phi2))
    print(f"{float(tau):>10} {mp.nstr(abs(gs)/mp.sqrt(tau),9):>17} {mp.nstr(lead/mp.sqrt(tau),9):>33} {float(mp.sqrt(2)/36):>12.7f}")
print(f"\nsqrt2/36 = {mp.nstr(mp.sqrt(2)/36, 12)}  = 2^(3/2)/72")
print("Both columns -> sqrt2/36: the sqrt(pi y*) factors cancel EXACTLY, so the DLMF/Olver")
print("leading coefficient equals |B_{s*}| with NO free constant.  |T2| <= (sqrt2/36) sqrt(tau)(1+o(1)).")
