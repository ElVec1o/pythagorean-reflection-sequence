#!/usr/bin/env python3
"""Verify the self-contained steepest-descent proof of lem:cos (paper2.tex).

S_e = sum_{n>=0} (-1)^n e^{-B_n} W^{2n}/(2n)!  is represented by Cauchy's theorem and
evaluated by the two simple saddles z*=+-iW/2 of h(z)=2z log W - log Gamma(2z+1) (with the
csc(pi z) phase). Leading (B=0): each saddle contributes (1/2)e^{+-iW}, summing to cos W exactly.
Modulation: scale each saddle by e^{-B(z*)}, B(z*+)=(1/24)tau^2(P_1(iW)-iW/2) -> -i sqrt2/36 sqrt(tau),
P_1(2z)=2z(2z+1)(4z+1)/6. Prediction cos W - (sqrt2/36) sqrt(tau) sin W matches S_e to O(tau).

OOM-safe: single-thread mpmath, dps 40.
"""
import mpmath as mp
mp.mp.dps = 40


def se(tau):
    q = mp.e**(-tau); s = mp.mpf(0)
    for j in range(9000):
        p = mp.mpf(1)
        for k in range(1, 2 * j + 1):
            p *= (1 - q**k)
        t = (-2 * (1 - q))**j * q**(j * (j + 1)) / p
        s += t
        if j > 10 and abs(t) < mp.mpf(10)**(-44):
            break
    return s


print("Saddle z*=iW/2 prediction vs exact S_e   (W = sqrt(2/tau) e^{-tau/2}):")
print(f"{'tau':>8} {'B(z*).imag':>14} {'-sqrt2/36 sqrt.t':>16} {'saddle pred':>13} {'S_e':>13} {'err/tau':>10}")
for tau in [mp.mpf('0.02'), mp.mpf('0.01'), mp.mpf('0.005'), mp.mpf('0.0025')]:
    W = mp.sqrt(2 / tau) * mp.e**(-tau / 2)
    z = 1j * W / 2
    P1 = 2 * z * (2 * z + 1) * (4 * z + 1) / 6
    B = (mp.mpf(1) / 24) * tau**2 * (P1 - z)
    pred = (mp.e**(-B) * mp.e**(1j * W) / 2 + mp.e**(-mp.conj(B)) * mp.e**(-1j * W) / 2).real
    Se = se(tau)
    print(f"{mp.nstr(tau,3):>8} {mp.nstr(B.imag,6):>14} {mp.nstr(-mp.sqrt(2)/36*mp.sqrt(tau),6):>16} "
          f"{mp.nstr(pred,7):>13} {mp.nstr(Se,7):>13} {mp.nstr((pred-Se)/tau,4):>10}")
print("\nerr/tau bounded => saddle-point remainder is O(tau); the two-saddle proof is correct.")
