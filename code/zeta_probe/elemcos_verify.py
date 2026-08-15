#!/usr/bin/env python3
"""Verify the elementary derivation of lem:cos (paper2.tex, rem:elemcos).

Confirms, to ~10 digits:
  (1) the exact sinh-product form  g_j = (-1)^j e^{-j tau} sinh(tau/2)^j / prod_{k=1}^{2j} sinh(k tau/2)
      equals the j-th term of  S_e = sum_j (-2(1-q))^j q^{j(j+1)} / (q;q)_{2j};
  (2) S_e = cos W - (sqrt2/36) sqrt(tau) sin W + O(tau),  W = sqrt(2/tau) e^{-tau/2};
  (3) the equivalent w-form constant  c1 = 17 sqrt2 / 36 = 0.667823...  (eval at cos w = 0).

OOM-safe: single-thread mpmath, dps <= 60.
"""
import mpmath as mp
mp.mp.dps = 60


def se_series(tau):
    q = mp.e**(-tau); s = mp.mpf(0)
    for j in range(12000):
        p = mp.mpf(1)
        for k in range(1, 2 * j + 1):
            p *= (1 - q**k)
        term = (-2 * (1 - q))**j * q**(j * (j + 1)) / p
        s += term
        if j > 10 and abs(term) < mp.mpf(10)**(-66):
            break
    return s


def se_product(tau):
    s = mp.mpf(0)
    for j in range(12000):
        den = mp.mpf(1)
        for k in range(1, 2 * j + 1):
            den *= mp.sinh(k * tau / 2)
        gj = (-1)**j * mp.e**(-j * tau) * mp.sinh(tau / 2)**j / den
        s += gj
        if j > 10 and abs(gj) < mp.mpf(10)**(-66):
            break
    return s


s2_36 = mp.sqrt(2) / 36
c1 = 17 * mp.sqrt(2) / 36

print("(1)+(2)  S_e = cos W - (sqrt2/36) sqrt(tau) sin W + O(tau),  W = sqrt(2/tau) e^{-tau/2}")
print(f"{'tau':>9} {'series==product':>16} {'remainder R1':>14} {'R1/tau (bounded?)':>17}")
for tau in [mp.mpf('0.04'), mp.mpf('0.02'), mp.mpf('0.01'), mp.mpf('0.005'), mp.mpf('0.0025')]:
    W = mp.sqrt(2 / tau) * mp.e**(-tau / 2)
    Se = se_series(tau)
    diff_form = abs(Se - se_product(tau))
    R1 = Se - (mp.cos(W) - s2_36 * mp.sqrt(tau) * mp.sin(W))
    print(f"{mp.nstr(tau, 3):>9} {mp.nstr(diff_form, 3):>16} {mp.nstr(R1, 4):>14} {mp.nstr(R1 / tau, 5):>17}")

print()
print(f"(3)  c1 = 17 sqrt2/36 = {mp.nstr(c1, 12)}  (eval at w=(m+1/2)pi, cos w = 0)")
print(f"{'m':>4} {'tau_m':>12} {'S_e/((-1)^m sqrt.t)':>20} {'err':>11}")
for m in [5, 10, 20, 40]:
    w = (m + mp.mpf('0.5')) * mp.pi
    tau = 2 / w**2
    val = se_series(tau) / ((-1)**m * mp.sqrt(tau))
    print(f"{m:>4} {mp.nstr(tau, 5):>12} {mp.nstr(val, 10):>20} {mp.nstr(val - c1, 3):>11}")
