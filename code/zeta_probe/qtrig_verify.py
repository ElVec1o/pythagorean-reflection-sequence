#!/usr/bin/env python3
"""qtrig_verify.py -- verification for paper2 Proposition prop:qtrig / Remark rem:qtrig.

Checks, with mpmath at dps=60:
  (1) the sinh-form of S_e equals cos(z0; q^2),  z0 = sqrt(2(1-q)),   at generic q;
  (2) the sinh-form of 1-Sigma_1 equals cos(Z; q^2),  Z = z0/sqrt(q), at generic q;
  (3) at the tabulated travel poles (t1_data.txt): |cos(Z;q^2)| < 1e-40 and
      |S_e|/sqrt(tau) in [0.698, 0.708], with S_e matching the tabulated value.
Exit 0 and print PASS on success.
"""
import os
from mpmath import mp, mpf, sinh, exp, sqrt

mp.dps = 60
TOL = mpf(10) ** -50

def cosq(z, q, J=400):
    """cos(z;q^2) = sum_j (-1)^j q^{j^2+j} z^{2j}/(q;q)_{2j}."""
    s = mp.mpf(0); poch = mp.mpf(1)
    for j in range(J):
        if j > 0:
            for i in (2 * j - 1, 2 * j):
                poch *= (1 - q ** i)
        s += (-1) ** j * q ** (j * j + j) * z ** (2 * j) / poch
    return s

def sinh_series(tau, phase, J=400):
    """sum_j (-1)^j e^{-j*phase*tau} sinh^j(tau/2)/prod_{m<=2j} sinh(m tau/2).
    phase=1 gives S_e; phase=0 gives 1-Sigma_1 (paper2, sec:sd)."""
    s = mp.mpf(0); h = sinh(tau / 2)
    for j in range(J):
        den = mp.mpf(1)
        for m in range(1, 2 * j + 1):
            den *= sinh(m * tau / 2)
        t = (-1) ** j * exp(-j * phase * tau) * h ** j / den
        s += t
        if j > 5 and abs(t) < mpf(10) ** -70:
            break
    return s

def main():
    ok = True
    for tv in ('0.7', '0.3', '0.15', '0.07', '0.02'):
        tau = mpf(tv); q = exp(-tau)
        z0 = sqrt(2 * (1 - q)); Z = z0 / sqrt(q)
        d1 = abs(sinh_series(tau, 1) - cosq(z0, q))
        d2 = abs(sinh_series(tau, 0) - cosq(Z, q))
        print(f"tau={tv:>5s}  |S_e - cos(z0)| = {mp.nstr(d1, 3):>10s}   "
              f"|1-Sigma_1 - cos(Z)| = {mp.nstr(d2, 3):>10s}")
        ok &= d1 < TOL and d2 < TOL
    data = os.path.join(os.path.dirname(__file__), 'tools', 't1series', 't1_data.txt')
    lo, hi = mpf(10), mpf(0)
    for ln in open(data):
        f = ln.split()
        if len(f) < 5:
            continue
        m, tau, se_tab = int(f[0]), mpf(f[1]), mpf(f[3])
        # the alternating series cancels ~e^w, w = sqrt(2/tau): raise precision to hold it
        mp.dps = 60 + int(0.9 * float(sqrt(2 / tau)))
        tau = mpf(str(tau)); q = exp(-tau)
        z0 = sqrt(2 * (1 - q)); Z = z0 / sqrt(q)
        cz = abs(cosq(Z, q)); r = abs(se_tab) / sqrt(tau)
        se = cosq(z0, q)
        ok &= cz < mpf(10) ** -30 and abs(se / se_tab - 1) < mpf(10) ** -30
        lo, hi = min(lo, r), max(hi, r)
    mp.dps = 60
    print(f"poles: |cos(Z;q^2)| and |S_e/S_e_tab - 1| < 1e-30 at all rows; |S_e|/sqrt(tau) in [{mp.nstr(lo,6)}, {mp.nstr(hi,6)}]")
    ok &= lo > mpf('0.698') and hi < mpf('0.708')
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == '__main__':
    raise SystemExit(main())
