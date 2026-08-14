#!/usr/bin/env python3
"""
The CRITICAL contested question: is sup_w |T2|/sqrt(tau) <= sqrt(2)/36 (an upper
bound) or does it EXCEED sqrt(2)/36 (so sqrt2/36 is only the leading coefficient)?

The two error-bound colleagues disagree:
  - Task-D/F author: "C=0.06 conservative; sharp C0=sqrt2/36 is an upper bound asymptotically"
  - Adversary: "sqrt2/36 is EXCEEDED at every finite tau (ratio 1.371..1.004 ->1 from ABOVE),
    so it is the leading coeff NOT an upper bound; |T2|<=(sqrt2/36)sqrt(tau) is FALSE."

We resolve by DENSE on-shell phase scan: for each tau, sweep w around the on-shell
value (w=sqrt(2/tau)) -- but w is FIXED by tau on-shell. So 'sweeping the phase' means
scanning tau finely (each tau gives a different W mod 2pi). Compute realized
sup_tau |T2(tau)|/sqrt(tau) over a dense tau grid in several decades.
"""
import mpmath as mp
from abelplana_verify import S1_bulk

mp.mp.dps = 40
SQRT2_36 = mp.sqrt(2)/36

def ratio(tau):
    q = mp.e**(-tau)
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    S1 = S1_bulk(q)
    T2 = S1 - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))
    return abs(T2)/mp.sqrt(tau)

# dense scan over several decades
print("Dense on-shell scan of |T2|/sqrt(tau):")
print(f"  sqrt(2)/36 = {mp.nstr(SQRT2_36,8)}")
print()
decades = [
    ("0.5..0.05",  mp.mpf('0.05'), mp.mpf('0.5'),   400),
    ("0.05..0.005",mp.mpf('0.005'),mp.mpf('0.05'),  400),
    ("0.005..5e-4",mp.mpf('0.0005'),mp.mpf('0.005'),300),
]
gsup = mp.mpf(0); gsup_tau = None
for name, lo, hi, n in decades:
    sup = mp.mpf(0); sup_tau = None
    for j in range(n+1):
        tau = lo*(hi/lo)**(mp.mpf(j)/n)
        r = ratio(tau)
        if r > sup: sup, sup_tau = r, tau
    print(f"  range {name:14s}: sup |T2|/sqrt(t) = {mp.nstr(sup,8)} at tau={mp.nstr(sup_tau,5)}"
          f"  (ratio to sqrt2/36 = {mp.nstr(sup/SQRT2_36,5)})")
    if sup > gsup: gsup, gsup_tau = sup, sup_tau

# zoom near the suspected global peak ~ tau 0.2-0.25
print()
print("Zoom near global peak (tau in 0.15..0.30, 2000 pts):")
sup = mp.mpf(0); sup_tau = None
lo, hi, n = mp.mpf('0.15'), mp.mpf('0.30'), 2000
for j in range(n+1):
    tau = lo + (hi-lo)*mp.mpf(j)/n
    r = ratio(tau)
    if r > sup: sup, sup_tau = r, tau
print(f"  GLOBAL sup |T2|/sqrt(t) = {mp.nstr(sup,8)} at tau={mp.nstr(sup_tau,6)}")
print(f"  -> ratio to sqrt2/36 = {mp.nstr(sup/SQRT2_36,6)}  (so sqrt2/36 is { 'EXCEEDED' if sup>SQRT2_36 else 'an upper bound'})")
print(f"  -> is C=0.06 a valid bound? {sup} <= 0.06 ? {'YES' if sup<=mp.mpf('0.06') else 'NO'}  (headroom {mp.nstr(mp.mpf('0.06')/sup,5)}x)")

# small-tau envelope: does it ever exceed the moderate-tau peak?
print()
print("Small-tau envelope (tau in 1e-4..1e-3, 500 pts): does it exceed the peak?")
sup = mp.mpf(0); sup_tau=None
lo, hi, n = mp.mpf('1e-4'), mp.mpf('1e-3'), 500
for j in range(n+1):
    tau = lo*(hi/lo)**(mp.mpf(j)/n)
    r = ratio(tau)
    if r > sup: sup, sup_tau = r, tau
print(f"  sup in [1e-4,1e-3] = {mp.nstr(sup,8)} at tau={mp.nstr(sup_tau,5)} (ratio to sqrt2/36 = {mp.nstr(sup/SQRT2_36,6)})")
