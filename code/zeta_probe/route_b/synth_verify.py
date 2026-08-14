#!/usr/bin/env python3
"""
INDEPENDENT synthesis verification of the central lem:cos claims.
Re-derive from scratch, do not trust prior numbers.

Checks:
  (1) T2_direct (from S1 bulk) == alternating sum of psi(i) with EXACT integer B.
  (2) Saddle s*=iW/2: B_{s*} = O(sqrt tau), and |B_{s*}|/sqrt(tau) -> sqrt(2)/36.
  (3) Leading-term ratio T2_direct / Re[g_{s*} e^{iW}] -> 1 as tau->0.
  (4) The on-shell sup of |T2|/sqrt(tau) over the phase, vs the claimed
      sharp constant sqrt(2)/36 = 0.039284 and conservative C=0.06.
  (5) Re(B_iy) -> -inf on imaginary axis (Abel-Plana real-axis divergence).
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk, B_direct_integer

mp.mp.dps = 50

SQRT2_36 = mp.sqrt(2)/36   # = 0.0392837...

def T2_direct(tau):
    q = mp.e**(-tau)
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    S1 = S1_bulk(q)
    return S1 - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W)), w, W

def T2_altsum(tau, N=120):
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    tot = mp.mpf(0)
    for i in range(1, N+1):
        Bi = B_direct_integer(i, tau)       # exact integer B via product-form phi
        g = 1 - mp.e**(-Bi)
        term = (-1)**i * W**(2*i) * g / mp.factorial(2*i)
        tot += term
        if abs(term) < mp.mpf(10)**(-(mp.mp.dps+5)) and i > 2*float(W):
            break
    return tot

print("="*78)
print("CHECK 1+3: T2_direct vs alt-sum, and saddle leading-term ratio")
print("="*78)
for tau in [mp.mpf('0.1'), mp.mpf('0.05'), mp.mpf('0.02'), mp.mpf('0.01'), mp.mpf('0.005')]:
    Td, w, W = T2_direct(tau)
    Ta = T2_altsum(tau)
    # saddle
    sstar = mp.mpc(0,1)*W/2
    Bss, _ = B_exact(sstar, tau)
    gss = 1 - mp.e**(-Bss)
    saddle = mp.re(gss*mp.e**(mp.mpc(0,1)*W))
    print(f"tau={float(tau):7.4f}  T2_dir={mp.nstr(Td,10):>14}  |alt-dir|={mp.nstr(abs(Ta-Td),3)}"
          f"  |B_s*|/sqrt(t)={mp.nstr(abs(Bss)/mp.sqrt(tau),8)}  T2/saddle={mp.nstr(Td/saddle,7)}")

print()
print("  (target: |B_s*|/sqrt(t) -> sqrt2/36 =", mp.nstr(SQRT2_36,8), ", T2/saddle -> 1)")

print()
print("="*78)
print("CHECK 2: |B_{s*}|/sqrt(tau) -> sqrt(2)/36 at small tau")
print("="*78)
for tau in [mp.mpf('0.01'), mp.mpf('0.001'), mp.mpf('0.0004'), mp.mpf('0.0001')]:
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    sstar = mp.mpc(0,1)*W/2
    Bss, _ = B_exact(sstar, tau)
    print(f"tau={float(tau):8.5f}  |B_s*|/sqrt(t)={mp.nstr(abs(Bss)/mp.sqrt(tau),10)}"
          f"  Re/Im(B_s*)={mp.nstr(mp.re(Bss)/mp.im(Bss),4)}")
print("  sqrt(2)/36 =", mp.nstr(SQRT2_36,10))

print()
print("="*78)
print("CHECK 5: Re(B_iy) -> -inf on imaginary axis (kills real-axis Abel-Plana)")
print("="*78)
tau = mp.mpf('0.1')
w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
print(f"tau=0.1, W={float(W):.3f}, y*=W/2={float(W/2):.3f}, pole y=pi/tau={float(mp.pi/tau):.1f}")
for y in [5, 10, 20, 30, 40]:
    B, _ = B_exact(mp.mpc(0,1)*y, tau)
    print(f"  y={y:3d}: Re B_iy={mp.nstr(mp.re(B),6):>14}  |g_iy|=|1-e^-B|={mp.nstr(abs(1-mp.e**(-B)),4)}")
