#!/usr/bin/env python3
r"""
DIAGNOSTIC: does the FULL defining sum  T2 = sum_{i>=1} (-1)^i g_i a_i  reproduce the
closed form T2_closed = S1 - (1-cos w) - (cos w - cos W) ?  And does the windowed sum
match the full sum to within the tail bound?

If the full sum != closed form, the whole Abel-Plana identification is mis-stated and the
crux test is meaningless.  We check this FIRST, to high precision, with generous IMAX.
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk

mp.mp.dps = 60
I = mp.mpc(0, 1)

def setup(tau):
    tau = mp.mpf(tau); q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau, q, w, W

def T2_closed(tau):
    tau, q, w, W = setup(tau)
    S1 = S1_bulk(q)
    return S1 - (1 - mp.cos(w)) - (mp.cos(w) - mp.cos(W))

def a_i(i, W): return W**(2*i)/mp.factorial(2*i)
def g_i(i, tau):
    B, _ = B_exact(mp.mpc(i), tau)
    return 1 - mp.e**(-mp.re(B))

print("="*96)
print("DIAGNOSTIC: full defining sum  vs  closed form  (and windowed vs full)")
print("="*96)
print(f"{'tau':>8} {'IMAX':>5} {'T2_closed':>17} {'T2_fullsum':>17} {'|full-closed|':>14} {'last term':>12}")
for tau in [mp.mpf('0.05'), mp.mpf('0.02'), mp.mpf('0.01'), mp.mpf('0.005')]:
    tau, q, w, W = setup(tau)
    T2c = T2_closed(tau)
    IMAX = int(float(W)) + int(14*float(mp.sqrt(W))) + 60
    tot = mp.mpf(0); last = mp.mpf(0)
    for i in range(1, IMAX+1):
        term = (-1)**i * g_i(i, tau) * a_i(i, W)
        tot += term
        last = abs(term)
    print(f"{float(tau):>8} {IMAX:>5} {mp.nstr(T2c,12):>17} {mp.nstr(tot,12):>17} "
          f"{mp.nstr(abs(tot-T2c),5):>14} {mp.nstr(last,4):>12}")

# Also: is g_i defined with B_i = B_{i}, i.e. does the i-th term use B at i or at i-1?
# The paper's T2 = sum_{i>=1} (-1)^i W^{2i}/(2i)! (1 - e^{-B_i}).  Check both B_i and B_{i-1}.
print("\n--- sensitivity: does the term use B_i or B_{i-1}? (should be B_i per eq:T1T2) ---")
print(f"{'tau':>8} {'closed':>15} {'sum w/ B_i':>15} {'sum w/ B_{i-1}':>16} {'sum w/ B_{i+1}':>16}")
for tau in [mp.mpf('0.02'), mp.mpf('0.005')]:
    tau, q, w, W = setup(tau)
    T2c = T2_closed(tau)
    IMAX = int(float(W)) + int(14*float(mp.sqrt(W))) + 60
    def S(shift):
        tot = mp.mpf(0)
        for i in range(1, IMAX+1):
            ii = i + shift
            if ii < 0: continue
            if ii == 0:
                g = mp.mpf(0)  # B_0 = 0 => g_0 = 0
            else:
                B, _ = B_exact(mp.mpc(ii), tau); g = 1 - mp.e**(-mp.re(B))
            tot += (-1)**i * g * a_i(i, W)
        return tot
    print(f"{float(tau):>8} {mp.nstr(T2c,10):>15} {mp.nstr(S(0),10):>15} {mp.nstr(S(-1),10):>16} {mp.nstr(S(1),10):>16}")
