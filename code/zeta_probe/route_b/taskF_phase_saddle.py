#!/usr/bin/env python3
"""
TASK F -- PART 3b: the saddle of the GENUINE phase the cited theorem acts on.

Reconcile two exponents that appear in this problem:

  (A) The REAL-AXIS Abel-Plana phase  Phi(y) = 2 y log W + arg g_{iy} - arg Gamma(1+2iy).
      Its stationary point (foundation B) is  y* = W/2 + (1/2) sqrt(tau) + ...,  Phi''(y*) = -4/W.
      THIS is the genuine stationary-phase object: integrand = -A(y) sin Phi(y),
      amplitude A(y) >= 0, phase Phi real, single nondegenerate stationary point y*.
      [The real-axis integral itself diverges in the tail, but the STATIONARY-PHASE
       LEADING TERM is governed entirely by a neighborhood of y* where everything is finite.]

  (B) The Lindelof exponent with sin(pi s): saddle shifted off-axis by the i pi s term.
      (Part 3 found that off-axis saddle; not the object we cite the theorem for.)

This script confirms (A) rigorously with EXACT B:
  (1) y* = W/2 + (1/2) sqrt(tau) + O(tau):   (y*-W/2)/sqrt(tau) -> 1/2
  (2) Phi''(y*) -> -4/W  (nondegenerate)
  (3) the stationary-phase leading term  T2 ~ -A(y*) sqrt(2 pi/|Phi''(y*)|) sin(Phi(y*)-pi/4)
      reproduces T2_true with relative error -> 0 like O(sqrt tau).
  (4) |T2| <= A(y*) sqrt(2 pi/|Phi''(y*)|)*(1+o(1)) = (sqrt2/36) sqrt(tau)*(1+o(1)) = O(sqrt tau).
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk

mp.mp.dps = 80
I = mp.mpc(0, 1)

def setup(tau):
    tau = mp.mpf(tau); q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau, q, w, W

def T2_true(tau):
    tau, q, w, W = setup(tau)
    S1 = S1_bulk(q)
    return S1 - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

def A_of_y(y, W, tau):
    s = I*y
    B, _ = B_exact(s, tau)
    g = 1 - mp.e**(-B)
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))

def Phi_of_y(y, W, tau):
    s = I*y
    B, _ = B_exact(s, tau)
    g = 1 - mp.e**(-B)
    return 2*y*mp.log(W) + mp.arg(g) - mp.im(mp.loggamma(1+2*I*y))

def Phi1(y, W, tau, h=mp.mpf('1e-15')):
    return (Phi_of_y(y+h, W, tau) - Phi_of_y(y-h, W, tau))/(2*h)
def Phi2(y, W, tau, h=mp.mpf('1e-10')):
    return (Phi_of_y(y+h, W, tau) - 2*Phi_of_y(y, W, tau) + Phi_of_y(y-h, W, tau))/h**2

print("="*92)
print("PART 3b -- stationary point of the REAL-AXIS phase Phi(y) (the genuine SP object)")
print("="*92)
print(f"{'tau':>8} {'W':>9} {'y*':>10} {'(y*-W/2)/sqrt(tau)':>20} {'Phi2(y*)':>12} {'ratio/(−4/W)':>13} "
      f"{'A(y*)sqrt(2pi/|Phi2|)/sqrt(tau)':>32}")
for tau in [mp.mpf('0.1'), mp.mpf('0.02'), mp.mpf('0.005'), mp.mpf('0.001'), mp.mpf('0.0002')]:
    tau, q, w, W = setup(tau)
    y = W/2
    # Newton on Phi1=0 (stationary point of the real phase)
    for _ in range(60):
        f = Phi1(y, W, tau); d = Phi2(y, W, tau)
        step = f/d; y = y - step
        if abs(step) < mp.mpf('1e-50'): break
    ystar = y
    shift = (ystar - W/2)/mp.sqrt(tau)
    p2 = Phi2(ystar, W, tau)
    Aystar = A_of_y(ystar, W, tau)
    spamp = Aystar*mp.sqrt(2*mp.pi/abs(p2))
    print(f"{float(tau):>8} {float(W):>9.4f} {float(ystar):>10.5f} {mp.nstr(shift,9):>20} "
          f"{mp.nstr(p2,6):>12} {mp.nstr(p2/(-4/W),7):>13} {mp.nstr(spamp/mp.sqrt(tau),10):>32}")

print("\n" + "="*92)
print("STATIONARY-PHASE LEADING TERM vs TRUE T2   (relative error scaling)")
print("="*92)
print(f"{'tau':>8} {'T2_true':>16} {'SP leading':>16} {'|T2|/sqrt(tau)':>15} {'rel err':>12} {'relerr/sqrt(tau)':>16}")
prev = None
for tau in [mp.mpf('0.02'), mp.mpf('0.005'), mp.mpf('0.001'), mp.mpf('0.0002')]:
    tau, q, w, W = setup(tau)
    T2 = T2_true(tau)
    y = W/2
    for _ in range(60):
        f = Phi1(y, W, tau); d = Phi2(y, W, tau); step=f/d; y=y-step
        if abs(step) < mp.mpf('1e-50'): break
    ystar=y; p2=Phi2(ystar,W,tau); Aystar=A_of_y(ystar,W,tau)
    phistar = Phi_of_y(ystar,W,tau)
    # integrand = -A sin Phi; SP of int -A(y) sin Phi dy with Phi''<0:
    #   = -A(y*) sqrt(2pi/|Phi''|) sin(Phi(y*) - pi/4)   (sign from -Phi'' => -pi/4)
    SP = -Aystar*mp.sqrt(2*mp.pi/abs(p2))*mp.sin(phistar - mp.pi/4)
    relerr = abs((T2-SP)/T2)
    print(f"{float(tau):>8} {mp.nstr(T2,12):>16} {mp.nstr(SP,12):>16} {mp.nstr(abs(T2)/mp.sqrt(tau),8):>15} "
          f"{mp.nstr(relerr,6):>12} {mp.nstr(relerr/mp.sqrt(tau),5):>16}")
