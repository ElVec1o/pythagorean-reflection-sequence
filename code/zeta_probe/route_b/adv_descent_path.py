#!/usr/bin/env python3
"""
Does a convergent steepest-descent contour through the saddle EXIST?

The Lindelof integrand h(s) = a_s g_s pi/sin(pi s). For a saddle-point bound to give
|T2|=O(sqrt tau) RIGOROUSLY we need a contour C (homotopic to the pole-encircling
contour) on which |h| is dominated by its value at the saddle and decays on both
tails, with controlled off-saddle integral.

Map the magnitude |h(sigma+i eta)| on a grid to SEE the descent geometry:
 - along Re=const lines (does it decay as eta-> large? NO, g blows up)
 - along Im=const lines (does it decay as sigma grows? the 1/sin(pi s)~e^{-pi|eta|}... )
The question: is there a saddle (col) with TWO descending valleys forming a usable path?
"""
import mpmath as mp
from abelplana_verify import B_exact

def logabs_h(s, W, tau):
    B,_ = B_exact(s, tau)
    g = 1 - mp.e**(-B)
    if abs(g) == 0: return mp.mpf('-inf')
    la = 2*s*mp.log(W) - mp.loggamma(2*s+1)     # log a_s
    return mp.re(la) + mp.log(abs(g)) + mp.log(mp.pi) - mp.log(abs(mp.sin(mp.pi*s)))

if __name__ == "__main__":
    mp.mp.dps = 40
    tau = mp.mpf('0.02'); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    ystar = float(W/2)
    print(f"tau={float(tau)}, W={float(W):.3f}, saddle near (0, {ystar:.3f})")
    print("Map log|h| over (sigma, eta). Looking for a col with two descending valleys.")
    print()
    sigmas = [mp.mpf(x)/2 for x in range(0, 17)]     # 0..8
    etas = [mp.mpf(ystar)+mp.mpf(d) for d in [-4,-2,0,2,4,6,8,10,14,20]]
    # header
    hdr = "  eta\\sig " + "".join(f"{float(s):7.1f}" for s in sigmas)
    print(hdr)
    for eta in etas:
        row = f"  {float(eta):7.2f} "
        for sig in sigmas:
            try:
                v = logabs_h(mp.mpc(sig, eta), W, tau)
                row += f"{float(v):7.2f}"
            except Exception:
                row += "   nan "
        print(row)
    print()
    print("Reading: at FIXED eta, does log|h| DECREASE as sigma grows (escape sideways)?")
    print("         at FIXED sigma>0, does log|h| eventually DECREASE as eta grows past saddle?")
    print("If |h| only ever GROWS upward at every sigma, no descent valley closes the contour.")
