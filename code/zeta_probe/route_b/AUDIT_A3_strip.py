"""
AUDIT of lem:Bbounded (A3). Two questions:
 Q1: Is the LITERAL bound  Re B_s >= -(sqrt2/18) sqrt(tau)  true on the OPERATIVE contour dR
     (Re s >= 1/2, |Im s| = W/2 and Re s = 1/2)? Or only with a (1+o(1)) / minus C2 tau^{3/2}?
 Q2: On dR the relevant bound for |g_s|<=2 is only Re B_s >= -log(2) ~ -0.693. Since
     -(sqrt2/18) sqrt(tau) -> 0, ANY uniform constant slightly below 0 suffices for |g_s|<=2.
     So check: what is the actual inf of Re B_s over dR, and is it > -log 2 for small tau?
We scan the full boundary dR (both horizontals to large Re s, and the left edge), at high dps.
"""
import mpmath as mp
from lemcos_Bstrip import B_gamma
mp.mp.dps = 35

def scan(tau, Kg=3000):
    W = mp.sqrt(2/tau)*mp.e**(-tau/2)
    st = mp.sqrt(tau)
    bound = -mp.sqrt(2)/18*st
    mins = mp.mpf('1e9'); argmin=None
    # left edge Re s = 1/2
    for k in range(0, 121):
        t = -W/2 + W*k/120
        s = mp.mpc(0.5, float(t)); r = mp.re(B_gamma(s, tau, Kg))
        if r < mins: mins=r; argmin=('left', float(0.5), float(t))
    # horizontals Im s = +-W/2, sigma in [1/2, 3W]
    smax = float(3*W)+2
    nn = 160
    for sign in (1,-1):
        for k in range(0, nn+1):
            sig = 0.5 + (smax-0.5)*k/nn
            s = mp.mpc(sig, float(sign*W/2)); r = mp.re(B_gamma(s, tau, Kg))
            if r < mins: mins=r; argmin=('horiz', sig, float(sign*W/2))
    return W, bound, mins, argmin

print(f"{'tau':>8} {'W':>8} {'-sqrt2/18 st':>13} {'inf Re B on dR':>15} {'inf/st':>9} {'> -log2?':>9} {'>= bound?':>9} {'argmin':>22}")
for taus in ['0.05','0.02','0.01','0.005','0.002']:
    tau = mp.mpf(taus)
    W, bound, mins, argmin = scan(tau)
    st = mp.sqrt(tau)
    print(f"{taus:>8} {float(W):>8.3f} {mp.nstr(bound,5):>13} {mp.nstr(mins,6):>15} "
          f"{mp.nstr(mins/st,5):>9} {str(mins> -mp.log(2)):>9} {str(mins>=bound):>9} "
          f"{argmin[0]+' sig='+mp.nstr(argmin[1],4):>22}")
print()
print("VERDICT LOGIC: For |g_s|<=2 we only need Re B_s >= -log2 = -0.6931 on dR.")
print("If 'inf Re B' stays comfortably above -log2 for all small tau (it ->0^-), then |g_s|<=2 is")
print("RIGOROUS without needing the literal -(sqrt2/18)sqrt(tau) constant -- a strictly weaker,")
print("robust-to-the-o(1) requirement. Whether '>= bound?' is True only matters for the SHARP")
print("constant, not for lem:cos itself.")
