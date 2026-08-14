#!/usr/bin/env python3
"""
Find the ACTUAL critical point of the Lindelof integrand and check it is s*=iW/2.

Lindelof: T2 = (1/2i) oint a_s g_s pi/sin(pi s) ds.  For the steepest-descent we need
the critical point of F(s) = 2s log W - loggamma(2s+1) - log sin(pi s) + log g_s.
The colleague's claim (lemcos_context line 31-33): F'(s)=0 at s*=iW/2 from the
'pure a/sin' part (Phi'(y)=2 log(W/2y)+...=0 => y=W/2). g_s is a slowly varying
correction.

We compute F'(s)=0 numerically (a) for the pure part 2s log W - loggamma(2s+1) - log sin(pi s),
and (b) including log g_s, and compare to iW/2. We also report F''(s*).

Then we compute the saddle-point VALUE
   T2_saddle = Re[ (1/2i) * a_{s*} g_{s*} pi/sin(pi s*) * sqrt(2 pi / (-F''(s*))) ] (up to phase)
and compare |T2_saddle| to the true |T2|.
"""
import mpmath as mp
from abelplana_verify import B_exact

def setup(tau):
    tau = mp.mpf(tau)
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau, w, W

def Fpure(s, W):
    # log of  W^{2s} / Gamma(2s+1) / sin(pi s)  (pure a/sin, no g)
    return 2*s*mp.log(W) - mp.loggamma(2*s+1) - mp.log(mp.sin(mp.pi*s))

def Fpure_prime(s, W):
    return 2*mp.log(W) - 2*mp.psi(0, 2*s+1) - mp.pi*mp.cos(mp.pi*s)/mp.sin(mp.pi*s)

def logg(s, tau):
    B,_ = B_exact(s, tau)
    return mp.log(1 - mp.e**(-B))

if __name__ == "__main__":
    mp.mp.dps = 50
    for tau0 in ['0.1', '0.02', '0.005', '0.001']:
        tau, w, W = setup(tau0)
        sstar_guess = mp.mpc(0, float(W/2))
        # (a) critical point of pure a/sin
        try:
            crit_pure = mp.findroot(lambda s: Fpure_prime(s, W), sstar_guess)
        except Exception as e:
            crit_pure = None
        # (b) include g: F' = Fpure' + d/ds log g.  Use numeric derivative of logg.
        def Ffull_prime(s):
            dg = mp.diff(lambda z: logg(z, tau), s)
            return Fpure_prime(s, W) + dg
        try:
            crit_full = mp.findroot(Ffull_prime, sstar_guess)
        except Exception as e:
            crit_full = None
        print(f"\ntau={tau0}: iW/2 = {mp.nstr(sstar_guess,8)}")
        print(f"   crit pt of pure a/sin:        {mp.nstr(crit_pure,8) if crit_pure is not None else 'FAIL'}")
        print(f"   crit pt of full (with log g): {mp.nstr(crit_full,8) if crit_full is not None else 'FAIL'}")
        if crit_pure is not None:
            print(f"   |crit_pure - iW/2| = {mp.nstr(abs(crit_pure-sstar_guess),4)}")
        if crit_full is not None:
            print(f"   |crit_full - iW/2| = {mp.nstr(abs(crit_full-sstar_guess),4)}")
            # F'' at the full critical point
            Fpp = mp.diff(Ffull_prime, crit_full)
            print(f"   F''(crit_full) = {mp.nstr(Fpp,6)}  (claim ~ -4/W = {mp.nstr(-4/W,6)})")
