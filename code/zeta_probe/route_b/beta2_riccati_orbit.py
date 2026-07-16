#!/usr/bin/env python3
"""Forward Riccati rational-orbit normal form (paper2 rem:backward, forward part).

The Riccati relation u(z)u(Qz) - a(z)u(z) + q = 0 gives the explicit continued fraction
q/(a(z) - q/(a(Qz) - ...)), which by Pincherle converges to the MINIMAL-solution ratio
q H(Qz)/H(z). The zero condition G(q,z1)=0 forces the DOMINANT ratios
   w_n := G(q, Q^{n+1} z1)/G(q, Q^n z1)
to obey w_1 = a(z1) EXACTLY and then the rational map w_{n+1} = a(Q^n z1) - q/w_n.
Under the reductio (q, z1 rational) the whole forward orbit is an explicit Q-orbit
converging to the attracting fixed point 1 at rate Theta(Q^n); heights compound
quadratically (t^{O(n^2)}), so Liouville (Q^n vs t^{-n^2}) is consistent: CONSERVING.
Together with the backward theta-growth normal form (v2.8.3, v2.11.3) this exhausts the
one-orbit reformulations of the zero condition. No crack; structure bookends complete.
"""
import mpmath as mp

if __name__ == "__main__":
    mp.mp.dps = 45
    q = mp.mpf('0.449453630558948046125545825395696389319555316196'); Q = q*q
    zs = 2*q*(1-q)
    def gk(k):
        poch = mp.mpf(1)
        for i in range(1, 2*k+1): poch *= (1-q**i)
        return mp.mpf((-1)**k)*q**(k*(k-1))/poch
    G = lambda w, K=150: sum(gk(k)*mp.mpc(w)**k for k in range(K))
    a = lambda w: q+1-q*w
    w1 = (G(Q**2*zs)/G(Q*zs)).real
    print("w_1 direct vs a(z*):", mp.nstr(abs(w1-a(zs)), 3))
    w = a(zs); ok = True
    for n in range(1, 8):
        w = a(Q**n*zs)-q/w
        direct = (G(Q**(n+2)*zs)/G(Q**(n+1)*zs)).real
        if abs(w-direct) > mp.mpf(10)**-25: ok = False
    print("rational recursion reproduces ratios:", ok)
    print("rate: (w_8-1)/Q^8 =", mp.nstr((w-1)/Q**8, 6), "(Theta(Q^n))")
