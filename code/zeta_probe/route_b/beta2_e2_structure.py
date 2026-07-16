#!/usr/bin/env python3
"""Orbit collapse + the E2-coupled jet structure (paper2 prop:nofinitering, corrected).

(i) ORBIT COLLAPSE: along the diagonal z*(q) = 2q(1-q) the z-recurrence has coefficients
    a(Q^j z*) = q+1-q Q^j z* in Q(q), so u_{j+2} = a(Q^j z*) u_{j+1} - q u_j: EVERY orbit value
    u_j = G(q, Q^j z*) lies in span_{Q(q)}{u_0, u_1}. The sigma-orbit is NOT the obstruction to a
    finite differential ring. (An earlier version of prop:nofinitering attributed the failure to
    orbit spread -- 15th caught error of the arc; conclusion unaffected, mechanism corrected.)

(ii) E2-COUPLED STRUCTURE: delta G = (theta^2 - theta) G + phi(q) G - T, with
     phi(q) = sum_{i>=1} i q^i/(1-q^i)   (quasimodular: 24 phi = 1 - E_2 up to normalization),
     T = sum_k (-1)^k [sum_{i>2k} i q^i/(1-q^i)] q^{k(k-1)} z^k/(q;q)_{2k}  (weights O(k q^{2k})).
     Since [delta, theta] = 0, each delta raises the z-jet by TWO: delta^n S involves
     theta^{2n} G|_{z=z*} with unit leading coefficient.

(iii) THE ACTUAL OBSTRUCTION: the z-jet tower {theta^m G} -- algebraically independent over C(z) by
     the differential-transcendence theorem. Nesterenko closes IFF S is differentially algebraic in
     q (no supporting structure; no ADE order<=4 deg<=5 over 800 terms).
"""
import mpmath as mp

if __name__ == "__main__":
    mp.mp.dps = 40
    q = mp.mpf('0.37'); Q = q*q; zs = 2*q*(1-q)

    def G(z, K=160):
        t = mp.mpf(0); poch = mp.mpf(1)
        for k in range(K):
            if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
            term = mp.mpf((-1)**k)*q**(k*(k-1))*mp.mpc(z)**k/poch
            t += term
            if k > 10 and abs(term) < mp.mpf(10)**-45: break
        return t
    u = [G(Q**j*zs) for j in range(6)]
    ok = all(abs(u[j+2]-((q+1-q*Q**j*zs)*u[j+1]-q*u[j])) < mp.mpf(10)**-32 for j in range(4))
    print("(i) orbit collapse u_{j+2} = a_j u_{j+1} - q u_j:", ok)

    PHI = sum(i*q**i/(1-q**i) for i in range(1, 400))
    def gk(k):
        poch = mp.mpf(1)
        for i in range(1, 2*k+1): poch *= (1-q**i)
        return mp.mpf((-1)**k)*q**(k*(k-1))/poch
    partial = lambda k: sum(i*q**i/(1-q**i) for i in range(1, 2*k+1))
    z0 = mp.mpf('0.51')
    dG = sum(gk(k)*(k*(k-1)+partial(k))*z0**k for k in range(80))
    t2t = sum(gk(k)*k*(k-1)*z0**k for k in range(80))
    T = sum(gk(k)*(PHI-partial(k))*z0**k for k in range(80))
    print("(ii) deltaG - [(th^2-th)G + phi G - T] =", mp.nstr(abs(dG-(t2t+PHI*G(z0)-T)), 4))
