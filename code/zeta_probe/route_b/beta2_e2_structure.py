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


# ============================================================================
# LAMBERT-ORBIT IDENTITY (v2.11.2, paper2 prop:nofinitering(ii), verified 41 digits):
#   T(q,z) = sum_{d>=1} [2q^d/(1-q^d)] (theta G)(q, q^{2d} z)
#          + sum_{d>=1} [q^d/(1-q^d)^2]  G(q, q^{2d} z)
# Proof: expand tail_k = sum_{i>2k} i q^i/(1-q^i) = sum_d sum_{i>2k} i q^{id}, swap sums
# (absolutely convergent), and evaluate sum_{i>2k} i x^i = x^{2k+1}[(2k+1)-2kx]/(1-x)^2 at
# x = q^d; the k-sums reassemble into G and theta-G at the orbit points q^{2d} z.
# MEANING: the entire non-modular content of delta G is an E_2-weighted trace of the module
# over the forward sigma-orbit. On the diagonal the orbit collapses to 4 generators but the
# collapse coefficients become transfer-product series (not rational): the identity RELOCATES
# the obstruction, does not remove it. beta_2 unaffected; the structure is banked.
# ============================================================================
def verify_lambert_orbit(qs='0.37', zs='0.51'):
    import mpmath as mp
    q = mp.mpf(qs); z = mp.mpf(zs)
    def gk(k):
        poch = mp.mpf(1)
        for i in range(1, 2*k+1): poch *= (1-q**i)
        return mp.mpf((-1)**k)*q**(k*(k-1))/poch
    G = lambda w, K=120: sum(gk(k)*mp.mpc(w)**k for k in range(K))
    tG = lambda w, K=120: sum(k*gk(k)*mp.mpc(w)**k for k in range(K))
    PHI = sum(i*q**i/(1-q**i) for i in range(1, 400))
    partial = lambda k: sum(i*q**i/(1-q**i) for i in range(1, 2*k+1))
    lhs = sum(gk(k)*(PHI-partial(k))*z**k for k in range(80))
    rhs = mp.mpf(0)
    for d in range(1, 240):
        w = q**(2*d)*z
        rhs += 2*q**d/(1-q**d)*tG(w) + q**d/(1-q**d)**2*G(w)
        if q**d < mp.mpf(10)**-42: break
    print("Lambert-orbit identity rel diff:", mp.nstr(abs(lhs-rhs)/abs(lhs), 4))
