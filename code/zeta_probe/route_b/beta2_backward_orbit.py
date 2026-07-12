#!/usr/bin/env python3
"""Backward-orbit normal form of the zero condition (paper2 rem:backward).

If G(q, z1) = 0, the three-term recurrence along the backward sigma-orbit loses one solution
constant: G(q, Q^{-m} z1) = G(q, Q z1) * r_m(q) with r_0 = 0, r_1 = -1/q,
    r_m = ( a(Q^{-m} z1) r_{m-1} - r_{m-2} ) / q,   a(w) = q+1-qw,
all r_m in Q(q, z1). The C1-asymptotics (thm:zeroproduct) give the exact evaluation
    lim_m  r_m Q^{m(m+1)/2} (-z1)^{-m}  =  theta_Q(-z1) / ( (q;q)_inf * G(q, Q z1) ),
rate Q^m, correction series sum_j b_j z1^{-j} Q^{mj} (b_j = q^{j-j(j-1)/2}/(q;q)_j).

DIOPHANTINE COSTING (honest): under q* = s/t the normalized terms are rationals of height
(st)^{m^2+O(m)} with error O(Q^m); acceleration by J terms gains Q^{mJ} but pays the quadratic
heights of the b_j: arithmetic ratio stays <= 1/2 (prop:nogo conservation). A NORMAL FORM of the
reductio -- the sharpest single-sequence statement of the problem -- NOT a crack in the wall.
"""
import mpmath as mp

if __name__ == "__main__":
    mp.mp.dps = 50
    q = mp.mpf('0.449453630558948046125545825395696389319555316196'); Q = q*q
    zs = 2*q*(1-q)

    def G(z, K=220):
        t = mp.mpf(0); poch = mp.mpf(1)
        for k in range(K):
            if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
            term = mp.mpf((-1)**k)*q**(k*(k-1))*mp.mpc(z)**k/poch
            t += term
            if k > 10 and abs(term) < mp.mpf(10)**-55: break
        return t
    th = lambda x, N=90: sum(Q**(mp.mpf(n)*(n-1)/2)*mp.mpc(x)**n for n in range(-N, N+1))

    def poch_inf(a0, base):
        r = mp.mpf(1); x = mp.mpf(a0)
        while x > mp.mpf(10)**-52: r *= (1-x); x *= base
        return r
    u1 = G(Q*zs)
    r = [mp.mpf(0), -1/q]
    for m in range(2, 26):
        r.append(((q+1-q*zs/Q**m)*r[m-1] - r[m-2])/q)
    for m in [3, 10, 15]:
        direct = G(zs/Q**m)/u1
        print(f"m={m}: proportionality rel err {mp.nstr(abs(direct-r[m])/abs(r[m]), 3)}")
    C = th(-zs)/(poch_inf(q, q)*u1)
    for m in [12, 20, 24]:
        rho = r[m]*Q**(mp.mpf(m)*(m+1)/2)*(-zs)**(-m)
        print(f"m={m}: rho_m - limit = {mp.nstr(abs(rho-C), 3)}")
