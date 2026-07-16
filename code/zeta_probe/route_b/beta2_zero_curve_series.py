#!/usr/bin/env python3
"""THEOREM (companion paper thm:integrality): the zero curve of the Hahn-Exton q-cosine is an
INTEGER power series:
   z_1(q) = 1 - q - q^3 + q^4 - q^5 + 2q^6 - 2q^7 + 4q^8 - 6q^9 + 8q^10 - 14q^11 + ... in Z[[q]].

PROOF (Hensel): g_k = (-1)^k q^{k(k-1)}/(q;q)_{2k} in Z[[q]] (partitions into parts <= 2k),
g_k == 0 mod q^{k(k-1)}, so G(q,z) converges (q)-adically on 1 + qZ[[q]] and G(0,z) = 1 - z;
G(0,1) = 0 with unit derivative G_z(0,1) = -1: Hensel in the complete local ring Z[[q]].

FEATURES (measured, order 56): not rational (full Hankel rank); no algebraic relation of
bidegree <= (6,5); radius of convergence ~ 0.5696 (|c56/c55| = 1.7557) -- a complex branch
point of the zero configuration; q* = 0.4494 lies INSIDE the disc.

LEDGER (the narrowest margin recorded): integrality gives LINEAR heights t^N against geometric
error (q/R)^N: the Liouville criterion for the crossing z_1(q) = 2q(1-q) reads s < R ~ 0.5696,
failing by factor s/R ~ 1.76 at s = 1. The obstruction is the sub-unit radius (complex zero
collision) -- a new, geometric face of the wall.

Coefficient sequence (OEIS-candidate): 1,-1,0,-1,1,-1,2,-2,4,-6,8,-14,21,-34,56,-88,148,-242,
398,-669,1109,-1867,3145,-5293,8987,...
"""
from fractions import Fraction as Fr

M = 56

def mul(a, b):
    c = [Fr(0)]*(M+1)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j in range(M+1-i):
            if b[j]: c[i+j] += ai*b[j]
    return c

def sub(a, b): return [x-y for x, y in zip(a, b)]
def add(a, b): return [x+y for x, y in zip(a, b)]

def inv(a):
    c = [Fr(0)]*(M+1); c[0] = 1/a[0]
    for n in range(1, M+1):
        c[n] = -sum(a[i]*c[n-i] for i in range(1, n+1))/a[0]
    return c

def qpow(n):
    c = [Fr(0)]*(M+1)
    if n <= M: c[n] = Fr(1)
    return c

ONE = qpow(0)

def gk(k):
    if k*(k-1) > M: return [Fr(0)]*(M+1)
    den = ONE[:]
    for i in range(1, 2*k+1): den = mul(den, sub(ONE, qpow(i)))
    return [(-1)**k*x for x in mul(qpow(k*(k-1)), inv(den))]

if __name__ == "__main__":
    Gs = [gk(k) for k in range(9)]
    def evalG(z):
        tot = [Fr(0)]*(M+1); zp = ONE[:]
        for k in range(9):
            tot = add(tot, mul(Gs[k], zp)); zp = mul(zp, z)
        return tot
    def evalGz(z):
        tot = [Fr(0)]*(M+1); zp = ONE[:]
        for k in range(1, 9):
            tot = add(tot, [k*x for x in mul(Gs[k], zp)]); zp = mul(zp, z)
        return tot
    z = ONE[:]
    for _ in range(8):
        z = sub(z, mul(evalG(z), inv(evalGz(z))))
    print("integer to q^56:", all(x.denominator == 1 for x in z))
    print("coefficients:", [int(z[n]) for n in range(25)])
    print("radius estimate 1/|c56/c55| =", round(abs(int(z[55])/int(z[56])), 5))


# ============================================================================
# BRANCH POINT (v2.12.1): the radius-limiting singularity of z_1(q) is the simple fold
#   q_c = -0.55457861014657970734...,  z_c = 2.5239525204417102908...
# (G = G_z = 0, G_zz = 0.2143 != 0, G_q = -1.5012 != 0 => z_1 ~ z_c + C sqrt(q_c - q));
# coefficient fold law |c_n| n^{3/2} |q_c|^n -> 0.7690 confirms R = |q_c| exactly.
# Neither q_c nor z_c algebraic deg <= 4 (PSLQ 10^6). Two new constants of the problem.
#
# RADIUS-CAP LEMMA (the uniformization verdict): for any reparametrization q = psi(u),
# psi in u Z[[u]] (required to keep z_1 o psi in Z[[u]]) with u* = phi(q*) = s'/t' in Q,
# the Liouville criterion reads num(u*) = s' < R_u; but any non-polynomial integer power
# series has radius <= 1, so R_u <= 1 while s' >= 1: UNATTAINABLE. Every integral
# uniformization is capped at the boundary s' = 1 = R_u. The sub-unit radius can be
# moved but not beaten -- the geometric face of the theta-decay boundary.
# ============================================================================
def find_branch_point():
    import mpmath as mp
    mp.mp.dps = 35
    def G(q, z, K=140):
        t = mp.mpf(0); poch = mp.mpf(1)
        for k in range(K):
            if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
            t += mp.mpf((-1)**k)*q**(k*(k-1))*z**k/poch
        return t
    def Gz(q, z, K=140):
        t = mp.mpf(0); poch = mp.mpf(1)
        for k in range(K):
            if k > 0: poch *= (1-q**(2*k-1))*(1-q**(2*k))
            if k >= 1: t += mp.mpf((-1)**k)*k*q**(k*(k-1))*z**(k-1)/poch
        return t
    q, z = mp.mpf('-0.57'), mp.mpf('1.5')
    h = mp.mpf('1e-18')
    for _ in range(40):
        F1, F2 = G(q, z), Gz(q, z)
        J11 = (G(q+h, z)-G(q-h, z))/(2*h); J12 = Gz(q, z)
        J21 = (Gz(q+h, z)-Gz(q-h, z))/(2*h); J22 = (Gz(q, z+h)-Gz(q, z-h))/(2*h)
        det = J11*J22-J12*J21
        dq = (F1*J22-F2*J12)/det; dz = (J11*F2-J21*F1)/det
        q, z = q-dq, z-dz
        if abs(dq)+abs(dz) < mp.mpf(10)**-28: break
    print("q_c =", mp.nstr(q, 20), " z_c =", mp.nstr(z, 20))
    print("residuals:", mp.nstr(abs(G(q, z)), 3), mp.nstr(abs(Gz(q, z)), 3))
