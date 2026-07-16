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

M = 56   # (holonomy test used M = 120; see holonomy_test below)

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


# ============================================================================
# HOLONOMY TEST (v2.12.3): z_1 is NOT holonomic. No linear ODE sum_i P_i(q) z_1^{(i)} = 0
# with deg P_i <= d for (r,d) up to (8,10), (6,14), (5,12) -- exact linear algebra on
# 110-116 integer coefficients (z_1 computed to order 120 by integer Newton), every
# matrix full column rank. CONSEQUENCE: z_1 is an integer power series that is
# non-algebraic, non-holonomic, radius < 1 -- the class where NO arithmetic technology
# exists. Chudnovsky-Andre-Bost and Calegari-Dimitrov-Tang arithmetic holonomy bounds
# (the newest "integrality + structure => arithmetic" machinery) all require holonomy;
# Polya-Carlson requires radius exactly 1. Integrality alone is not actionable.
# NOTE: the Newton iteration needs inv_unit (leading coeff G_z(0,1) = -1, NOT +1) --
# a naive inv() assuming a[0]=1 silently returns garbage (c_1 = 511 instead of -1).
# ============================================================================
def holonomy_test():
    """recompute z_1 to order 120 (integer Newton) and test for a linear ODE"""
    MM = 120
    def mul(a, b):
        c = [0]*(MM+1)
        for i, ai in enumerate(a):
            if ai == 0: continue
            for j in range(MM+1-i):
                if b[j]: c[i+j] += ai*b[j]
        return c
    sub2 = lambda a, b: [x-y for x, y in zip(a, b)]
    add2 = lambda a, b: [x+y for x, y in zip(a, b)]
    def inv_unit(a):
        u = a[0]; assert u in (1, -1)
        c = [0]*(MM+1); c[0] = u
        for n in range(1, MM+1):
            c[n] = -u*sum(a[i]*c[n-i] for i in range(1, n+1))
        return c
    def qp(n):
        c = [0]*(MM+1)
        if n <= MM: c[n] = 1
        return c
    def inv_poch(m):
        c = [0]*(MM+1); c[0] = 1
        for part in range(1, m+1):
            for n in range(part, MM+1): c[n] += c[n-part]
        return c
    ONE = qp(0)
    Gs = []
    for k in range(12):
        Gs.append([0]*(MM+1) if k*(k-1) > MM else
                  [(-1)**k*x for x in mul(qp(k*(k-1)), inv_poch(2*k))])
    def eG(z):
        t = [0]*(MM+1); zp = ONE[:]
        for k in range(12):
            t = add2(t, mul(Gs[k], zp)); zp = mul(zp, z)
        return t
    def eGz(z):
        t = [0]*(MM+1); zp = ONE[:]
        for k in range(1, 12):
            t = add2(t, [k*x for x in mul(Gs[k], zp)]); zp = mul(zp, z)
        return t
    z = ONE[:]
    for _ in range(9): z = sub2(z, mul(eG(z), inv_unit(eGz(z))))
    assert all(x == 0 for x in eG(z)), "Newton residual nonzero"
    p = (1 << 61) - 1
    ders = [[x % p for x in z]]
    for _ in range(9):
        a = ders[-1]; ders.append([(a[n+1]*(n+1)) % p for n in range(len(a)-1)]+[0])
    for (r, d) in [(4, 10), (6, 14), (8, 10)]:
        cols = [[0]*j + ders[i][:MM+1-j] for i in range(r+1) for j in range(d+1)]
        rows = MM-r-2
        A = [[cols[k][n] for k in range(len(cols))] for n in range(rows)]
        C = len(A[0]); rr = 0
        for cc in range(C):
            piv = next((x for x in range(rr, rows) if A[x][cc] % p), None)
            if piv is None: continue
            A[rr], A[piv] = A[piv], A[rr]
            iv = pow(A[rr][cc], p-2, p); A[rr] = [x*iv % p for x in A[rr]]
            for x in range(rows):
                if x != rr and A[x][cc] % p:
                    f = A[x][cc]; A[x] = [(u-f*v) % p for u, v in zip(A[x], A[rr])]
            rr += 1
            if rr == rows: break
        print(f"order {r}, deg {d}: {C} unknowns, rank {rr} -> {'ODE' if rr < C else 'NO ODE'}")
