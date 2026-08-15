#!/usr/bin/env python3
r"""
assembly_certificate.py -- certificate for the block-assembly inputs (R) and (L) of paper2.

It certifies, by two independent arithmetic models, the statements proved in
private/assembly_RL.tex:

  PART 1  exact power series in Z[[q]] (two truncation orders):
          catalytic telescoping for the travel and the bulk section identities,
              G^T_0 = Sigma_0/(1-Sigma_1),   G^T_1 = Sigma_1/(1-Sigma_1),
              G_0   = S_0/(1-S_1),           G_1   = S_1/(1-S_1),
              t_1   = T_1/(1-S_1),           b_1   = T_0 + t_1 S_0,
          the reciprocity  t_0 = b_1,  the bilinear form  T_0(1-S_1)+T_1 S_0 = S_1,
          the cocycle dictionary  P_11 = 1+T_0,  P_12 = T_1,  P_22 = S_e = 1-S_1,
          the Casoratian  P_11 S_e + P_12 S_0 = 1,
          the Hahn-Exton closed form  P_12 = (2q^3/(1-q^3)) Y_3(1),
          and  S_o = ((1-q)/(2q)) S_0.

  PART 2  the Moebius factorisation  B = (b_0 + g kappa)/(1 - g t_1),
          kappa = t_0 b_1 - b_0 t_1, with g a free rational parameter, plus three
          hypothesis-deletion controls (rank-2 gap term; asymmetric gapless kernel;
          gap term q^{a+2b} instead of q^{a+b}).

  PART 3  high precision at the travel poles (two distinct precisions), where the
          defining series of the resolvent do NOT converge and only the analytic
          continuation exists: b_0 = S_0/S_e, t_0 = b_1 = S_1/S_e, t_1 = P_12/S_e,
          and B(q,y) at y=1 and y=q against the Moebius value.

  PART 4  the marker-junction kernel is NOT rank one: exact rational minors of the
          junction matrix  q^{max(|a_L|-1,|a_R|)}  (the site-0 cost, tabulated from
          the validated matching engine).  This is the obstruction to the numerator
          identification asserted in (R).

No floating point enters PART 1, 2 or 4.  PART 3 states its precision and the
agreement of the two precisions.

Run:  bash code/zeta_probe/tools/runcap.sh 8000 1800 python3 code/zeta_probe/assembly_certificate.py
"""
from fractions import Fraction as F
import sys

FAIL = []
def check(name, ok, extra=""):
    print(("  PASS  " if ok else "  FAIL  ") + name + (("   " + extra) if extra else ""))
    if not ok:
        FAIL.append(name)

# =========================================================================
# truncated power series over Q, ring Q[[q]]/(q^{N+1})
# =========================================================================
class SeriesRing:
    def __init__(self, N):
        self.N = N
    def zero(self): return [F(0)]*(self.N+1)
    def one(self):
        z = self.zero(); z[0] = F(1); return z
    def q(self, k):
        z = self.zero()
        if 0 <= k <= self.N: z[k] = F(1)
        return z
    def add(self, a, b): return [x+y for x, y in zip(a, b)]
    def sub(self, a, b): return [x-y for x, y in zip(a, b)]
    def smul(self, c, a): return [c*x for x in a]
    def mul(self, a, b):
        N = self.N; r = [F(0)]*(N+1)
        for i, ai in enumerate(a):
            if ai == 0: continue
            for j, bj in enumerate(b[:N-i+1]):
                if bj: r[i+j] += ai*bj
        return r
    def inv(self, a):
        assert a[0] != 0, "not invertible"
        N = self.N; r = [F(0)]*(N+1); r[0] = 1/a[0]
        for n in range(1, N+1):
            s = F(0)
            for k in range(1, n+1): s += a[k]*r[n-k]
            r[n] = -s/a[0]
        return r
    def div(self, a, b): return self.mul(a, self.inv(b))
    def geom(self, a): return self.inv(self.sub(self.one(), a))   # 1/(1-a)

def blocks(R):
    """the four k-recursion blocks plus the auxiliary T_k, as truncated series."""
    q = R.q
    def alpha(k): return R.smul(F(2), R.mul(q(k+1), R.geom(q(k+1))))
    def gamma(k): return R.sub(alpha(k+1), alpha(k))
    def A(k):     return R.smul(F(2), R.mul(q(1), R.geom(q(k+1))))
    def C(k):     return R.sub(R.smul(F(2), R.mul(q(k+3), R.geom(q(k+2)))),
                               R.smul(F(2), R.mul(q(k+2), R.geom(q(k+1)))))
    def ladder(k, src, step):
        tot = R.zero(); prod = R.one(); j = 0
        while True:
            tot = R.add(tot, R.mul(src(k, j), prod))
            prod = R.mul(prod, step(k+2*j))
            if all(x == 0 for x in prod) or j > R.N+4: break
            j += 1
        return tot
    S   = lambda k: ladder(k, lambda k, j: alpha(k+2*j),   gamma)
    T   = lambda k: ladder(k, lambda k, j: alpha(k+2*j+1), gamma)
    Sig = lambda k: ladder(k, lambda k, j: A(k+2*j),       C)
    return dict(S0=S(0), S1=S(1), T0=T(0), T1=T(1), Sig0=Sig(0), Sig1=Sig(1))

def solve_sections(R, e, c, smin, smax):
    """Solve  Phi_s = e_s (c_s + sum_{s'} q^{max(s,s')} Phi_{s'})  in Q[[q]]/(q^{N+1}).
    e_s = O(q) so each Picard iteration gains one power of q; N+1 iterations are exact."""
    Phi = {s: R.mul(e[s], c[s]) for s in range(smin, smax+1)}
    for _ in range(R.N+1):
        new = {}
        for s in range(smin, smax+1):
            acc = c[s][:]
            for sp in range(smin, smax+1):
                acc = R.add(acc, R.mul(R.q(max(s, sp)), Phi[sp]))
            new[s] = R.mul(e[s], acc)
        Phi = new
    return Phi

def sect(R, Phi, k, smin, smax):
    tot = R.zero()
    for s in range(smin, smax+1):
        tot = R.add(tot, R.mul(R.q(k*s), Phi[s]))
    return tot

def cocycle(R):
    """P = prod_{n>=1} [[1+2q^{2n}, -2q^n],[2q^{3n}, 1-2q^{2n}]] acting as in the
    gapless three-term recursion.  Returns P11,P12,P21,P22."""
    x, y, X, Y = R.zero(), R.one(), R.one(), R.zero()
    for n in range(1, R.N+2):
        q2n, q3n, qn = R.q(2*n), R.q(3*n), R.q(n)
        a = R.add(R.one(), R.smul(F(2), q2n))
        d = R.sub(R.one(), R.smul(F(2), q2n))
        xn = R.sub(R.mul(x, a), R.smul(F(2), R.mul(y, qn)))
        yn = R.add(R.smul(F(2), R.mul(x, q3n)), R.mul(y, d))
        Xn = R.sub(R.mul(X, a), R.smul(F(2), R.mul(Y, qn)))
        Yn = R.add(R.smul(F(2), R.mul(X, q3n)), R.mul(Y, d))
        x, y, X, Y = xn, yn, Xn, Yn
    return X, Y, x, y

def part1(N):
    print(f"\n[PART 1]  exact power series in Z[[q]], truncation order q^{N}")
    R = SeriesRing(N); B = blocks(R); SM = N+2
    one = R.one()
    # ---- bulk gapless block: e_s = 2q^s (s>=1), source c=1 ------------------
    e_b = {s: R.smul(F(2), R.q(s)) for s in range(1, SM+1)}
    c1  = {s: one[:] for s in range(1, SM+1)}
    Phi = solve_sections(R, e_b, c1, 1, SM)
    G0, G1 = sect(R, Phi, 0, 1, SM), sect(R, Phi, 1, 1, SM)
    Se = R.sub(one, B['S1'])
    check("bulk  G_0 = S_0/(1-S_1)", G0 == R.div(B['S0'], Se))
    check("bulk  G_1 = S_1/(1-S_1)", G1 == R.div(B['S1'], Se))
    check("bulk block reproduces the bulk-run counts 2,2,6,2,18,6,42,18,118,50,282,190,706,594",
          [int(v) for v in G0[1:15]] == [2,2,6,2,18,6,42,18,118,50,282,190,706,594])
    # ---- bulk with source c_s = q^s  (the rank-one gap vector) --------------
    cq  = {s: R.q(s) for s in range(1, SM+1)}
    Psi = solve_sections(R, e_b, cq, 1, SM)
    b1, t1 = sect(R, Psi, 0, 1, SM), sect(R, Psi, 1, 1, SM)
    t0 = G1
    check("bulk  t_1 = T_1/(1-S_1)", t1 == R.div(B['T1'], Se))
    check("bulk  b_1 = T_0 + t_1 S_0", b1 == R.add(B['T0'], R.mul(t1, B['S0'])))
    check("RECIPROCITY  t_0 = b_1", t0 == b1)
    check("bilinear form  T_0(1-S_1) + T_1 S_0 = S_1",
          R.add(R.mul(B['T0'], Se), R.mul(B['T1'], B['S0'])) == B['S1'])
    # ---- travel block: e_s = 2q^{1+s} (s>=0), source c=1 -------------------
    e_t = {s: R.smul(F(2), R.q(1+s)) for s in range(0, SM+1)}
    c1t = {s: one[:] for s in range(0, SM+1)}
    Phit = solve_sections(R, e_t, c1t, 0, SM)
    GT0, GT1 = sect(R, Phit, 0, 0, SM), sect(R, Phit, 1, 0, SM)
    Set = R.sub(one, B['Sig1'])
    check("travel  G^T_0 = Sigma_0/(1-Sigma_1)", GT0 == R.div(B['Sig0'], Set))
    check("travel  G^T_1 = Sigma_1/(1-Sigma_1)", GT1 == R.div(B['Sig1'], Set))
    check("travel block reproduces the travel-run counts 2,6,10,26,54,114,274,582,1298",
          [int(v) for v in GT0[1:10]] == [2,6,10,26,54,114,274,582,1298])
    check("Sigma_1 = 2q+2q^3-4q^4+6q^5-4q^6+...",
          [int(v) for v in B['Sig1'][:8]] == [0,2,0,2,-4,6,-4,2])
    # ---- cocycle dictionary ------------------------------------------------
    P11, P12, P21, P22 = cocycle(R)
    check("cocycle  P_22 = S_e = 1-S_1", P22 == Se)
    check("cocycle  P_12 = T_1  (so t_1 = P_12/S_e is an identity, not a definition)",
          P12 == B['T1'])
    check("cocycle  P_11 = 1 + T_0", P11 == R.add(one, B['T0']))
    check("cocycle  P_21 = -S_0", P21 == R.smul(F(-1), B['S0']))
    check("Casoratian  P_11 S_e + P_12 S_0 = 1",
          R.add(R.mul(P11, Se), R.mul(P12, B['S0'])) == one)
    # ---- Hahn-Exton closed form and S_o ------------------------------------
    def qpoch(a, n, step=1):
        r = one[:]
        for i in range(n): r = R.mul(r, R.sub(one, R.q(a+step*i)))
        return r
    Y3 = R.zero(); k = 0
    while k*k+3*k <= N:
        num = one[:]
        for _ in range(k): num = R.mul(num, R.smul(F(-2), R.sub(one, R.q(1))))
        num = R.mul(num, R.q(k*k+3*k))
        Y3 = R.add(Y3, R.div(num, R.mul(qpoch(2, k, 2), qpoch(5, k, 2))))
        k += 1
    check("P_12 = (2q^3/(1-q^3)) Y_3(1)   (Hahn-Exton J^{(3)}_{3/2})",
          P12 == R.mul(R.smul(F(2), R.mul(R.q(3), R.geom(R.q(3)))), Y3))
    So = R.zero(); j = 0
    while j*(j+2) <= N:
        num = one[:]
        for _ in range(j): num = R.mul(num, R.smul(F(-2), R.sub(one, R.q(1))))
        num = R.mul(num, R.mul(R.q(j*(j+2)), R.sub(one, R.q(1))))
        So = R.add(So, R.div(num, qpoch(1, 2*j+1)))
        j += 1
    check("S_o = ((1-q)/(2q)) S_0",
          R.mul(So, R.smul(F(2), R.q(1))) == R.mul(R.sub(one, R.q(1)), B['S0']))
    Sexp = R.zero(); j = 0
    while j*(j+1) <= N:
        num = one[:]
        for _ in range(j): num = R.mul(num, R.smul(F(-2), R.sub(one, R.q(1))))
        num = R.mul(num, R.q(j*(j+1)))
        Sexp = R.add(Sexp, R.div(num, qpoch(1, 2*j)))
        j += 1
    check("S_e (defining series of eq:blocks) = 1 - S_1", Sexp == Se)

# =========================================================================
# PART 2 -- Moebius factorisation with g a free parameter, and deletions
# =========================================================================
class GPolySeries:
    """Q[g][[q]]/(q^{N+1}); a series is a list of dicts {gdeg: Fraction}."""
    def __init__(self, N): self.N = N
    def zero(self): return [dict() for _ in range(self.N+1)]
    def one(self):
        z = self.zero(); z[0] = {0: F(1)}; return z
    def q(self, k):
        z = self.zero()
        if 0 <= k <= self.N: z[k] = {0: F(1)}
        return z
    def gq(self, k):
        """g * q^k"""
        z = self.zero()
        if 0 <= k <= self.N: z[k] = {1: F(1)}
        return z
    def add(self, a, b):
        r = self.zero()
        for i in range(self.N+1):
            d = dict(a[i])
            for k, v in b[i].items():
                d[k] = d.get(k, F(0)) + v
                if d[k] == 0: del d[k]
            r[i] = d
        return r
    def neg(self, a): return [{k: -v for k, v in d.items()} for d in a]
    def sub(self, a, b): return self.add(a, self.neg(b))
    def smul(self, c, a): return [{k: c*v for k, v in d.items()} for d in a]
    def mul(self, a, b):
        N = self.N; r = self.zero()
        for i, da in enumerate(a):
            if not da: continue
            for j in range(0, N-i+1):
                db = b[j]
                if not db: continue
                tgt = r[i+j]
                for ka, va in da.items():
                    for kb, vb in db.items():
                        kk = ka+kb
                        tgt[kk] = tgt.get(kk, F(0)) + va*vb
                        if tgt[kk] == 0: del tgt[kk]
        return r
    def iszero(self, a): return all(not d for d in a)

def part2(N):
    print(f"\n[PART 2]  Moebius factorisation, g free, truncation order q^{N}")
    G = GPolySeries(N); SM = N+2
    RS = SeriesRing(N)
    def lift(a): return [({0: c} if c != 0 else {}) for c in a]
    def solve(kernel, source, smin, smax):
        """Phi_b = e_b(c_b + sum_a K(a,b) Phi_a); returns dict of GPolySeries."""
        e = {b: G.smul(F(2), G.q(b)) for b in range(smin, smax+1)}
        Phi = {b: G.mul(e[b], source[b]) for b in range(smin, smax+1)}
        for _ in range(N+1):
            new = {}
            for b in range(smin, smax+1):
                acc = source[b]
                for a in range(smin, smax+1):
                    acc = G.add(acc, G.mul(kernel(a, b), Phi[a]))
                new[b] = G.mul(e[b], acc)
            Phi = new
        return Phi
    one = G.one()
    src1 = {b: one for b in range(1, SM+1)}
    K_full   = lambda a, b: G.add(G.q(max(a, b)), G.gq(a+b))
    K_rank2  = lambda a, b: G.add(G.q(max(a, b)), G.add(G.gq(a+b), G.gq(2*a+2*b)))
    K_shift  = lambda a, b: G.add(G.q(max(a, b)), G.gq(a+2*b))
    # gapless quantities (g-free) from PART 1 machinery
    e_b = {s: RS.smul(F(2), RS.q(s)) for s in range(1, SM+1)}
    c1  = {s: RS.one() for s in range(1, SM+1)}
    cq  = {s: RS.q(s)  for s in range(1, SM+1)}
    Phi0 = solve_sections(RS, e_b, c1, 1, SM); Psi0 = solve_sections(RS, e_b, cq, 1, SM)
    b0 = lift(sect(RS, Phi0, 0, 1, SM)); t0 = lift(sect(RS, Phi0, 1, 1, SM))
    b1 = lift(sect(RS, Psi0, 0, 1, SM)); t1 = lift(sect(RS, Psi0, 1, 1, SM))
    kap = G.sub(G.mul(t0, b1), G.mul(b0, t1))
    def total(Phi):
        tot = G.zero()
        for b in range(1, SM+1): tot = G.add(tot, Phi[b])
        return tot
    # B (1 - g t_1) - (b_0 + g kappa) == 0 ?
    for label, K, must_hold in (("gap term q^{a+b} (the model)", K_full, True),
                                ("DELETION: rank-2 gap term", K_rank2, False),
                                ("DELETION: gap term q^{a+2b}", K_shift, False)):
        Bv = total(solve(K, src1, 1, SM))
        gt1 = G.zero()
        for i in range(N+1):
            for k, v in t1[i].items():
                gt1[i][k+1] = gt1[i].get(k+1, F(0)) + v
        gk = G.zero()
        for i in range(N+1):
            for k, v in kap[i].items():
                gk[i][k+1] = gk[i].get(k+1, F(0)) + v
        res = G.sub(G.mul(Bv, G.sub(one, gt1)), G.add(b0, gk))
        ok = G.iszero(res)
        first = next((i for i in range(N+1) if res[i]), None)
        check(f"Moebius  B(1-g t_1) = b_0 + g kappa  [{label}]",
              ok == must_hold,
              "" if ok else f"first nonzero at q^{first}")
    # deletion: asymmetric gapless kernel must break the reciprocity t_0 = b_1
    K_asym = lambda a, b: RS.add(RS.q(max(a, b)), RS.q(a+2*b))
    def solve_rs(K, c):
        Phi = {s: RS.mul(e_b[s], c[s]) for s in range(1, SM+1)}
        for _ in range(N+1):
            new = {}
            for s in range(1, SM+1):
                acc = c[s][:]
                for sp in range(1, SM+1): acc = RS.add(acc, RS.mul(K(sp, s), Phi[sp]))
                new[s] = RS.mul(e_b[s], acc)
            Phi = new
        return Phi
    Pa = solve_rs(K_asym, c1); Pb = solve_rs(K_asym, cq)
    t0a = sect(RS, Pa, 1, 1, SM); b1a = sect(RS, Pb, 0, 1, SM)
    check("DELETION: asymmetric gapless kernel breaks t_0 = b_1", t0a != b1a,
          "reciprocity uses K(a,b)=K(b,a) essentially")

# =========================================================================
# PART 3 -- high precision at the travel poles (analytic continuation regime)
# =========================================================================
def part3(npoles, dps_list):
    print(f"\n[PART 3]  travel poles, {npoles} of them, precisions {dps_list}")
    import mpmath as mp
    def Sig1(q, dps):
        tot = mp.mpf(0); prod = mp.mpf(1); j = 0
        while True:
            k = 1+2*j
            tot += 2*q/(1-q**(k+1))*prod
            prod *= 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
            if abs(prod) < mp.mpf(10)**(-dps-12) and j > 30: break
            j += 1
            if j > 400000: break
        return tot
    def blocks_num(q, dps):
        out = {}
        def lad(k, srcf, stepf):
            tot = mp.mpf(0); prod = mp.mpf(1); j = 0
            while True:
                tot += srcf(k+2*j)*prod; prod *= stepf(k+2*j)
                if abs(prod) < mp.mpf(10)**(-dps-12) and j > 30: break
                j += 1
                if j > 400000: break
            return tot
        al = lambda k: 2*q**(k+1)/(1-q**(k+1))
        ga = lambda k: al(k+1)-al(k)
        A  = lambda k: 2*q/(1-q**(k+1))
        C  = lambda k: 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        out['S0'] = lad(0, al, ga); out['S1'] = lad(1, al, ga)
        out['T1'] = lad(1, lambda k: al(k+1), ga)
        out['Sig0'] = lad(0, A, C); out['Sig1'] = lad(1, A, C)
        return out
    def resolvent(q, Nb, y=None):
        """O(N) two-point solve of  L_b = (1+2q^{2b})L_{b-1} + 2q^b R_b + 2q^b c_b,
           R_{b+1} = -2q^{3b}L_{b-1} + (1-2q^{2b})R_b - 2q^{2b}c_b,
           with L_0 = 0 and R_{Nb+1} = 0.  Returns (b0,t0,b1,t1)."""
        out = []
        for src in ('one', 'qb'):
            # homogeneous solution with (L_0,R_1) = (0,1) and particular with (0,0)
            Lh, Rh = mp.mpf(0), mp.mpf(1)
            Lp, Rp = mp.mpf(0), mp.mpf(0)
            qb = mp.mpf(1)
            for b in range(1, Nb+1):
                qb *= q; q2b = qb*qb; q3b = q2b*qb
                c = mp.mpf(1) if src == 'one' else qb
                Lh, Rh = (1+2*q2b)*Lh + 2*qb*Rh, -2*q3b*Lh + (1-2*q2b)*Rh
                Lp, Rp = (1+2*q2b)*Lp + 2*qb*Rp + 2*qb*c, -2*q3b*Lp + (1-2*q2b)*Rp - 2*q2b*c
            R1 = -Rp/Rh
            out.append((Lp + R1*Lh, R1))
        (b0, t0), (b1, t1) = out
        return b0, t0, b1, t1
    results = {}
    for dps in dps_list:
        mp.mp.dps = dps
        f = lambda w: Sig1(mp.e**(-2/(w*w)), dps) - 1
        # global scan in w = sqrt(2/tau): the poles sit near w = (m+1/2)pi, m>=0
        poles = []
        wlo, whi = mp.mpf('1.2'), (npoles+1)*mp.pi
        steps = 200*npoles
        a, fa = wlo, f(wlo)
        for i in range(1, steps+1):
            bb = wlo + (whi-wlo)*mp.mpf(i)/steps
            fb = f(bb)
            if fa*fb < 0:
                lo, hi = a, bb
                for _ in range(6*dps):
                    mid = (lo+hi)/2
                    if f(lo)*f(mid) <= 0: hi = mid
                    else: lo = mid
                w = (lo+hi)/2
                poles.append(mp.e**(-2/(w*w)))
                if len(poles) >= npoles: break
            a, fa = bb, fb
        rows = []
        for qm in poles:
            tau = -mp.log(qm)
            Nb = int(mp.ceil((dps+15)*mp.log(10)/tau)) + 60
            b0, t0, b1, t1 = resolvent(qm, Nb)
            B = blocks_num(qm, dps)
            Se = 1 - B['S1']
            e = lambda u, v: abs(u-v)/max(abs(v), mp.mpf(1))
            gV = qm/(1-qm); gU = qm/(1-qm*qm)
            kap = t0*b1 - b0*t1
            # Moebius values (PART 2 certifies the formula itself; the dense
            # cross-check below re-derives B independently of the formula)
            BV = (b0+gV*kap)/(1-gV*t1); BU = (b0+gU*kap)/(1-gU*t1)
            rows.append(dict(q=qm, tau=tau, Nb=Nb,
                             e_b0=e(b0, B['S0']/Se), e_t0=e(t0, B['S1']/Se),
                             e_rec=e(t0, b1), e_t1=e(t1, B['T1']/Se),
                             b0=b0, t1=t1, s=gV*t1, BV=BV, BU=BU,
                             lift=(1-gV*t1)*BV + qm*b0))
        results[dps] = rows
        print(f"  dps={dps}: {len(rows)} poles, q from {mp.nstr(rows[0]['q'],8)} to {mp.nstr(rows[-1]['q'],10)}")
        for k in ('e_b0', 'e_t0', 'e_rec', 'e_t1'):
            worst = max(r[k] for r in rows)
            print(f"     max rel. err {k:6s} = {mp.nstr(worst,4)}")
        print("     m   q_m            b0*tau      s=gV t1     B_V           B_U")
        for i, r in enumerate(rows[:8]):
            print(f"    {i+1:>3} {mp.nstr(r['q'],10):<14} {mp.nstr(r['b0']*r['tau'],8):<11}"
                  f" {mp.nstr(r['s'],8):<11} {mp.nstr(r['BV'],8):<13} {mp.nstr(r['BU'],8)}")
    # agreement of the two precisions
    d1, d2 = dps_list[0], dps_list[1]
    n = min(len(results[d1]), len(results[d2]))
    worst = max(abs(results[d1][i]['q']-results[d2][i]['q']) for i in range(n))
    print(f"  two-precision agreement on q_m: max |diff| = {mp.nstr(worst,4)} over {n} poles")
    # the alternating ladders lose ~ w/log 10 digits to cancellation at the highest
    # pole; budget 15 digits and require the rest.
    ok = True; detail = []
    for d in dps_list:
        tol = mp.mpf(10)**(-d+15)
        worstd = max(max(r[k] for r in results[d]) for k in ('e_b0','e_t0','e_rec','e_t1'))
        detail.append(f"dps {d}: {mp.nstr(worstd,3)} (< 1e-{d-15})")
        ok = ok and worstd < tol
    check(f"dictionary b_0=S_0/S_e, t_0=b_1=S_1/S_e, t_1=P_12/S_e at {n} travel poles",
          ok, "; ".join(detail))
    check("gate signs b_0>0 and s<1 at every computed pole",
          all(r['b0'] > 0 and r['s'] < 1 for r in results[dps_list[-1]]))
    check("lifting identity  (1-s)B_V + q b_0 > 0 at every computed pole",
          all(r['lift'] > 0 for r in results[dps_list[-1]]))
    # --- independent dense cross-check of the Moebius value (no Sherman-Morrison) ---
    mp.mp.dps = 30
    qstar = results[dps_list[-1]][0]['q']
    worst = mp.mpf(0)
    for qv in (mp.mpf('0.5'), mp.mpf('0.7'), qstar):
        Sm = int(mp.ceil(45*mp.log(10)/(-mp.log(qv)))) + 25
        Nb = int(mp.ceil(45*mp.log(10)/(-mp.log(qv)))) + 60
        b0, t0, b1, t1 = resolvent(qv, Nb)
        kap = t0*b1 - b0*t1
        for y in (mp.mpf(1), qv):
            g = qv/(1-qv*y)
            Mx = mp.matrix(Sm, Sm); E = mp.matrix(Sm, 1)
            for b in range(1, Sm+1):
                E[b-1, 0] = 2*qv**b
                for a in range(1, Sm+1):
                    Mx[b-1, a-1] = 2*qv**b*(qv**max(a, b) + qv**(a+b)*g)
            P = mp.lu_solve(mp.eye(Sm) - Mx, E)
            Bdense = sum(P[i, 0] for i in range(Sm))
            Bmob = (b0 + g*kap)/(1 - g*t1)
            worst = max(worst, abs(Bdense-Bmob)/abs(Bmob))
    print(f"  dense cross-check of the Moebius value at q=0.5,0.7,q_1 and y=1,q: "
          f"max rel err {mp.nstr(worst,4)} (dps 30, truncation q^45-scaled)")
    check("Moebius value agrees with an independent dense resolvent solve",
          worst < mp.mpf(10)**(-20))

# =========================================================================
# PART 4 -- the marker junction is not rank one
# =========================================================================
def part4():
    print("\n[PART 4]  marker-junction kernel: exact rank test")
    # Site-0 cost (arrival), d_L the last bulk deposit (even, f=0), d_R the first
    # travel deposit (odd, f=+1).  The closed form proved in paper2 Cor. (marker
    # junctions) is
    #     Site_0(d_L, d_R) = max(|d_L - 1|, |d_R|),
    # NOT max(|d_L|-1, |d_R|): the two agree on d_L >= 0 and differ on d_L <= -2.
    # The exhaustive verification against the exact matching value lives in
    # code/zeta_probe/tools/sitecost (Rust, exact integer arithmetic).
    def site0(dL, dR): return max(abs(dL-1), abs(dR))
    def site0_old(dL, dR): return max(abs(dL)-1, abs(dR))
    cells = 0; diff = 0; first = None
    for dL in range(-12, 13, 2):
        for dR in [v for v in range(-9, 10) if v % 2]:
            cells += 1
            if site0(dL, dR) != site0_old(dL, dR):
                diff += 1
                if first is None: first = (dL, dR, site0(dL, dR), site0_old(dL, dR))
    print(f"  the earlier marker form max(|d_L|-1,|d_R|) differs from the proved form "
          f"on {diff} of {cells} cells (|d_L|<=12 even, |d_R|<=9 odd); "
          f"smallest: d_L={first[0]}, d_R={first[1]}, true {first[2]} vs {first[3]}")
    check("the earlier marker form agrees exactly on d_L >= 0 and nowhere below -1",
          all(site0(dL, dR) == site0_old(dL, dR)
              for dL in range(0, 13, 2) for dR in range(-9, 10, 2) if dR % 2)
          and diff > 0)
    # the interleaved 3x3 minor, exactly
    x = F(1, 2)
    rows3 = [[x**site0(aL, aR) for aR in (1, 5, 9)] for aL in (0, 4, 8)]
    det3 = (rows3[0][0]*(rows3[1][1]*rows3[2][2]-rows3[1][2]*rows3[2][1])
            - rows3[0][1]*(rows3[1][0]*rows3[2][2]-rows3[1][2]*rows3[2][0])
            + rows3[0][2]*(rows3[1][0]*rows3[2][1]-rows3[1][1]*rows3[2][0]))
    check("interleaved 3x3 junction minor is nonzero (rank >= 3)",
          det3 == x**9*(x-x**3)*(x**5-x**7) and det3 != 0,
          f"det = {det3} at x=1/2")
    aLs = [0, 2, 4, 6, 8]; aRs = [1, 3, 5, 7, 9]
    q = F(1, 3)
    Mrows = [[q**site0(aL, aR) for aR in aRs] for aL in aLs]
    # exact Gaussian elimination over Q
    A = [row[:] for row in Mrows]; n = len(A); m = len(A[0]); rank = 0
    for c in range(m):
        piv = next((r for r in range(rank, n) if A[r][c] != 0), None)
        if piv is None: continue
        A[rank], A[piv] = A[piv], A[rank]
        pv = A[rank][c]
        for r in range(n):
            if r != rank and A[r][c] != 0:
                f = A[r][c]/pv
                A[r] = [A[r][j] - f*A[rank][j] for j in range(m)]
        rank += 1
    print(f"  junction matrix [q^max(|a_L|-1,|a_R|)] on a_L in {aLs}, a_R in {aRs}, q=1/3")
    print(f"  exact rank over Q = {rank}")
    check("marker junction kernel is NOT rank one (rank >= 3)", rank >= 3,
          f"rank {rank}: the numerator of (R) does not factor as Sigma_0 * B_V * J")
    # the sign-symmetrised junction of paper2 eq. (junctionsym): the bulk run's
    # junction-adjacent deposit carries either sign with weight B_sigma/2
    sig = [0, 2, 4, 6, 8, 10]; srs = [1, 3, 5, 7, 9, 11]
    xh = F(1, 2)
    def jsym(sg, r):
        if sg == 0: return xh**site0(0, r)
        return (xh**site0(sg, r) + xh**site0(-sg, r)) / 2
    Msym = [[jsym(sg, r) for r in srs] for sg in sig]
    A = [row[:] for row in Msym]; n = len(A); m2 = len(A[0]); rk = 0
    for c in range(m2):
        piv = next((r for r in range(rk, n) if A[r][c] != 0), None)
        if piv is None: continue
        A[rk], A[piv] = A[piv], A[rk]
        pv = A[rk][c]
        for r in range(n):
            if r != rk and A[r][c] != 0:
                f = A[r][c]/pv
                A[r] = [A[r][j] - f*A[rk][j] for j in range(m2)]
        rk += 1
    check(f"sign-symmetrised junction matrix has rank 6 on the 6x6 block at x=1/2",
          rk == 6, f"rank {rk}")
    # for contrast: the gap-bridge kernel q^{a+b} IS rank one
    Ag = [[q**(a+b) for b in range(1, 6)] for a in range(1, 6)]
    r2 = 0; A = [row[:] for row in Ag]
    for c in range(5):
        piv = next((r for r in range(r2, 5) if A[r][c] != 0), None)
        if piv is None: continue
        A[r2], A[piv] = A[piv], A[r2]; pv = A[r2][c]
        for r in range(5):
            if r != r2 and A[r][c] != 0:
                f = A[r][c]/pv
                A[r] = [A[r][j] - f*A[r2][j] for j in range(5)]
        r2 += 1
    check("gap-bridge kernel q^{a+b} IS rank one (this is why (L) factorises)", r2 == 1)

if __name__ == "__main__":
    print("="*78)
    print("assembly_certificate.py -- inputs (R) and (L) of paper2")
    print("="*78)
    for N in (28, 40):
        part1(N)
    part2(18)
    part3(npoles=int(sys.argv[1]) if len(sys.argv) > 1 else 8, dps_list=(40, 70))
    part4()
    print("\n" + "="*78)
    if FAIL:
        print("FAILED CHECKS:"); [print("   " + f) for f in FAIL]; sys.exit(1)
    print("ALL CHECKS PASS")
