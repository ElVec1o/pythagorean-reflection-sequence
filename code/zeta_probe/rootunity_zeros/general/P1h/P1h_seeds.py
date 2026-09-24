# P1h_seeds.py -- RIGOROUS (Arb): level-n data at every reduced seed j/n, N0 <= n <= N1, in the NEW region R0 = [1/6, 1/5)
# (integer test 5j < n <= 6j).  Same exact finite formula as P1g_seeds.py (P1e Lemma Zk, P1g Lemma Zpm), but also returns
# env^0 = sum_k |gam^0_k| |(1-w)^{-1/2n} e^{Phi_n(zeta^k)}| (needed by Lemma B' for Z itself).
# Serves (a) the base case N <= 150 of Theorem M' and of Theorem main' (P1g) on R0, (b) the level-n data of Lemma B'_R0.
# FAILS LOUDLY (exit 1).  Line format:
#   j n |Z|lo |Z+|lo |Z-|lo env+ env- |omega|up margin_lo env0
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1h_seeds.py N0 N1 OUT [XLO XHI]   (default region [1/6,1/5): XLO <= a/N < XHI)
import sys
from math import gcd
from fractions import Fraction as Fr
from flint import arb, acb, ctx
sys.path.insert(0, '..'); sys.path.insert(0, '../P1g')
from dround import fdn, fup
from P1g_seeds import Gfactors
PI = arb.pi(); I = acb(0, 1)
def e(y): return (2*PI*I*y).exp()
def enc(a, N):
    z = e(arb(a)/N); c = -2*(1 - z)
    lX = N*arb(c.abs_lower()).log()
    if bool(lX < 600):
        X = c**N; B = 2 + X; w = 2/(B*(1 + (1 - 4/(B*B)).sqrt()))
        u = ((1 - w).log()*2/N).exp()/c; fw = (1 - w).log()*(-arb(1)/(2*N))
    else:
        u = 1/c; eps = arb(2)*(-lX).exp()*3/N
        u = u*(1 + acb(arb(0, eps.upper()), arb(0, eps.upper()))); fw = acb(arb(0, eps.upper()), arb(0, eps.upper()))
    ua = arb(u.abs_upper())
    M = int(60/(-float(ua.log().mid()))) + 10
    ET = [e(arb(j)/N) for j in range(N)]
    def gam(sh):
        return [sum((ET[(-(v*v + sh*v + k*v)*a) % N] for v in range(N)), acb(0))/N for k in range(N)]
    G = {s: gam(s) for s in (0, 1, -1)}
    Ph = [acb(0)]*N; un = acb(1)
    for n in range(1, M+1):
        un = un*u
        if n % N == 0: continue
        cn = un/(n*(1 - ET[(-n*a) % N]))
        for k in range(N): Ph[k] = Ph[k] + cn*ET[(k*n*a) % N]
    tail = arb(N)/4*ua**(M+1)/((M+1)*(1 - ua))
    rt = acb(arb(0, tail.upper()), arb(0, tail.upper()))
    b = [(ph + rt).exp() for ph in Ph]
    Zs = {s: sum((g*x for g, x in zip(G[s], b)), acb(0)) for s in (0, 1, -1)}
    ew = fw.exp()
    env = {s: sum((arb(g.abs_upper())*arb((x*ew).abs_upper()) for g, x in zip(G[s], b)), arb(0)) for s in (0, 1, -1)}
    return z, u, Zs, env
def lo(v): return arb(v.abs_lower())
def check(a, N):
    for pr in (128, 256, 512, 1024):
        ctx.prec = pr
        z, u, Zs, env = enc(a, N)
        if not all(bool(lo(Zs[s]) > 0) for s in (0, 1, -1)): continue
        om = Zs[-1]/(u*Zs[1]); t1 = -(1 + om)/2
        Gs = Gfactors(z, t1, e(arb(a)/(2*N)))
        if all(bool(lo(g) > 0) for g in Gs):
            marg = lo(Gs[0])
            for g in Gs[1:]: marg = marg.min(lo(g))
            return z, u, Zs, env, om, marg
    return None
if __name__ == '__main__':
    N0, N1, OUT = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    XLO = Fr(sys.argv[4]) if len(sys.argv) > 4 else Fr(1, 6); XHI = Fr(sys.argv[5]) if len(sys.argv) > 5 else Fr(1, 5)
    f = open(OUT, 'w'); cnt = 0; mm = None; mZ = None; mZ0 = None
    for N in range(N0, N1 + 1):
        for a in range(1, N):
            if gcd(a, N) != 1 or not (XLO <= Fr(a, N) < XHI): continue
            r = check(a, N)
            if r is None:
                print('SEEDS FAILED at %d/%d' % (a, N), flush=True); sys.exit(1)
            z, u, Zs, env, om, marg = r
            zl = [lo(Zs[s]) for s in (0, 1, -1)]
            f.write('%d %d %s %s %s %s %s %s %s %s\n' % (a, N, fdn(zl[0], 6), fdn(zl[1], 6), fdn(zl[2], 6),
                    fup(env[1], 6), fup(env[-1], 6), fup(arb(om.abs_upper()), 6), fdn(marg, 6), fup(env[0], 6)))
            cnt += 1; mm = marg if mm is None else mm.min(marg)
            zz = zl[1].min(zl[2]); mZ = zz if mZ is None else mZ.min(zz)
            mZ0 = zl[0] if mZ0 is None else mZ0.min(zl[0])
        f.flush()
    print('SEEDS PASSED: %d seeds %d<=n<=%d in [%s,%s); min|Z|>=%s; min|Z^pm|>=%s; min margin>=%s' % (cnt, N0, N1, XLO, XHI, fdn(mZ0), fdn(mZ), fdn(mm)), flush=True)
