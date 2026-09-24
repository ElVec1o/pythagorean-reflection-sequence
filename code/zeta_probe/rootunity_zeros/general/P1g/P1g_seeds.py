# P1g_seeds.py -- RIGOROUS (Arb, python-flint) level-n data at every reduced seed j/n, N0 <= n <= N1, n <= 5j <= 4n, j/n != 1/2.
# Exact finite formula (Lemma Zk of P1e, shifted weights; P1g Lemma Zpm):
#   Z^s_n(j/n) = sum_k gam^s_k e^{Phi_n(zeta^k)},  gam^s_k = (1/n) sum_nu zeta^{-nu^2 - s nu - k nu},  s in {0,+1,-1},
#   env^s = sum_k |gam^s_k| |(1-w_n)^{-1/2n} e^{Phi_n(zeta^k)}|        (the loss envelope of Lemma R),
#   omega = Z^-/(u0 Z^+),  t1 = -(1+omega)/2,
#   normalised transfer factors (P1g Def. G):  G1 = (1-z^2)/z - t1,  G2 = (1-z)/z - t1,
#       G3(x) = t1 + (1+x)/(2x),  G4(x) = t1 (1-x+z) + (1+z)/(2x),   x = +-sqrt(z).
# FAILS LOUDLY (exit 1) if any |Z^s| or any |G_i| is not certified > 0.  Writes one line per seed to OUT:
#   j n  |Z|lo |Z+|lo |Z-|lo  env+ env-  |omega|up  margin_lo  (all decimal, directed rounding)  omega_mid
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1g_seeds.py N0 N1 OUT
import sys
from math import gcd
from flint import arb, acb, ctx
sys.path.insert(0, '..')
from dround import fdn, fup
PI = arb.pi(); I = acb(0, 1)
def e(y): return (2*PI*I*y).exp()
def Gfactors(z, t1, X=None):
    # X: a square root of z (default principal); the pair {X, -X} is what matters, so X = e(x/2) avoids the branch cut at z=-1
    G = [(1 - z*z)/z - t1, (1 - z)/z - t1]
    s = z.sqrt() if X is None else X
    for x in (s, -s): G += [t1 + (1 + x)/(2*x), t1*(1 - x + z) + (1 + z)/(2*x)]
    return G
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
    env = {s: sum((arb(g.abs_upper())*arb((x*ew).abs_upper()) for g, x in zip(G[s], b)), arb(0)) for s in (1, -1)}
    return z, u, Zs, env
def lo(v): return arb(v.abs_lower())
def check(a, N):
    for pr in (128, 256, 512, 1024):
        ctx.prec = pr
        z, u, Zs, env = enc(a, N)
        if not all(bool(lo(Zs[s]) > 0) for s in (0, 1, -1)): continue
        om = Zs[-1]/(u*Zs[1]); t1 = -(1 + om)/2
        Gs = Gfactors(z, t1)
        if all(bool(lo(g) > 0) for g in Gs):
            marg = lo(Gs[0])
            for g in Gs[1:]: marg = marg.min(lo(g))
            return z, u, Zs, env, om, marg
    return None
if __name__ == '__main__':
    N0, N1, OUT = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    f = open(OUT, 'w'); cnt = 0; mm = None; mZ = None
    for N in range(N0, N1 + 1):
        for a in range(1, N):
            if gcd(a, N) != 1 or not (N <= 5*a <= 4*N) or 2*a == N: continue
            r = check(a, N)
            if r is None:
                print('SEEDS FAILED at %d/%d' % (a, N), flush=True); sys.exit(1)
            z, u, Zs, env, om, marg = r
            zl = [lo(Zs[s]) for s in (0, 1, -1)]
            f.write('%d %d %s %s %s %s %s %s %s %s %s\n' % (a, N, fdn(zl[0], 6), fdn(zl[1], 6), fdn(zl[2], 6),
                    fup(env[1], 6), fup(env[-1], 6), fup(arb(om.abs_upper()), 6), fdn(marg, 6),
                    om.real.mid().str(10, radius=False), om.imag.mid().str(10, radius=False)))
            cnt += 1; mm = marg if mm is None else mm.min(marg)
            zz = zl[1].min(zl[2]); mZ = zz if mZ is None else mZ.min(zz)
        f.flush()
        print('n<=%d: %d seeds, min|Z^pm|>=%s, min margin>=%s' % (N, cnt, fdn(mZ), fdn(mm)), flush=True)
    print('SEEDS PASSED: %d seeds %d<=n<=%d; min|Z^pm|>=%s; min margin>=%s' % (cnt, N0, N1, fdn(mZ), fdn(mm)), flush=True)
