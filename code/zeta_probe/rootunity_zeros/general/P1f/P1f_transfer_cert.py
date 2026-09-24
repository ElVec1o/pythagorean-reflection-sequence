# P1f_transfer_cert.py -- Arb (python-flint) certificate of the Task-C conditions of P1f_lemma.tex (Theorem C) at
# zeta = e(a/N), for all reduced a/N with N <= 5a <= 4N and NMIN <= N <= NMAX.  FAILS LOUDLY (exit 1).
# Encloses, by the exact finite formula (as Lemma Zk of P1e):
#   Z   = sum_k g0_k e^{Phi(zeta^k)},   Z^pm = sum_k gpm_k e^{Phi(zeta^k)},
#   g_k = (1/N) sum_nu zeta^{-nu^2 - k nu},  gpm_k = (1/N) sum_nu zeta^{-nu^2 -+ nu - k nu},
#   Phi(Y) = sum_{n<=M, N!|n} u0^n Y^n/(n(1-zeta^{-n})) + rigorous tail,  u0 = lambda^2/c,
# then omega = Z^-/(u0 Z^+), t1* = -(1+omega)/2, and checks that the following are certified nonzero:
#   Z, Z^+;  1 - gU t1*, 1 - gV t1* (gU = zeta/(1-zeta^2), gV = zeta/(1-zeta));
#   for both roots x = +-sqrt(zeta):  t1* + (1+x)/(2x)  and  t1*(1-x+zeta)/(1+zeta) + 1/(2x).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1f_transfer_cert.py NMIN NMAX
import sys
from math import gcd
from flint import arb, acb, ctx
sys.path.insert(0, '..')
from dround import fdn
PI = arb.pi(); I = acb(0, 1)
def e(y): return (2*PI*I*y).exp()
def enc(a, N):
    z = e(arb(a)/N); c = -2*(1 - z)
    lX = N*arb(c.abs_lower()).log()
    if bool(lX < 600):
        X = c**N; B = 2 + X; w = 2/(B*(1 + (1 - 4/(B*B)).sqrt()))
        u = ((1 - w).log()*2/N).exp()/c
    else:
        u = 1/c; eps = arb(2)*(-lX).exp()*3/N
        u = u*(1 + acb(arb(0, eps.upper()), arb(0, eps.upper())))
    ua = arb(u.abs_upper())
    M = int(60/(-float(ua.log().mid()))) + 10
    ET = [e(arb(j)/N) for j in range(N)]
    def gam(sh):
        return [sum((ET[(-(v*v + sh*v + k*v)*a) % N] for v in range(N)), acb(0))/N for k in range(N)]
    G0, Gp, Gm = gam(0), gam(1), gam(-1)
    Ph = [acb(0)]*N; un = acb(1)
    for n in range(1, M+1):
        un = un*u
        if n % N == 0: continue
        cn = un/(n*(1 - ET[(-n*a) % N]))
        for k in range(N): Ph[k] = Ph[k] + cn*ET[(k*n*a) % N]
    tail = arb(N)/4*ua**(M+1)/((M+1)*(1 - ua))   # |1-zeta^{-n}| >= 4/N for N !| n
    rt = acb(arb(0, tail.upper()), arb(0, tail.upper()))
    b = [(ph + rt).exp() for ph in Ph]
    Z = sum((g*x for g, x in zip(G0, b)), acb(0)); Zp = sum((g*x for g, x in zip(Gp, b)), acb(0)); Zm = sum((g*x for g, x in zip(Gm, b)), acb(0))
    return z, u, Z, Zp, Zm
def nz(v): return bool(arb(v.abs_lower()) > 0)
def check(a, N):
    for pr in (128, 256, 512, 1024):
        ctx.prec = pr
        z, u, Z, Zp, Zm = enc(a, N)
        if not (nz(Z) and nz(Zp)): continue
        om = Zm/(u*Zp); t1 = -(1 + om)/2
        gU = z/(1 - z*z); gV = z/(1 - z)
        qs = [1 - gU*t1, 1 - gV*t1]
        sq = z.sqrt()
        for x in (sq, -sq): qs += [t1 + (1 + x)/(2*x), t1*(1 - x + z)/(1 + z) + 1/(2*x)]
        if all(nz(v) for v in qs):
            return min([arb(v.abs_lower()) for v in [Z, Zp] + qs], key=lambda y: float(y.mid())), om
    return None, None
if __name__ == '__main__':
    N0, N1 = int(sys.argv[1]), int(sys.argv[2]); cnt = 0; mn = None
    for N in range(N0, N1+1):
        for a in range(1, N):
            if gcd(a, N) != 1 or not (N <= 5*a <= 4*N): continue
            m, om = check(a, N)
            if m is None:
                print('CERT FAILED at %d/%d' % (a, N), flush=True); sys.exit(1)
            cnt += 1; mn = m if mn is None else mn.min(m)
        print('N<=%d: %d cases certified, min certified modulus >= %s' % (N, cnt, fdn(mn)), flush=True)
    print('CERT PASSED: %d cases, %d<=N<=%d, all conditions certified nonzero, min modulus >= %s' % (cnt, N0, N1, fdn(mn)), flush=True)
