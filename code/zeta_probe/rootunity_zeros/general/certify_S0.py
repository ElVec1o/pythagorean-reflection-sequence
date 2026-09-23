# certify_S0.py -- interval-arithmetic (mpmath.iv) certificate that S_0(zeta) != 0
# for every zeta = e^{2 pi i a/N}, gcd(a,N)=1, 1<=a<=N/2, 3<=N<=NMAX, log|2(1-zeta)| >= DELTA.
# Uses the exact reduction (S0_lemma.tex, Lemma 1):
#   S_0 = K * Sigma,  K = prod_j (1-zeta^j u)^{-(1/2 - ((-j) mod N)/N)}  (an exponential, never 0),
#   Sigma = sum_r zeta^{r^2} eps^r lam^{2r} / prod_{i=1}^{2r} (1 - zeta^i u),
#   lam = (1-w)^{1/N} (principal), u = eps*lam^2/c, c = -2(1-zeta), eps = e^{-2 pi i n0/N},
#   w = the root of c^N w = (1-w)^2 with |w|<1 (enclosed by a contraction argument).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 certify_S0.py [NMAX] [DELTA]
import sys
from math import gcd
from mpmath import iv, mp, mpf, mpc, exp, pi, log
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 60
DELTA = float(sys.argv[2]) if len(sys.argv) > 2 else 0.05
iv.dps = 50; mp.dps = 60

class C:  # rectangular complex interval
    __slots__ = ('re', 'im')
    def __init__(s, re, im=0): s.re = iv.mpf(re); s.im = iv.mpf(im)
    def __add__(s, o): return C(s.re + o.re, s.im + o.im)
    def __sub__(s, o): return C(s.re - o.re, s.im - o.im)
    def __mul__(s, o): return C(s.re*o.re - s.im*o.im, s.re*o.im + s.im*o.re)
    def inv(s):
        d = s.re**2 + s.im**2
        if mpf(d.a) <= 0: raise ValueError('division by interval containing 0')
        return C(s.re/d, -s.im/d)
    def absup(s): return mpf(iv.sqrt(s.re**2 + s.im**2).b)
    def abslo(s):
        def lo(x):
            A, B = mpf(x.a), mpf(x.b)
            return mpf(0) if A <= 0 <= B else min(abs(A), abs(B))
        return iv.sqrt(iv.mpf(lo(s.re))**2 + iv.mpf(lo(s.im))**2).a  # rigorous lower bound (rounded down)
def cis(num, den):  # e^{2 pi i num/den}, rigorous
    t = 2*iv.pi*iv.mpf(num)/den
    return C(iv.cos(t), iv.sin(t))
def ball(z0, rad):
    z0 = mpc(z0); return C(iv.mpf([z0.real - rad, z0.real + rad]), iv.mpf([z0.imag - rad, z0.imag + rad]))

def enclose_w(a, N):
    # floating guess
    z = exp(2j*pi*a/N); c = -2*(1-z); Cf = c**N
    w0 = 1/Cf
    for _ in range(200): w0 = (1-w0)**2/Cf
    cI = (C(1) - cis(a, N)) * C(-2)
    CI = C(1)
    for _ in range(N): CI = CI*cI
    # T(w) = (1-w)^2/C maps disk D(w0,rho) into itself and contracts if
    # |T(w0)-w0| + L rho <= rho,  L = 2(1+|w0|+rho)/|C|.
    rho = mpf(10)**-20 * max(abs(w0), mpf(10)**-300)
    Cinv = CI.inv()
    w0I = C(w0.real, w0.imag); one = C(1)
    Tw0 = (one - w0I)*(one - w0I)*Cinv
    resid = (Tw0 - w0I).absup()
    L = 2*(1 + abs(w0) + rho) * Cinv.absup()
    if not (L < 1 and resid + L*rho <= rho and abs(w0) + rho < 1):
        raise ValueError('w enclosure failed a=%d N=%d' % (a, N))
    return ball(w0, rho), cI

def sigma(a, N):
    n0 = 0 if (N % 2 == 1 or N % 4 == 0) else 1
    wI, cI = enclose_w(a, N)
    one = C(1)
    x = one - wI                       # Re x > 0 since |w|<1
    rho2 = x.re**2 + x.im**2
    ph = iv.atan2(x.im, x.re)           # principal arg (Re x > 0, so |ph| < pi/2)
    mod = iv.exp(iv.log(rho2)/(2*N))
    lam = C(mod*iv.cos(ph/N), mod*iv.sin(ph/N))
    eps = cis(-n0, N)
    u = eps*lam*lam*cI.inv()
    zp = [cis((a*i) % N, N) for i in range(N)]   # zeta^i
    tot = C(0); term = C(1); big = mpf(0)
    for r in range(N):
        t = zp[(r*r) % N] * term
        tot = tot + t; big = max(big, t.absup())
        # term_{r+1} = term_r * eps * lam^2 / ((1-zeta^{2r+1}u)(1-zeta^{2r+2}u))
        f = (one - zp[(2*r+1) % N]*u) * (one - zp[(2*r+2) % N]*u)
        term = term * eps * lam * lam * f.inv()
    return tot, big

bad = 0; cnt = 0; worst = (1e9, None)
for N in range(3, NMAX + 1):
    for a in range(1, N//2 + 1):
        if gcd(a, N) != 1: continue
        # rigorous test of l >= DELTA: |2(1-zeta)| = 4 sin(pi a/N) >= e^DELTA
        s = 4*iv.sin(iv.pi*iv.mpf(a)/N)
        if mpf(s.b) < mpf(iv.exp(iv.mpf(DELTA)).a): continue
        if mpf(s.a) < mpf(iv.exp(iv.mpf(DELTA)).b): print('borderline l, included', a, N)
        tot, big = sigma(a, N); cnt += 1
        lo = tot.abslo()
        lo = mpf(lo)
        if lo <= 0: bad += 1; print('NOT CERTIFIED', a, N, tot.re, tot.im)
        elif lo/big < worst[0]: worst = (float(lo/big), (a, N))
    print('N', N, 'done', flush=True) if N % 10 == 0 else None
print('cases', cnt, 'uncertified', bad, 'min |Sigma|_lo/max|term| =', worst)
print('ALL CERTIFIED' if bad == 0 else 'FAILURES')
