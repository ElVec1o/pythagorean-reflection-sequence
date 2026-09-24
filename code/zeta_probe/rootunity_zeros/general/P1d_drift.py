# P1d_drift.py -- Proposition 6 of P1d_lemma.tex: Lemma (1'') as literally stated (one seed, all N >= 151) is FALSE.
# Mechanism: a deep rational j/n0 (n0 odd) inside the seed's neighbourhood.  Along x_N = j/n0 + theta/(n0 N), theta = +-1,
# Theorem 1 + Lemma 5 at the seed j/n0 give
#     |Sigma_N(x_N)| / sqrt N  =  (|G*|/sqrt N) * P(N) * (1 +- B_{j/n0}),     P(N) := |exp(-Phi_N(eps)) * Main'_{j/n0}(x_N)|,
# and P(N) is computed here in Arb (point x, rigorous enclosure) for N far beyond any direct computation of Sigma_N.
# P(N) drifts exponentially in N (to 0 on one side, to infinity on the other) because Re g0(j/n0) != 0 for odd n0.
# Mode 'direct' also computes Sigma_N itself (Arb, O(N) terms) for moderate N, as an independent check of the formula.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1d_drift.py j n0 n2 N1 N2 ... [direct]
import sys
from math import gcd
from flint import arb, acb, ctx
ctx.prec = 256
PI = arb.pi(); I = acb(0, 1)
def e(x): return (2*arb.pi()*I*x).exp()     # pi recomputed at the current precision
def aup(z): return arb(z.abs_upper())
from P1d_cert import li2_ball, krawczyk
ctx.prec = 320                      # (P1d_cert sets 160 on import; reset here)

def setup_point(a, N):
    x = arb(a)/N; zeta = e(x); c = -2*(1 - zeta)
    X = c**N; B = 2 + X
    w = 2/(B*(1 + (1 - 4/(B*B)).sqrt())); assert bool(aup(w) < 1)   # small root of w^2-(2+X)w+1 (|B| large, branch-safe)
    lam2 = ((1 - w).log()*2/N).exp(); u0 = lam2/c
    th = arb(acb(u0.mid()).arg().mid()); lu = (u0*(-I*th).exp()).log() + I*th
    return x, zeta, c, u0, lu

def one_minus_e_frac(k, N):
    # 1 - e(k/N) for integer k, accurate also when k/N is near an integer (reduced residue + expm1)
    k %= N
    if 2*k > N: k -= N
    return -((2*arb.pi()*I*arb(k)/N).expm1())

def phi_eps(a, N, u0, lu, eps, nmax):
    # Phi_N(eps) = sum_{n>=1, N not| n} (u0^n/n) eps^n/(1 - zeta^{-n}); tail n>nmax: <= (N/4) sum |u0|^n/n
    s = acb(0)
    epsn = lambda n: acb(1) if eps == 1 else e(arb(-n % N)/N)
    for n in range(1, nmax+1):
        if n % N == 0: continue
        s += (n*lu).exp()/n*epsn(n)/one_minus_e_frac(-n*a, N)
    g = aup(u0); assert bool(g < 1)
    t = arb(N)/4*g**(nmax+1)/((nmax+1)*(1 - g))
    return s + acb(arb(0, t.upper()), arb(0, t.upper()))

def main_prime(p, q, x, lu, n2, d=None):
    # Main'_Z(x) for d = x - p/q > 0 (P1d_lemma.tex, eq. (Main'))
    if d is None: d = x - arb(p)/q
    assert bool(d > 0)
    U = (q*lu).exp()
    m = acb(0); Um = acb(U.mid())
    for _ in range(200): m = (I/(PI*q))*(1 - Um*e(-q*m)).log()
    rt = 2.0**(-(ctx.prec - 30)); B = None
    for _ in range(ctx.prec + 50):
        B = krawczyk(q, U, acb(m.mid()), rt)
        if B is not None: break
        rt *= 2
    t0 = B; W0 = U*e(-q*t0)
    F2 = PI*I*(1 + W0)/(1 - W0); A = abs(F2)/2; alpha = (PI - F2.arg())/2
    F0 = PI*I*t0*t0/2 + li2_ball(W0, 200)/(2*PI*I*q*q)
    S = acb(0)
    for k in range(q):
        gk = sum((e(arb(((-nu*nu - k*nu)*p) % q)/q) for nu in range(q)), acb(0))/q
        Bv = -(1 - W0).log()/(2*q)
        for n in range(1, n2+1):
            if n % q: Bv += (n*lu).exp()/n/(1 - e(-n*x))*e(arb((k*n*p) % q)/q)*e(-n*t0)
        S += gk*Bv.exp()
    return (I*(alpha - PI/4)).exp()*(PI/(2*A)).sqrt()*(F0/d).exp()*S

def sigma_direct(a, N):
    n0 = 1 if N % 4 == 2 else 0
    old = ctx.prec; ctx.prec = 200 + N//2
    x, zeta, c, u0, lu = setup_point(a, N)
    eps = e(arb(-n0)/N); u = eps*u0; l2e = eps*u0*c
    zp = [e(arb((a*i) % N)/N) for i in range(N)]
    S = acb(0); term = acb(1)
    for r in range(N):
        S += zp[(r*r) % N]*term
        term = term*l2e/((1 - zp[(2*r+1) % N]*u)*(1 - zp[(2*r+2) % N]*u))
    ctx.prec = old
    return S

if __name__ == '__main__':
    args = sys.argv[1:]; direct = args[-1] == 'direct'
    if direct: args = args[:-1]
    j, n0, n2 = int(args[0]), int(args[1]), int(args[2])
    for Ns in args[3:]:
        for th in (1, -1):
            N = int(float(Ns))
            ctx.prec = max(320, int(2.5*N.bit_length()) + 200)   # adaptive: d ~ 1/(n0 N) must be resolved
            while (j*N + th) % n0 or gcd((j*N + th)//n0, N) != 1: N += 1
            a = (j*N + th)//n0
            x, zeta, c, u0, lu = setup_point(a, N)
            n0N = 1 if N % 4 == 2 else 0
            eps = e(arb(-n0N)/N)
            Ph = phi_eps(a, N, u0, lu, 1 if n0N == 0 else eps, 700)
            dd = arb(n0*a - j*N)/(n0*N)                  # exact d = x - j/n0
            if th > 0: M = main_prime(j, n0, x, lu, n2, dd)
            else:      # d<0: conjugation (Lemma 2): Main'_{j/n0}(x) = conj Main'_{(n0-j)/n0}(1-x); u0(1-x) = conj u0(x)
                M = main_prime(n0 - j, n0, 1 - x, lu.conjugate(), n2, -dd).conjugate()
            P = abs((-Ph).exp()*M)
            gfac = arb(2).sqrt() if N % 2 == 0 else arb(1)
            line = '%d/%d theta=%+d N=%d (N%%4=%d): predicted |Sigma|/sqrtN = (|G*|/sqrtN) P(N) = %s' % (j, n0, th, N, N % 4, (gfac*P).str(6, radius=False))
            if direct and N <= 40000:
                S = sigma_direct(a, N)
                line += '   direct Arb |Sigma|/sqrtN = %s  (ratio %s)' % ((abs(S)/arb(N).sqrt()).str(8, radius=False), (abs(S)/arb(N).sqrt()/(gfac*P)).str(8, radius=False))
            print(line, flush=True)
