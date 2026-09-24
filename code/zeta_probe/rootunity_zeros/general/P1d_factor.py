# P1d_factor.py -- VERIFIED (numerical, high precision) check of Theorem 1 (Gauss-sum factorisation) of P1d_lemma.tex:
#   Sigma_N(a/N) = G*_N(a) * exp(-Phi_N(eps)) * Z_N(a/N),   Z_N = sum_{n>=0} psi_n zeta^{-n^2},  exp(Phi_N(Y)) = sum psi_n Y^n,
#   Phi_N(Y) = sum_{n>=1, N not| n} (u0^n/n) Y^n / (1 - zeta^{-n}),  u0 = lam^2/c,  G*_N = sum_{r mod N} e((a r^2 - n0 r)/N).
# Sigma_N is computed directly (Arb, as in P1c_band_arb.py); the right side with truncated series (truncation checked by
# the size of the last terms).  All residue classes of N mod 4.  Also prints |G*|^2/N (1 for N odd, 2 for N even).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1d_factor.py NMIN NMAX STEP [NT]
import sys
from math import gcd
from flint import acb, arb, ctx
NMIN, NMAX, STEP = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); NT = int(sys.argv[4]) if len(sys.argv) > 4 else 700
def cis(k, N): return (2*arb.pi()*k/N*acb(0, 1)).exp()
worst = 0; cnt = 0
for N in range(NMIN, NMAX + 1, STEP):
    for a in (N//3 + 1, N//5 + 2, (2*N)//7 + 1, N//2 - 1, N//9 + 1):
        if gcd(a, N) != 1 or not (0 < a < N): continue
        ctx.prec = 200 + N//2
        n0 = 1 if N % 4 == 2 else 0
        z = cis(a, N); c = -2*(1 - z); X = c**N; B = 2 + X; s = (B*B - 4).sqrt(); d1, d2 = B + s, B - s
        den = d1 if abs(d1).mid() >= abs(d2).mid() else d2
        w = 2/den; lam2 = ((1 - w).log()*2/N).exp(); eps = cis(-n0, N); u = eps*lam2/c; u0 = lam2/c
        if not (abs(u0) < 1): continue          # off the arc
        zp = [cis((a*i) % N, N) for i in range(N)]
        S = acb(0); term = acb(1)
        for r in range(N):
            S += zp[(r*r) % N]*term
            term = term*eps*lam2/((1 - zp[(2*r+1) % N]*u)*(1 - zp[(2*r+2) % N]*u))
        # right-hand side
        cn = [acb(0)]*NT; pw = acb(1)
        for n in range(1, NT):
            pw = pw*u0
            if n % N: cn[n] = pw/n/(1 - cis((-n*a) % N, N))
        Phieps = acb(0); ep = acb(1)
        for n in range(1, NT): ep = ep*eps; Phieps += cn[n]*ep
        psi = [acb(1)]
        for n in range(1, NT):
            psi.append(sum((k*cn[k]*psi[n-k] for k in range(1, n+1)), acb(0))/n)
        Z = sum((psi[n]*cis((-a*n*n) % N, N) for n in range(NT)), acb(0))
        G = sum((cis((a*r*r - n0*r) % N, N) for r in range(N)), acb(0))
        rhs = G*(-Phieps).exp()*Z
        rel = abs(S - rhs)/abs(S)
        worst = max(worst, float(rel.mid())); cnt += 1
        print('N=%d (N%%4=%d) a=%d |Sigma|=%s rel.diff=%.2e |G*|^2/N=%s last|psi|=%.1e' % (
            N, N % 4, a, abs(S).str(8, radius=False), float(rel.mid()), (abs(G)**2/N).str(5, radius=False), float(abs(psi[-1]).mid())), flush=True)
print('cases %d, max relative difference %.2e' % (cnt, worst))
