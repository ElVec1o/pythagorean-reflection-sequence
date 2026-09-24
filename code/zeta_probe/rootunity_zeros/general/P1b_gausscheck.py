# P1b: exact (integer-phase) evaluation of the leading saddle-sum factor
#   G = sum_{m in M_theta, surviving parity} e^{-i pi m^2 N/(2 q theta)} * t_m * W_m/W_{m0}
# using the PROVED phase law / masking (report_P1b.md sec. 1) and the VERIFIED twist rule
# t_m = e^{-i pi m/theta} for N = 2 mod 4 (t_m = 1 otherwise). Reports min |G|/sqrt(#terms) per class.
# All four N classes. Only admissible (a,N): a=(pN+theta)/q integer, gcd(a,N)=1, a>=1.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1b_gausscheck.py QMAX THMAX
import sys, cmath
from math import gcd, pi, sin, exp, sqrt
QMAX, THMAX = int(sys.argv[1]), int(sys.argv[2])
worst = {}
for q in range(2, QMAX+1):
    for p in range(1, q//2+1):
        if gcd(p, q) != 1 or 4*sin(pi*p/q) < exp(0.05): continue
        for th in [t for t in range(-THMAX, THMAX+1) if t]:
            ms = list(range(0, 2*th)) if th > 0 else list(range(0, 2*th, -1))
            if q % 2 == 1: live = ms; wph = lambda m: -pow(4*p, -1, q)*m*m/q          # W_m/W_0 = e(-inv(4p) m^2/q)
            else:
                m0 = 0 if q % 4 == 0 else 1; live = [m for m in ms if (m - m0) % 2 == 0]
                k = pow(p, -1, q); wph = lambda m, k=k, m0=m0: -k*((m*m - m0*m0)//4)/q
            for N in range(4*q*abs(th), 4*q*abs(th)*3):
                if (p*N+th) % q: continue
                a = (p*N+th)//q
                if a < 1 or gcd(a, N) != 1: continue
                G = 0
                for m in live:
                    ph = -m*m*N/(4*q*th) + wph(m) + (-m/(2*th) if N % 4 == 2 else 0)
                    G += cmath.exp(2j*pi*ph)
                r = abs(G)/sqrt(len(live))
                key = ('q odd' if q % 2 else 'q=%d mod 4' % (q % 4), N % 4)
                if key not in worst or r < worst[key][0]: worst[key] = (r, p, q, th, N)
for k in sorted(worst): print(k, 'min |G|/sqrt(#live) = %.6f at p,q,theta,N=%s' % (worst[k][0], worst[k][1:]))
