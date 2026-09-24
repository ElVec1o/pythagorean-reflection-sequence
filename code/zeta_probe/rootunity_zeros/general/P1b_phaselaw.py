# P1b item (3): machine check of the PROVED phase law and masking (report_P1b.md sec. 1), for general u (|u|<1):
#   q odd:   W_m = W_0 e(-inv(4p) m^2/q)
#   q even:  W_{m+2} = W_m e(-k(m+1)/q), k = inv(p) mod q;  A(phi_m)=0 for m odd (4|q) / m even (q=2 mod 4)
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1b_phaselaw.py QMAX
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, sin, findroot, nstr
mp.dps = 30
def e(x): return exp(2j*pi*x)
def WA(p, q, u, m):
    z0 = e(mpf(p)/q); U = u**q
    f0 = findroot(lambda f: 2j*f - (mpf(2)/q)*log(1-U*exp(2j*q*f)), mpc(0, 0.01))
    fs = f0 + pi*m/q; V = u*exp(2j*fs)
    Cf = sqrt((1-V**q)/(1-U))
    for i in range(1, q+1): Cf *= ((1-z0**i*u)/(1-z0**i*V))**(mpf(i)/q)
    A = mpc(0)
    for rho in range(q):
        B = z0**(rho*rho)*exp(2j*rho*fs)
        for i in range(1, 2*rho+1): B /= (1-z0**i*V)
        A += B
    return Cf*A, A
worst = [0, 0, 1e9]
for q in range(2, int(sys.argv[1])+1):
    for p in range(1, q):
        if gcd(p, q) != 1 or 4*sin(pi*p/q) < exp(0.05): continue
        for u in (-1/(2*(1-e(mpf(p)/q))), -0.93/(2*(1-e(mpf(p)/q)))*e(mpf('0.0137'))):
            W = [WA(p, q, u, m) for m in range(2*q)]
            if q % 2:
                r = pow(4*p, -1, q)
                for m in range(2*q): worst[0] = max(worst[0], abs(W[m][0] - W[0][0]*e(-mpf(r*m*m)/q))/abs(W[0][0]))
            else:
                k = pow(p, -1, q); dead = 1 if q % 4 == 0 else 0
                for m in range(2*q-2):
                    if m % 2 == dead: worst[1] = max(worst[1], abs(W[m][1])/abs(W[1-dead][1]))
                    else: worst[0] = max(worst[0], abs(W[m+2][0] - W[m][0]*e(-mpf(k*(m+1))/q))/abs(W[m][0]))
                worst[2] = min(worst[2], min(abs(W[m][1]) for m in range(2*q) if m % 2 != dead))
print('max rel. deviation from phase law:', nstr(worst[0], 3), ' max |A| at masked saddles / |A| live:', nstr(worst[1], 3), ' min live |A| (even q):', nstr(worst[2], 4))
