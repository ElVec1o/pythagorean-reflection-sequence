# P1c: error of the P1a multi-saddle asymptotic as a function of the DISTANCE d = a/N - p/q (theta = qNd may be large).
# Uses the PROVED translation law: saddles phi_m = phi_0 + pi m/q, g_m(phi_m) = g_0(phi_0) - i pi^2 m^2/q^2 (one findroot).
# N odd only (eps=1). Prints err = min|Sigma/Main -+ 1| and K = err/|d|.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1c_dist.py p q d N1 N2 ...   (a = round((p/q+d) N), N odd, gcd(a,N)=1)
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, polylog, findroot, nstr
def exact_sigma(a, N, q):
    mp.dps = 40 + int(0.6*N/q + 30)
    z = exp(2j*pi*a/N); c = -2*(1-z); C = c**N; w = 1/C
    for _ in range(300): w = (1-w)**2/C
    lam = (1-w)**(mpf(1)/N); u = lam**2/c
    zp = [exp(2j*pi*((a*i) % N)/N) for i in range(N)]
    tot = mpc(0); term = mpc(1)
    for r in range(N):
        tot += zp[(r*r) % N]*term
        term = term*lam*lam/((1-zp[(2*r+1) % N]*u)*(1-zp[(2*r+2) % N]*u))
    return tot, u
def main(p, q, theta, N, u):
    z0 = exp(2j*pi*p/q); tau = 2*pi*mpf(theta)/(q*N); U = u**q
    g0 = lambda f: 1j*f**2 - (1j/q**2)*(polylog(2, U*exp(2j*q*f)) - polylog(2, U))
    f0 = findroot(lambda f: 2j*f - (mpf(2)/q)*log(1-U*exp(2j*q*f)), 1j*mpf('0.01'))
    G0 = g0(f0); V = u*exp(2j*f0); g2 = 2j + 4j*V**q/(1-V**q)   # V^q, g'' are m-independent
    pre = sqrt(2*pi*tau/(-g2))/(q*tau)*exp(G0/tau)
    tot = mpc(0)
    ms = range(0, 2*theta) if theta > 0 else range(0, 2*theta, -1)
    for m in ms:
        fs = f0 + pi*m/q; Vm = u*exp(2j*fs)
        Cf = sqrt((1-V**q)/(1-U))
        for i in range(1, q+1): Cf *= ((1-z0**i*u)/(1-z0**i*Vm))**(mpf(i)/q)
        A = mpc(0); T = mpc(1)
        for rho in range(q):
            A += z0**(rho*rho)*exp(2j*rho*fs)*T
            T /= (1-z0**(2*rho+1)*Vm)*(1-z0**(2*rho+2)*Vm)
        tot += exp(-1j*pi**2*m*m/(q*q*tau))*Cf*A
    return pre*tot
if __name__ == '__main__':
    p, q, d = int(sys.argv[1]), int(sys.argv[2]), mpf(sys.argv[3])
    for N in [int(x) for x in sys.argv[4:]]:
        if N % 2 == 0: N += 1
        a = int(mp.nint((mpf(p)/q + d)*N))
        while gcd(a, N) != 1 or (N % 2 == 0): N += 2; a = int(mp.nint((mpf(p)/q + d)*N))
        theta = q*a - p*N
        if theta == 0: continue
        S, u = exact_sigma(a, N, q); mp.dps = 40
        r = S/main(p, q, theta, N, u); e = min(abs(r-1), abs(r+1)); dd = mpf(theta)/(q*N)
        print('%d/%d N=%d a=%d theta=%d d=%s ratio=%s err=%s K=err/|d|=%s' % (p, q, N, a, theta, nstr(dd, 4), nstr(r, 5), nstr(e, 4), nstr(e/abs(dd), 4)), flush=True)
