
# Test whether A_+(a/N), A_-(a/N) converge to a fixed limit as a/N -> p/q (q small, fixed)
# with N -> infinity along good rational approximants. This is the direct analogue of
# testing whether Lemma R's renormalisation (S_amp -> (1-w_q)^{-1/2q} Z_q(p/q)) has any
# counterpart for the block-model amplitudes A_+, A_-.
import math
from mpmath import mp, mpc, exp, pi, sqrt, fabs

mp.dps = 40

def heads(a, N):
    z = exp(2j*pi*a/N); c = -2*(1-z)
    poch = [mpc(1)]*(N)
    cur = mpc(1)
    for j in range(1, N):
        cur *= (1 - z**j)
        poch[j] = cur
    s = sqrt(c**N)
    He = sum(c**r*z**(r*r)/poch[2*r] for r in range((N-1)//2+1))
    Ho = sum(c**k*z**(k*k)/poch[2*k-N] for k in range((N+1)//2, N))/s
    return He, Ho

# approach p/q = 1/13 from above via a = round(N/13)
q = 13
print("Approaching a/N -> 1/%d :" % q)
for N in [13, 27, 53, 79, 131, 261, 521, 1041]:
    if N % 2 == 0: N += 1
    a = round(N/q)
    if a == 0: a = 1
    if math.gcd(a, N) != 1:
        continue
    He, Ho = heads(a, N)
    Ap, Am = (He+Ho)/2, (He-Ho)/2
    print("a=%d N=%d a/N=%.8f |A+|=%.8g |A-|=%.8g arg(A+)=%.6g arg(A-)=%.6g" %
          (a, N, a/N, fabs(Ap), fabs(Am), float(mp.arg(Ap)), float(mp.arg(Am))))
