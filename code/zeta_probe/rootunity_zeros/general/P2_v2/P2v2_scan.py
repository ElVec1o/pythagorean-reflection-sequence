
# Scan A_+ = (He+Ho)/2, A_- = (He-Ho)/2 for odd N in the P2 window a/N in (0,0.0804),
# looking for (i) how small |A+*A-| gets, (ii) any two-term/self-similar recursion
# in the partial sums (analogue of Z_N's renormalisation to Z_q), and (iii) whether the
# summands show Diophantine-hazard structure (denominators (1-zeta^j) small only near j~N).
import sys, math
from mpmath import mp, mpc, exp, pi, sqrt, nstr, fabs, log

mp.dps = 30

def heads(a, N):
    z = exp(2j*pi*a/N); c = -2*(1-z)
    # cache the running Pochhammer prod_{j=1}^{m}(1-z^j) incrementally
    poch = [mpc(1)]*(N)  # poch[m] = prod_{j=1}^m (1-z^j), m from 0..N-1
    cur = mpc(1)
    for j in range(1, N):
        cur *= (1 - z**j)
        poch[j] = cur
    s = c**(N//2) if N % 2 == 0 else sqrt(c**N)
    He = sum(c**r*z**(r*r)/poch[2*r] for r in range((N-1)//2+1))
    Ho = sum(c**k*z**(k*k)/poch[2*k-N] for k in range((N+1)//2, N))/s
    return z, c, He, Ho

def scan_odd(Ns, amax=0.0804):
    rows = []
    for N in Ns:
        if N % 2 == 0: continue
        for a in range(1, N):
            if math.gcd(a, N) != 1: continue
            if a/N > amax: continue
            z, c, He, Ho = heads(a, N)
            Ap, Am = (He+Ho)/2, (He-Ho)/2
            prod = fabs(Ap*Am)
            rows.append((a, N, float(a/N), float(fabs(Ap)), float(fabs(Am)), float(prod)))
    return rows

if __name__ == '__main__':
    Ns = list(range(3, 152, 2))
    rows = scan_odd(Ns)
    rows.sort(key=lambda r: r[5])
    print("N total cases:", len(rows))
    print("10 smallest |A+ A-|:")
    for r in rows[:10]:
        print("a=%d N=%d a/N=%.5f |A+|=%.6g |A-|=%.6g |A+A-|=%.6g" % r)
    print("10 largest |A+ A-|:")
    for r in rows[-10:]:
        print("a=%d N=%d a/N=%.5f |A+|=%.6g |A-|=%.6g |A+A-|=%.6g" % r)
