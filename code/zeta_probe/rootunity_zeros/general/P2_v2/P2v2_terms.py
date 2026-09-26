
# Which block-index rho dominates H_e = sum_rho c^rho zeta^{rho^2}/(zeta;zeta)_{2rho}?
from mpmath import mp, mpc, exp, pi, sqrt, fabs
mp.dps = 40
a, N = 10, 131
z = exp(2j*pi*a/N); c = -2*(1-z)
poch = [mpc(1)]*(N)
cur = mpc(1)
for j in range(1, N):
    cur *= (1 - z**j)
    poch[j] = cur
terms = []
for r in range((N-1)//2+1):
    t = c**r*z**(r*r)/poch[2*r]
    terms.append((r, float(fabs(t))))
terms.sort(key=lambda x: -x[1])
print("top 10 |term| by magnitude (rho, |term|):")
for r,v in terms[:10]:
    print(r, v)
print("rho=0 term magnitude:", terms and [v for r,v in terms if r==0])
print("max rho =", (N-1)//2)
