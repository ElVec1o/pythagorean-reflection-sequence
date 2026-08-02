#!/usr/bin/env python3
"""
t2abs_certificate.py -- certificate for Lemma lem:T2abs of paper 2.

|T_2| <= 0.17 tau^{1/4} <= 0.064 < 1 for tau <= 0.02, by absolute values on the boundary of

    R = { 1/2 <= Re s <= 2w,  |Im s| <= X/2 },

which lies WHOLLY INSIDE the lem:Bbounded strip S -- so no bound on B_s outside S is needed.
The residues n > 2w are not enclosed; they are added back as an elementary tail using
0 <= g_n <= 1 at integers (B_n = sum_{i<=2n} phi(i tau) - n phi(tau) >= n phi(tau) >= 0).

Amplitude, honestly:  |B_s| <= (tau^2/24)|M^3/3 + M^2/2 - M/3| + 0.02 tau^{3/2}  where |2s| <= 2w
(this is eq:Btrunc with P_1(M) - s written out in full; dropping the M^2/2 and -M/3 terms gives an
inequality that is FALSE on the contour, by about 6% at tau = 0.02), and |g_s| <= 1 + e^{30.3
sqrt(tau)} elsewhere on the boundary from eq:Bbounds.

Two things this script gets right that a naive version does not:
  * it integrates by ADAPTIVE QUADRATURE PIECEWISE between the region breakpoints.  The amplitude
    majorant jumps by a factor ~1500 at |2s| = 2w, and a uniform Riemann sum straddling that jump
    converges to the answer FROM BELOW: a uniform N=700 sum reports 0.1366 where the converged
    value is 0.1443.
  * it evaluates at X = w, not X = W.  lem:infpoles uses X = w, and it is the worse of the two by
    about 11%.

Arithmetic model: mpmath mpf at dps=30 with adaptive quadrature, not interval arithmetic.
"""
from mpmath import mp, mpf, mpc, exp, sqrt, pi, gamma, sin as msin, quad, factorial
import mpmath
mp.dps = 30

def Bb(s, tau):                       # honest eq:Btrunc bound on |B_s|
    M = 2*s
    P = M**3/3 + M**2/2 - M/3         # P1(M) - s, exactly
    return (tau**2/24)*abs(P) + mpf('0.02')*tau**mpf(1.5)

def gb(s, tau, w, crude):
    if abs(2*s) <= 2*w:
        b = Bb(s, tau); return min(crude, b*exp(b))
    return crude

def kern(s, X):
    try: return abs(X**(2*s)/gamma(2*s+1)*pi/msin(pi*s))
    except Exception: return mpf(0)

print(" tau       horiz      vert(1/2)  vert(2w)   tail(n>2w)   TOTAL     /tau^{1/4}")
worst = mpf(0)
for ts in ['0.02','0.0126651','0.01','0.005','0.001','1e-4','1e-5']:
    tau = mpf(ts); w = sqrt(2/tau); X = w        # <-- the case lem:infpoles uses
    crude = 1 + exp(mpf('30.3')*sqrt(tau))
    brk = sqrt(max(mpf(0), w*w - (X/2)**2))      # where |2s| crosses 2w on the edge
    def fh(sg): 
        s = mpc(sg, X/2); return kern(s, X)*gb(s, tau, w, crude)
    hor = 0
    for a,b in [(mpf('0.5'), brk), (brk, 2*w)]:
        if b > a: hor += quad(fh, [a, b], maxdegree=6)
    hor *= 2
    fv1 = lambda t: kern(mpc(mpf('0.5'), t), X)*gb(mpc(mpf('0.5'), t), tau, w, crude)
    ver1 = quad(fv1, [-X/2, 0, X/2], maxdegree=6)
    fv2 = lambda t: kern(mpc(2*w, t), X)*gb(mpc(2*w, t), tau, w, crude)
    ver2 = quad(fv2, [-X/2, 0, X/2], maxdegree=6)
    # residues n > 2w, using 0 <= g_n <= 1 (B_n = sum phi(i tau) - n phi(tau) >= 0)
    tail = mpf(0); n0 = int(2*w)+1
    for n in range(n0, n0+400):
        t = X**(2*n)/factorial(2*n); tail += t
        if t < mpf('1e-60')*max(tail, mpf('1e-60')): break
    tot = (hor+ver1+ver2)/(2*pi) + tail
    r = tot/tau**mpf(0.25); worst = max(worst, r)
    print(f"  {ts:>9} {mp.nstr(hor/(2*pi),4):>10} {mp.nstr(ver1/(2*pi),4):>10} {mp.nstr(ver2/(2*pi),4):>10} {mp.nstr(tail,3):>11}  {mp.nstr(tot,5):>9}  {mp.nstr(r,5)}")
print(f"\n  worst ratio on tau <= 0.02 (X=w, honest amplitude, converged): {mp.nstr(worst,5)}")
for C in ['0.17','0.20','0.25']:
    print(f"    |T2| <= {C} tau^{{1/4}}  =>  at tau=0.02: {mp.nstr(mpf(C)*mpf('0.02')**mpf(0.25),4)}   valid? {worst <= mpf(C)}")
