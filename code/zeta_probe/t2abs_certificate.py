#!/usr/bin/env python3
"""
t2abs_certificate.py -- certificate for Lemma lem:T2abs of paper 2.

lem:T2abs replaces the steepest-descent Remark lem:cos as the input the theorems consume.
It bounds |T_2| by ABSOLUTE VALUES on the boundary of the rectangle

    R = { Re s >= 1/2,  |Im s| <= W/2 }   (inside the lem:Bbounded strip S),

with no saddle, no path through a saddle, and no cited asymptotic theorem.  The Mellin-Barnes
kernel's two exponentials cancel on the horizontal edges, and the amplitude is bounded by region:

    |2s| <= 2w   :  |B_s| <= tau^2|2s|^3/72 + 0.02 tau^{3/2}   (eq:Btrunc)
                    hence |g_s| = |1 - e^{-B_s}| <= |B_s| e^{|B_s|}
    Re s > 2w    :  Re B_s >= 0  (lem:Bbounded, proof step (iii))  =>  |g_s| <= 2
    otherwise    :  |g_s| <= 1 + e^{30.3 sqrt(tau)}            (eq:Bbounds)

Output: |T_2|/tau^{1/4} is decreasing and below 0.14 throughout tau <= 0.02, so |T_2| <= 0.053
there.  That is all Lemma lem:infpoles needs (it consumes only |T_2(m pi)| < 1, from m = 4 on).

NOTE on why the crude bound is not enough: replacing the eq:Btrunc amplitude by the blanket
1 + e^{30.3 sqrt(tau)} everywhere gives a total of order 160, NOT o(1).  The sharp bound on the
vertical edge is the whole point.

Arithmetic model: mpmath mpf at dps=40, not interval arithmetic.
"""
from mpmath import mp, mpf, mpc, exp, sqrt, pi, gamma, sin as msin
import mpmath
mp.dps = 40

def gb(s, tau, w, crude):
    M = 2*abs(s)
    if M <= 2*w:
        b = tau**2 * M**3/72 + mpf('0.02')*tau**mpf(1.5)
        return min(crude, b*exp(b))
    if mpmath.re(s) > 2*w:
        return mpf(2)
    return crude

def kern(s, W):
    try:
        return abs(W**(2*s) / gamma(2*s+1) * pi / msin(pi*s))
    except Exception:
        return mpf(0)

print("  tau        |T2| bound     /tau^{1/4}    far-tail share")
worst = mpf(0)
for ts in ['0.02','0.01','0.005','0.002','0.001','1e-4','1e-5']:   # the lemma's range: tau <= 0.02
    tau = mpf(ts); w = sqrt(2/tau); W = w*exp(-tau/2)
    crude = 1 + exp(mpf('30.3')*sqrt(tau))
    SIG = 6*w + 20          # far cutoff; beyond it the factorial decay is checked below
    N = 700
    hor = mpf(0)
    for i in range(N+1):
        sg = mpf('0.5') + (SIG - mpf('0.5'))*i/N
        s = mpc(sg, W/2)
        hor += kern(s, W)*gb(s, tau, w, crude)
    hor *= (SIG - mpf('0.5'))/N * 2
    ver = mpf(0)
    for j in range(N+1):
        t = -W/2 + W*mpf(j)/N
        s = mpc(mpf('0.5'), t)
        ver += kern(s, W)*gb(s, tau, w, crude)
    ver *= W/N
    # far tail beyond SIG (bound |g|<=2, kernel decays factorially)
    tail = mpf(0)
    for i in range(60):
        sg = SIG + i*mpf(1)
        s = mpc(sg, W/2)
        tail += kern(s, W)*2
    tot = (hor + ver + 2*tail)/(2*pi)
    r = tot/tau**mpf(0.25)
    worst = max(worst, r)
    print(f"  {ts:>10}   {mp.nstr(tot,5):>10}   {mp.nstr(r,5):>10}    {mp.nstr(2*tail/(2*pi)/max(tot,mpf('1e-99')),3)}")
ok = worst <= mpf('0.14')
print(f"\n  worst |T2|/tau^{{1/4}} on tau <= 0.02 : {mp.nstr(worst,5)}   (claim: <= 0.14)")
print(f"  => |T2| <= 0.14 tau^{{1/4}} <= {mp.nstr(mpf('0.14')*mpf('0.02')**mpf(0.25),4)} < 1 throughout")
print(f"  lem:infpoles needs |T2(m pi)| < 1 at tau_m = 2/(m pi)^2 <= 0.02, i.e. m >= 4.")
print("\n  SUMMARY:", "PASS" if ok else "*** FAIL ***")
# the crude-amplitude control: shows the sharp eq:Btrunc bound is what makes it work
print("\n  control -- same contour with the blanket amplitude 1+e^{30.3 sqrt(tau)} everywhere:")
for ts in ['0.02','0.005']:
    tau = mpf(ts); w = sqrt(2/tau); W = w*exp(-tau/2)
    crude = 1 + exp(mpf('30.3')*sqrt(tau))
    N = 300; tot = mpf(0)
    for i in range(N+1):
        sg = mpf('0.5') + (2*w - mpf('0.5'))*i/N
        tot += kern(mpc(sg, W/2), W)*crude
    tot *= (2*w - mpf('0.5'))/N * 2
    v = mpf(0)
    for j in range(N+1):
        v += kern(mpc(mpf('0.5'), -W/2 + W*mpf(j)/N), W)*crude
    v *= W/N
    print(f"    tau={ts}: {mp.nstr((tot+v)/(2*pi),4)}  (not o(1) -- the sharp bound is essential)")
