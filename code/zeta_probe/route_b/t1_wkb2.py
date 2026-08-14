import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

def cocyc_y(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; yh.append(y)
    return yh

# The y-recursion in continuum: with u=w(1-t), t=q^n, the second-order recursion for the
# cocycle (x,y) becomes a Bessel/turning-point eq. The bulk dressing solution y(t) ~ 
# A * t^? * [sin/cos of phase]. Let me directly extract: define theta_n=u_n=w(1-q^n).
# Hypothesize y_n = R_n * sin(phi_n) with slowly-varying R_n. Use consecutive y to get R,phi.
# Then 1/(y_n y_{n-1}) ~ 1/(R^2 sin phi_n sin phi_{n-1}). Sum over n: phase advances d phi.
# This is a Riemann sum of 2 q^{3n}/(R^2 sin^2) dn. With q^{3n}~ t^3 -> away from boundary t->...
#
# Simpler decisive test: the FUNCTIONAL asymptotic. Compute t1/tau at poles AND off-poles,
# confirm it -> 1/4 and extract the rate so the claim "t1~tau/4 on V's footing" is concrete.
# Then verify the controlling identity: t1 = sum 2q3n/(y_n y_{n-1}) where y_inf=Se.
#
# Compare to a CLEAN candidate using proven blocks only:
# Since y_inf=Se=1-S1b and the cocycle is the same engine as S1b, maybe 
#   t1 ~ (1/Se^2) * sum 2q3n  in the regime y_n~Se?? test:
print("Candidate A: t1 vs (1/Se)*[geometric]?  and the true ratio")
for i in [2,4,8,16,32]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=50+int(2.0*float(w)); N=int(60/(1-q))
    yh=cocyc_y(q,N)
    qn=mp.mpf(1);S=mp.mpf(0)
    for n in range(1,N+1):
        qn=qn*q;S+=2*qn**3/(yh[n]*yh[n-1])
    Se=1-Sbulk(1,q)
    geo=2*q**3/(1-q**3)  # sum 2 q^{3n}
    print(f" m={i} t1={float(S):.6f} t1/tau={float(S/tau):.6f}  geo/Se^2={float(geo/Se**2):.4f}  geo={float(geo):.4f} Se={float(Se):.4f}")
    mp.mp.dps=50
