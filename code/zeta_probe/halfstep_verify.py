#!/usr/bin/env python3
"""Verifier for section 5 of private/U_cumulant_chain.tex (Rule 9).

  lem:funct    F(x) - F(qx) = q^{1/4} x F(sqrt(q) x)                      [generic]
  eq:half      c(qu)=c(u)+q^{3/2}u s(sqrt q u);  s(qu)=s(u)-u c(sqrt q u) [generic]
  thm:inv      c(u)c(sqrt q u) + q^{3/2} s(u) s(sqrt q u) = 1             [generic]
  eq:crec      c(qv) = (1+q-q v^2) c(v) - q c(v/q)                        [generic]
  thm:collapse q^{3/2}s(z0)s(Z)=1, s(z0)=s(z0/q), c(qZ)=Z/s(Z),
               P12 = -[c(z0)+c(z0/q)]/2                                   [at poles]
Precision is adapted to the e^{u/tau} cancellation of the alternating series.
"""
import sys
from mpmath import mp, mpf, mpc, sqrt, exp, nstr

DATA = "tools/t1series/t1_data.txt"

def qpochs(q, N):
    p = [mpf(1)]*(N+1)
    for n in range(1, N+1): p[n] = p[n-1]*(1-q**n)
    return p
def Fq(x, q, qp): return sum(q**(mpf(M*M)/4)*x**M/qp[M] for M in range(len(qp)))
def Cc(u, q, qp): return sum((-1)**j*q**(j*j+j)*u**(2*j)/qp[2*j] for j in range((len(qp)-1)//2))
def Ss(u, q, qp): return sum((-1)**k*q**(k*k+2*k)*u**(2*k+1)/qp[2*k+1] for k in range((len(qp)-2)//2))
def P12k(q, qp):
    y = 2*(1-q)
    return sum((-1)**(k-1)*y**k*q**(k*k+k+1)*(1-q**(2*k))/qp[2*k+1] for k in range(1, (len(qp)-2)//2))

def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DATA
    rows = [(int(f[0]), f[1]) for f in (l.split() for l in open(path)) if len(f) >= 5]
    ok = True; TOL = mpf(10)**(-25)

    mp.dps = 40
    for (qv, xv) in ((mpf('0.5'), mpf('0.3')), (mpf('0.8'), mpc(0, '0.41')), (mpf('0.97'), mpc('0.2','-0.35'))):
        qp = qpochs(qv, 400)
        d = abs(Fq(xv,qv,qp)-Fq(qv*xv,qv,qp)-qv**mpf('0.25')*xv*Fq(sqrt(qv)*xv,qv,qp))
        ok &= d < TOL
        print(f"  lem:funct     q={float(qv):5.2f}  dev = {nstr(d,3)}")

    for (ts, uu) in (('0.02','2.0'), ('0.005','1.0'), ('0.09048','0.41'), ('0.001','0.3')):
        tau = mpf(ts); u = mpf(uu)
        mp.dps = 40 + int(0.5*float(u/tau))
        q = exp(-tau); qp = qpochs(q, 2*int(3*float(u/tau))+300)
        cu, cqu, csu = Cc(u,q,qp), Cc(q*u,q,qp), Cc(sqrt(q)*u,q,qp)
        su, squ, ssu = Ss(u,q,qp), Ss(q*u,q,qp), Ss(sqrt(q)*u,q,qp)
        d1 = abs(cqu - cu - q**mpf('1.5')*u*ssu)
        d2 = abs(squ - su + u*csu)
        d3 = abs(cu*csu + q**mpf('1.5')*su*ssu - 1)
        d4 = abs(cqu - (1+q-q*u*u)*cu + q*Cc(u/q,q,qp))
        ok &= max(d1,d2,d3,d4) < TOL
        print(f"  eq:half/inv/crec  tau={float(tau):8.5f} u={float(u):4.2f} dps={mp.dps:4d}  "
              f"devs = {nstr(d1,2)}, {nstr(d2,2)}, {nstr(d3,2)}, {nstr(d4,2)}")

    print("  thm:collapse (at the 58 tabulated poles):")
    worst = [mpf(0)]*4
    for (m, ts) in rows:
        mp.dps = 45 + int(0.55*float((2/mpf(ts))**0.5))
        tau = mpf(ts); q = exp(-tau); z0 = sqrt(2*(1-q)); Z = z0/sqrt(q)
        qp = qpochs(q, 2*(int(2*sqrt(2/tau))+90)+3)
        sz0, sZ, cz0, czq = Ss(z0,q,qp), Ss(Z,q,qp), Cc(z0,q,qp), Cc(z0/q,q,qp)
        P = P12k(q, qp)
        worst[0] = max(worst[0], abs(q**mpf('1.5')*sz0*sZ - 1))
        worst[1] = max(worst[1], abs(sz0 - Ss(z0/q,q,qp))/abs(sz0))
        worst[2] = max(worst[2], abs(Cc(q*Z,q,qp) - Z/sZ)/abs(Z/sZ))
        worst[3] = max(worst[3], abs(-(cz0+czq)/2 - P)/abs(P))
    for lbl, v in zip(("q^{3/2}s(z0)s(Z)=1", "s(z0)=s(z0/q)", "c(qZ)=Z/s(Z)",
                       "P12=-[c(z0)+c(z0/q)]/2"), worst):
        ok &= v < TOL
        print(f"     {lbl:26s} worst dev = {nstr(v,3)}")
    print("PASS" if ok else "FAIL"); return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
