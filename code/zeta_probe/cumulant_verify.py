#!/usr/bin/env python3
"""Verifier for private/U_cumulant_chain.tex  (Rule 9).

Checks, at the tabulated travel poles:
  1. lem:rep     Phi(rho) = sum_M q^{M^2/4} (i rho)^M / (q;q)_M   [vs direct Gaussian quadrature]
  2. eq:parity   Re Phi(rho) = C(rho^2/q),  Im Phi(rho) = q^{1/4} rho T(rho^2/q)
  3. prop:poles  Re Phi(z0) = 0 at every travel pole
  4. prop:P12    P12 = q[T(yq) - T(y/q)] = (q^{3/4}/z0)[Im Phi(q z0)/q - Im Phi(z0)]
  5. lem:hyp     2 |Lam_2| s^2 <= 0.68 < 1 for tau <= 0.05
  6. thm:reduction  the degree-d jet model reproduces P12 with relative error -> 0
Prints PASS/FAIL.  Precision is adapted to the alternating-series cancellation (~e^w).
"""
import sys
from mpmath import mp, mpf, mpc, sqrt, exp, pi, log, quad, factorial

DATA = "tools/t1series/t1_data.txt"

def load(path):
    out = []
    for l in open(path):
        f = l.split()
        if len(f) >= 5:
            try: out.append((int(f[0]), f[1]))
            except ValueError: pass
    return out

def qpochs(q, N):
    p = [mpf(1)]*(N+1)
    for n in range(1, N+1): p[n] = p[n-1]*(1-q**n)
    return p

def Cser(v, q, qp):
    return sum((-1)**j * q**(j*j+j) * v**j / qp[2*j] for j in range((len(qp)-1)//2))

def Tser(v, q, qp):
    return sum((-1)**k * q**(k*k+2*k) * v**k / qp[2*k+1] for k in range((len(qp)-2)//2))

def PhiM(rho, q, qp):
    """lem:rep, right-hand side."""
    return sum(q**(mpf(M*M)/4) * (mpc(0, rho))**M / qp[M] for M in range(len(qp)))

def P12ksum(q, qp):
    y = 2*(1-q)
    return sum((-1)**(k-1) * y**k * q**(k*k+k+1) * (1-q**(2*k)) / qp[2*k+1]
               for k in range(1, (len(qp)-2)//2))

def lambdas(rho, q, nmax, K):
    x = mpc(0, rho); L = [mpc(0)]*(nmax+1); xk = mpc(1)
    ipow = [mpc(0, 1)**n for n in range(nmax+1)]
    for k in range(1, K+1):
        xk = xk*x; base = xk/(1-q**k)
        L[0] += base/k
        for n in range(1, nmax+1): L[n] += ipow[n]*(mpf(k)**(n-1))*base
    return L

def phi_model(L, s2, d):
    a, b = L[1], L[2]
    beta = 1 - b*s2
    G = beta**mpf('-0.5') * exp(a*a*s2/(2*beta))
    mu = a*s2/beta; sg = s2/beta
    P = [mpc(0)]*(d+1)
    for n in range(3, d+1): P[n] = L[n]/factorial(n)
    E = [mpc(0)]*(d+1); E[0] = mpc(1); term = [mpc(0)]*(d+1); term[0] = mpc(1)
    for r in range(1, d//3 + 1):
        new = [mpc(0)]*(d+1)
        for i, ci in enumerate(term):
            if ci == 0: continue
            for j, cj in enumerate(P):
                if cj == 0 or i+j > d: continue
                new[i+j] += ci*cj
        term = [c/r for c in new]
        for i in range(d+1): E[i] += term[i]
    M = [mpc(1), mu]
    for m in range(2, d+1): M.append(mu*M[m-1] + (m-1)*sg*M[m-2])
    return exp(L[0])*G*sum(E[m]*M[m] for m in range(d+1))

def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DATA
    rows = load(path); ok = True

    # ---- 1: lem:rep against direct Gaussian quadrature (shallow poles only) ----
    mp.dps = 50
    for (m, ts) in rows[:2]:
        tau = mpf(ts); q = exp(-tau); z0 = sqrt(2*(1-q)); s = sqrt(tau/2)
        qp = qpochs(q, int(3*sqrt(2/tau)) + 60)
        for rho in (z0, q*z0):
            K = int((mp.dps+10)*log(10)/log(1/rho)) + 5
            def f(t, rho=rho, K=K):
                x = rho*exp(mpc(0,1)*(pi/2 + s*t)); acc = mpc(0); xk = mpc(1)
                for k in range(1, K+1):
                    xk = xk*x; acc += xk/(k*(1-q**k))
                return exp(acc - t*t/2)
            E = quad(f, [-40,-12,-5,-2,0,2,5,12,40])/sqrt(2*pi)
            e = abs(E - PhiM(rho, q, qp))/abs(E)
            if e > mpf(10)**(-40): ok = False
            print(f"  1. lem:rep      m={m:2d} rho={'z0' if rho==z0 else 'q z0':4s} rel.dev = {mp.nstr(e,3)}")

    # ---- 2-5: identities at every tabulated pole ----
    worst = {k: mpf(0) for k in ("parity", "pole", "P12a", "P12b")}; hypmax = mpf(0)
    for (m, ts) in rows:
        mp.dps = 40 + int(0.6*float((2/mpf(ts))**0.5))
        tau = mpf(ts); q = exp(-tau); z0 = sqrt(2*(1-q)); y = z0*z0; s2 = tau/2
        qp = qpochs(q, 2*(int(2*sqrt(2/tau)) + 70) + 3)
        for rho in (z0, q*z0):
            Ph = PhiM(rho, q, qp); v = rho*rho/q
            d1 = abs(Ph.real - Cser(v, q, qp))/abs(Ph)
            d2 = abs(Ph.imag - q**mpf('0.25')*rho*Tser(v, q, qp))/abs(Ph)
            worst["parity"] = max(worst["parity"], d1, d2)
        Ph0 = PhiM(z0, q, qp)
        worst["pole"] = max(worst["pole"], abs(Ph0.real)/abs(Ph0))
        P = P12ksum(q, qp)
        worst["P12a"] = max(worst["P12a"], abs(P - q*(Tser(y*q,q,qp)-Tser(y/q,q,qp)))/abs(P))
        alt = (q**mpf('0.75')/z0)*(PhiM(q*z0,q,qp).imag/q - PhiM(z0,q,qp).imag)
        worst["P12b"] = max(worst["P12b"], abs(P-alt)/abs(P))
        if tau <= mpf('0.05'):
            K = int((mp.dps+10)*log(10)/log(1/z0)) + 5
            hypmax = max(hypmax, 2*abs(lambdas(z0, q, 2, K)[2])*s2)
    for k, lbl in (("parity","eq:parity"), ("pole","prop:poles"), ("P12a","prop:P12 (form 1)"),
                   ("P12b","prop:P12 (form 2)")):
        bad = worst[k] > mpf(10)**(-25)
        ok &= not bad
        print(f"  {'2344'[('parity','pole','P12a','P12b').index(k)]}. {lbl:22s} worst rel.dev over {len(rows)} poles = {mp.nstr(worst[k],3)}")
    ok &= (hypmax <= mpf('0.68'))
    print(f"  5. lem:hyp             max 2|Lam_2|s^2 (tau<=0.05) = {mp.nstr(hypmax,4)}  (bound 0.68)")

    # ---- 6: thm:reduction, relative error of the degree-d model ----
    print("  6. thm:reduction   relative error of the degree-d jet model vs P12:")
    for (m, ts) in rows:
        if m not in (2, 8, 20, 40, 48): continue
        mp.dps = 40 + int(0.6*float((2/mpf(ts))**0.5))
        tau = mpf(ts); q = exp(-tau); z0 = sqrt(2*(1-q)); s2 = tau/2
        qp = qpochs(q, 2*(int(2*sqrt(2/tau)) + 70) + 3); P = P12ksum(q, qp)
        line = []
        for d in (4, 5, 6):
            v = {}
            for rho in (q*z0, z0):
                K = int((mp.dps+10)*log(10)/log(1/rho)) + 5
                v[rho] = phi_model(lambdas(rho, q, d, K), s2, d).imag
            Pm = (q**mpf('0.75')/z0)*(v[q*z0]/q - v[z0])
            line.append(abs((Pm-P)/P))
        if line[1] > 10*tau: ok = False
        print(f"       m={m:2d} tau={float(tau):9.3e}  d=4: {mp.nstr(line[0],3):>9s}"
              f"   d=5: {mp.nstr(line[1],3):>9s}   d=6: {mp.nstr(line[2],3):>9s}"
              f"   [d=5]/tau = {mp.nstr(line[1]/tau,3)}")
    print("PASS" if ok else "FAIL"); return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
