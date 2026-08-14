#!/usr/bin/env python3
"""
halfint_lever.py -- The UNTRIED lever on the U-gate atom: nu=3/2 is HALF-INTEGER.
Classically J_{3/2}(x) = sqrt(2/(pi x)) (sin x / x - cos x): the trig decomposition is
GLOBAL and bypasses Airy/turning-point theory entirely. Test the q-analog:

  (A) Verify the sampled recurrence u_{n+2} - B_n u_{n+1} + u_n = 0  (sanity).
  (B) FIND the nu-contiguous relation:  J_{nu+1} = a(x,q) J_nu + b(x,q) J_{nu-1},
      hypothesis a = a0 * q^{alpha} (1-q^nu)/x-type monomial, b = const monomial.
      Fit numerically at high precision, then verify at many (x,q).
  (C) Probe EXACT amplitude structure at nu=1/2: envelope constant gamma(tau) of
      J^{(3)}_{1/2} vs 3/2 vs 1 (generic): scaling of gamma(tau)/gamma(0)-1 in tau.
"""
import mpmath as mp
mp.mp.dps = 40

def qpoch(a, q, n):
    """(a;q)_n, n can be mp.inf"""
    if n == mp.inf:
        # convergent product
        p = mp.mpf(1); k = 0; a_k = a
        while True:
            t = 1 - a_k
            p *= t
            a_k *= q
            k += 1
            if abs(a_k) < mp.mpf(10)**(-mp.mp.dps-8): break
        return p
    p = mp.mpf(1)
    for k in range(int(n)):
        p *= (1 - a*q**k)
    return p

def J3(nu, x, q, N=200):
    """Hahn-Exton q-Bessel J^{(3)}_nu(x;q) = x^nu ((q^{nu+1};q)_inf/(q;q)_inf)
       * sum (-1)^n q^{n(n+1)/2} x^{2n} / ((q;q)_n (q^{nu+1};q)_n)."""
    pref = x**nu * qpoch(q**(nu+1), q, mp.inf) / qpoch(q, q, mp.inf)
    s = mp.mpf(0); term_den1 = mp.mpf(1); term_den2 = mp.mpf(1)
    for n in range(N):
        num = (-1)**n * q**(mp.mpf(n)*(n+1)/2) * x**(2*n)
        s += num/(term_den1*term_den2)
        term_den1 *= (1 - q**(n+1))
        term_den2 *= (1 - q**(nu+1+n))
        if n>5 and abs(num/(term_den1*term_den2)) < mp.mpf(10)**(-mp.mp.dps-5): break
    return pref*s

print("### (A) recurrence sanity: u_{n+2} - B_n u_{n+1} + u_n = 0 ###")
q = mp.mpf('0.9'); nu = mp.mpf(3)/2; x0 = mp.mpf('0.7')
def B(xn): return (q**(nu/2)+q**(-nu/2)) - q**(1-nu/2)*xn**2
worst = 0
for n in range(6):
    xn = x0*q**(mp.mpf(n)/2)
    u0, u1, u2 = J3(nu, xn, q), J3(nu, xn*mp.sqrt(q), q), J3(nu, xn*q, q)
    r = abs(u2 - B(xn)*u1 + u0)
    worst = max(worst, r)
print(f"  max residual over 6 samples: {mp.nstr(worst,3)}  (should be ~1e-38)")

print()
print("### (B) nu-contiguous relation: J_{nu+1} = a J_nu + b J_{nu-1} ###")
# classical: J_{nu+1} = (2 nu / x) J_nu - J_{nu-1}
# q-hypothesis: a(x,q) = A0 (1-q^nu) q^{beta} / ((1-q) x),  b = -q^{gamma}
# Solve exactly for a,b at pairs of x for several q, nu; then infer structure.
for qv in [mp.mpf('0.85'), mp.mpf('0.95')]:
    for nuv in [mp.mpf(1)/2, mp.mpf(1), mp.mpf(3)/2]:
        x1, x2 = mp.mpf('0.6'), mp.mpf('1.1')
        # unknowns: assume J_{nu+1}(x) = (P/x) J_nu(x) + Q J_{nu-1}(x) with P,Q const in x
        M = mp.matrix([[J3(nuv,x1,qv)/x1, J3(nuv-1,x1,qv)],
                       [J3(nuv,x2,qv)/x2, J3(nuv-1,x2,qv)]])
        rhs = mp.matrix([J3(nuv+1,x1,qv), J3(nuv+1,x2,qv)])
        sol = mp.lu_solve(M, rhs)
        P, Q = sol[0], sol[1]
        # residual at a third x
        x3 = mp.mpf('0.85')
        res = J3(nuv+1,x3,qv) - (P/x3)*J3(nuv,x3,qv) - Q*J3(nuv-1,x3,qv)
        # candidate structure: P =? q^{a}(1-q^{nu})/(1-q) etc. print raw values vs candidates
        cand1 = (1-qv**nuv)/(1-qv)                 # q-number [nu]_q
        cand2 = qv**(nuv/2)*(1-qv**nuv)/(1-qv)
        print(f"  q={float(qv):.2f} nu={float(nuv):.1f}:  P={mp.nstr(P,12)}  Q={mp.nstr(Q,10)}  res(x3)={mp.nstr(abs(res),2)}")
        print(f"      P/[nu]_q={mp.nstr(P/cand1,12)}  P/(q^{{nu/2}}[nu]_q)={mp.nstr(P/cand2,12)}  -Q={mp.nstr(-Q,12)}")

print()
print("### (C) envelope constant drift gamma(tau) for nu = 1/2, 1, 3/2 ###")
# gamma_n := A_n (4-B_n^2)^{1/4}, A_n = sqrt(G_n)/sin(psi_n), G_n = u_n^2 - B_n u_n u_{n+1} + u_{n+1}^2
# measure gamma at fixed physical x in the bulk, as tau -> 0; fit gamma(tau)/gamma_extrap - 1 ~ C tau^alpha
def gamma_of(nu, x, tau):
    qv = mp.e**(-tau)
    Bx = (qv**(nu/2)+qv**(-nu/2)) - qv**(1-nu/2)*x**2
    u0, u1 = J3(nu, x, qv), J3(nu, x*mp.sqrt(qv), qv)
    G = u0**2 - Bx*u0*u1 + u1**2
    sinpsi = mp.sqrt(4-Bx**2)/2
    A = mp.sqrt(abs(G))/sinpsi
    return A*(4-Bx**2)**mp.mpf('0.25')

xfix = mp.mpf('1.0')
for nuv,name in [(mp.mpf(1)/2,'1/2'), (mp.mpf(1),'1  '), (mp.mpf(3)/2,'3/2')]:
    gs = []
    taus = [mp.mpf('0.20'), mp.mpf('0.10'), mp.mpf('0.05'), mp.mpf('0.025'), mp.mpf('0.0125')]
    for tau in taus:
        gs.append(gamma_of(nuv, xfix, tau))
    # Richardson-extrapolate assuming gamma = g0 + c tau (first order)
    g0 = 2*gs[-1] - gs[-2]
    devs = [abs(g/g0-1) for g in gs]
    # fit slope alpha in dev ~ C tau^alpha from last pairs
    import math
    al1 = mp.log(devs[-2]/devs[-3])/mp.log(taus[-2]/taus[-3])
    al2 = mp.log(devs[-1]/devs[-2])/mp.log(taus[-1]/taus[-2])
    print(f"  nu={name}: gamma(tau)={[mp.nstr(g,8) for g in gs]}")
    print(f"           |gamma/g0-1| slopes: {mp.nstr(al1,4)}, {mp.nstr(al2,4)}  (1.0 => gamma=g0(1+O(tau)) CONFIRMED)")
