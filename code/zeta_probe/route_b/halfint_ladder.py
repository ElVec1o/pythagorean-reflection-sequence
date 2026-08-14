#!/usr/bin/env python3
"""
halfint_ladder.py -- Verify the EXACT q-spherical-Bessel ladder derived from the
1phi1 contiguous relation, and probe the nu=3/2 RESONANCE in the Morita layer.

Derivation (b = q^{nu+1}, z = qx^2, f_nu(x) := 1phi1(0; q^{nu+1}; q, qx^2)):
  1/(b;q)_n - 1/(bq;q)_n = b(1-q^n)/[(1-b)(bq;q)_n] * 1/(bq;q)_{n-1}-shift
  => 1phi1(0;b;q,z) = 1phi1(0;bq;q,z) - [bz/((1-b)(1-bq))] * 1phi1(0;bq^2;q,qz)
  With nu' = -1/2 (b = q^{1/2}, z = qx^2):
  f_{-1/2}(x) = f_{1/2}(x) - [q^{3/2}x^2/((1-q^{1/2})(1-q^{3/2}))] * f_{3/2}(x q^{1/2})
  =>  f_{3/2}(x q^{1/2}) = (1-q^{1/2})(1-q^{3/2}) [f_{1/2}(x) - f_{-1/2}(x)] / (q^{3/2} x^2)
  -- the exact q-analog of  j_1(X) = (sin X / X - cos X)/X.
In terms of J^{(3)}: J_nu = x^nu ((q^{nu+1};q)_inf/(q;q)_inf) f_nu.
"""
import mpmath as mp
mp.mp.dps = 40

def qpoch_inf(a, q):
    p = mp.mpf(1); a_k = mp.mpf(a)
    while abs(a_k) > mp.mpf(10)**(-mp.mp.dps-8):
        p *= (1 - a_k); a_k *= q
    return p

def phi11(b, q, z, N=300):
    """1phi1(0; b; q, z) = sum (-1)^n q^{n(n-1)/2} z^n / ((q;q)_n (b;q)_n)"""
    s = mp.mpf(1); d1 = mp.mpf(1); d2 = mp.mpf(1)
    for n in range(1, N):
        d1 *= (1 - q**n)
        d2 *= (1 - b*q**(n-1))
        t = (-1)**n * q**(mp.mpf(n)*(n-1)/2) * z**n / (d1*d2)
        s += t
        if n > 5 and abs(t) < mp.mpf(10)**(-mp.mp.dps-5): break
    return s

def f_nu(nu, x, q): return phi11(q**(nu+1), q, q*x**2)

print("### (1) EXACT LADDER: f_{3/2}(x q^{1/2}) = (1-q^{1/2})(1-q^{3/2})[f_{1/2}(x)-f_{-1/2}(x)]/(q^{3/2}x^2) ###")
worst = 0
for qv in [mp.mpf('0.5'), mp.mpf('0.85'), mp.mpf('0.97')]:
    for xv in [mp.mpf('0.3'), mp.mpf('0.8'), mp.mpf('1.4')]:
        lhs = f_nu(mp.mpf(3)/2, xv*mp.sqrt(qv), qv)
        rhs = (1-mp.sqrt(qv))*(1-qv**mp.mpf('1.5'))*(f_nu(mp.mpf(1)/2,xv,qv)-f_nu(-mp.mpf(1)/2,xv,qv))/(qv**mp.mpf('1.5')*xv**2)
        rel = abs(lhs-rhs)/abs(lhs)
        worst = max(worst, rel)
        print(f"  q={float(qv):.2f} x={float(xv):.1f}: rel err = {mp.nstr(rel, 3)}")
print(f"  WORST: {mp.nstr(worst,3)}  (0 => identity EXACT)")

print()
print("### (2) same identity in J-normalization (with prefactors) ###")
# J_nu(x;q) = x^nu (q^{nu+1};q)_inf/(q;q)_inf * f_nu(x)
def J3(nu, x, q):
    return x**nu * qpoch_inf(q**(nu+1), q)/qpoch_inf(q, q) * f_nu(nu, x, q)
qv = mp.mpf('0.9'); xv = mp.mpf('1.1')
lhsJ = J3(mp.mpf(3)/2, xv*mp.sqrt(qv), qv)
# translate: f_{3/2}(xq^{1/2}) = J_{3/2}(xq^{1/2}) / [ (xq^{1/2})^{3/2} (q^{5/2};q)inf/(q;q)inf ]
pref32 = (xv*mp.sqrt(qv))**mp.mpf('1.5') * qpoch_inf(qv**mp.mpf('2.5'), qv)/qpoch_inf(qv, qv)
pref12 = xv**mp.mpf('0.5') * qpoch_inf(qv**mp.mpf('1.5'), qv)/qpoch_inf(qv, qv)
prefm12 = xv**mp.mpf('-0.5') * qpoch_inf(qv**mp.mpf('0.5'), qv)/qpoch_inf(qv, qv)
rhsJ = pref32*(1-mp.sqrt(qv))*(1-qv**mp.mpf('1.5'))/(qv**mp.mpf('1.5')*xv**2) * \
       ( J3(mp.mpf(1)/2,xv,qv)/pref12 - J3(-mp.mpf(1)/2,xv,qv)/prefm12 )
print(f"  J-form check: rel err = {mp.nstr(abs(lhsJ-rhsJ)/abs(lhsJ), 3)}")

print()
print("### (3) RESONANCE probe: kappa's prefactor 1/(p^{-2nu},p;p)_inf at nu=3/2 ###")
p = mp.mpf('0.9')
# (p^{-3};p)_inf: factors (1-p^{-3}p^k), k=0,1,2,3,... ; k=3 gives (1-1)=0
prod = mp.mpf(1); zero_at = None
for k in range(0, 8):
    fac = 1 - p**(-3)*p**k
    if abs(fac) < mp.mpf(10)**(-30): zero_at = k
    prod *= fac
print(f"  (p^-3;p)_inf partial product through k=7: {mp.nstr(prod,3)}; EXACT ZERO factor at k={zero_at}")
print(f"  => kappa as displayed (eq:kappa) is SINGULAR (1/0) at nu=3/2: resonant case 2nu in Z.")
print()
print("### (4) Phi_- parameter (p^{1-2nu};p)_n at nu=3/2: p^{-2} ###")
b = p**(-2)
for n in range(1,6):
    v = qpoch_inf(b, p)/1  # just show finite pochhammers
d = mp.mpf(1); zs=[]
for n in range(1, 6):
    d *= (1 - b*p**(n-1))
    zs.append(mp.nstr(d, 3))
print(f"  (p^-2;p)_n for n=1..5: {zs}   (0 from n=3 => Phi_- series has 0/0 terms; ill-defined as displayed)")
