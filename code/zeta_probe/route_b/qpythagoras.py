#!/usr/bin/env python3
"""
qpythagoras.py -- Hunt the EXACT q-Pythagoras identity for the K-S pair.
Classical target: J_{1/2}(X)^2 + J_{-1/2}(X)^2 = 2/(pi X)  (exact, global,
= the amplitude statement sin^2+cos^2=1; no turning point needed).

Lattice care: J_{1/2}(x) solves the nu=1/2 recurrence; its true partner on the SAME
recurrence is Jt(x) := J_{-1/2}(x q^{-1/4})  (involution B(-nu, x q^{-nu/2}) = B(nu,x)).

Battery:
  (0) Casoratian C(x) = J(xq^{1/2})Jt(x) - J(x)Jt(xq^{1/2})  -- constant? match c+c-(q^{1/4}-q^{-1/4})?
  (1) T1(x) = x [ J(x)^2 + Jt(x)^2 ]          -- constant in x?
  (2) periodicity: T1(x q^{1/2}) / T1(x) - 1  -- exactly 0? (theta-quotient structure)
  (3) if periodic: Fourier content of log-periodic T1 (how many modes?)
"""
import mpmath as mp
mp.mp.dps = 50

def qpoch_inf(a, q):
    p = mp.mpf(1); a_k = mp.mpf(a)
    while abs(a_k) > mp.mpf(10)**(-mp.mp.dps-10):
        p *= (1 - a_k); a_k *= q
    return p

def J3(nu, x, q, N=400):
    pref = mp.mpf(x)**nu * qpoch_inf(q**(nu+1), q)/qpoch_inf(q, q)
    s = mp.mpf(1); d1 = mp.mpf(1); d2 = mp.mpf(1)
    for n in range(1, N):
        d1 *= (1 - q**n); d2 *= (1 - q**(nu+n))
        t = (-1)**n * q**(mp.mpf(n)*(n+1)/2) * mp.mpf(x)**(2*n)/(d1*d2)
        s += t
        if n > 5 and abs(t) < mp.mpf(10)**(-mp.mp.dps-8): break
    return pref*s

q = mp.mpf('0.90')
Jp = lambda x: J3(mp.mpf(1)/2, x, q)
Jt = lambda x: J3(-mp.mpf(1)/2, x*q**mp.mpf('-0.25'), q)

print("### (0) Casoratian of the correct pair: constant? ###")
def Cas(x): return Jp(x*mp.sqrt(q))*Jt(x) - Jp(x)*Jt(x*mp.sqrt(q))
xs = [mp.mpf('0.05'), mp.mpf('0.3'), mp.mpf('0.8'), mp.mpf('1.3'), mp.mpf('1.7')]
Cvals = [Cas(x) for x in xs]
for x, c in zip(xs, Cvals): print(f"  C({float(x):.2f}) = {mp.nstr(c, 25)}")
# exact candidate: c+ c- q^{1/8} (q^{-1/4} - q^{1/4}), c+=(q^{3/2};q)inf/(q;q)inf, c-=(q^{1/2};q)inf/(q;q)inf
cp = qpoch_inf(q**mp.mpf('1.5'), q)/qpoch_inf(q, q)
cm = qpoch_inf(q**mp.mpf('0.5'), q)/qpoch_inf(q, q)
cand = cp*cm*q**mp.mpf('0.125')*(q**mp.mpf('-0.25') - q**mp.mpf('0.25'))
print(f"  candidate c+c- q^(1/8)(q^(-1/4)-q^(1/4)) = {mp.nstr(cand, 25)}")
print(f"  ratio C/candidate = {mp.nstr(Cvals[2]/cand, 25)}")

print()
print("### (1) T1(x) = x [ J(x)^2 + Jt(x)^2 ]: constant? ###")
T1 = lambda x: x*(Jp(x)**2 + Jt(x)**2)
tvals = [T1(x) for x in xs]
for x, t in zip(xs, tvals): print(f"  T1({float(x):.2f}) = {mp.nstr(t, 25)}")
print(f"  max/min - 1 = {mp.nstr(max(tvals)/min(tvals) - 1, 5)}")

print()
print("### (2) q^{1/2}-periodicity: T1(x q^{1/2})/T1(x) - 1 ###")
for x in [mp.mpf('0.4'), mp.mpf('0.9'), mp.mpf('1.5')]:
    r = T1(x*mp.sqrt(q))/T1(x) - 1
    print(f"  x={float(x):.2f}: {mp.nstr(r, 8)}")

print()
print("### (3) also test FULL-q periodicity T1(xq)/T1(x)-1, and the UNSHIFTED naive pair ###")
for x in [mp.mpf('0.4'), mp.mpf('0.9')]:
    r = T1(x*q)/T1(x) - 1
    print(f"  full-q: x={float(x):.2f}: {mp.nstr(r, 8)}")
T1n = lambda x: x*(J3(mp.mpf(1)/2,x,q)**2 + J3(-mp.mpf(1)/2,x,q)**2)
tn = [T1n(x) for x in xs]
print(f"  naive-pair max/min-1 = {mp.nstr(max(tn)/min(tn)-1, 5)}")
