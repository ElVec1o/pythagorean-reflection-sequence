"""Endpoint piece of the (T*_poles) certificate: q in [1 - 1e-6, 1].

On this range the crude tail bound g(s) = q^s/(R - (R-1) q^s) >= q^s/R (valid since R >= 1)
gives <s> >= q/(R(1-q)), so e1 + e2 = 2<s> >= 2q/(R(1-q)).  The claim
e1 + e2 >= (5/4)(2q-1)/(1-q) then follows from 2q/R - (5/4)(2q-1) > 0, which is checked here in
mpmath.iv interval arithmetic (outward rounding) on the closed box Q = [1 - 1e-6, 1], with R the
amplitude bound R(q) = exp(c/((1-c)(1-dbar))) (1+c)/(q(1-c)), c = q sqrt((1-q)/2),
dbar = (1-q)c/(1-c).  (Reviewer C's repair 3, room 32.)
"""
from mpmath import iv

iv.dps = 30
one = iv.mpf(1)
Q = iv.mpf(['0.999999', '1'])          # contains [1 - 1e-6, 1)
c = Q * iv.sqrt((one - Q) / 2)
db = (one - Q) * c / (one - c)
R = iv.exp(c / ((one - c) * (one - db))) * (one + c) / (Q * (one - c))
margin = 2 * Q / R - iv.mpf('1.25') * (2 * Q - one)
print('R enclosure      ', R)
print('margin enclosure ', margin)
# R >= 1 holds analytically (each factor of R is >= 1); it is not read off the enclosure.
assert margin.a > 0, 'endpoint check FAILED'
print('endpoint [1-1e-6, 1]: PASS (margin lower end %s)' % margin.a)
