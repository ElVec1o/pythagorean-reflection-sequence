#!/usr/bin/env python3
"""
SYMBOLIC re-derivation of B_{s*} leading term, independent of numerics.

B_s = sum_{x=0}^{s-1} b(x), b(x)=phi((2x+2)tau)+phi((2x+1)tau)-phi(tau).
Leading small-argument: phi(y) ~ y^2/24 (Lemma 1 equality at y->0).
So b(x) ~ (tau^2/24)[(2x+2)^2 + (2x+1)^2 - 1].
B_s ~ (tau^2/24) sum_{x=0}^{s-1}[(2x+2)^2+(2x+1)^2-1].

Compute the closed form (Faulhaber) and its leading cubic in s, then substitute
s = s* = iW/2 with W^2 = 2/tau (on-shell, leading), and read off the coefficient.
Compare to -i(sqrt2/36)sqrt(tau).
"""
import sympy as sp

x, s, tau, W = sp.symbols('x s tau W')

# leading b(x)
b_lead = (tau**2/24)*((2*x+2)**2 + (2*x+1)**2 - 1)
# sum_{x=0}^{s-1}  => use Faulhaber: sympy summation with symbolic upper limit
B_lead = sp.summation(b_lead, (x, 0, s-1))
B_lead = sp.expand(B_lead)
print("B_s (leading, exact Faulhaber):")
print("  ", B_lead)

# leading cubic term in s
B_poly = sp.Poly(B_lead, s)
print("\n  as polynomial in s:", B_poly.as_expr())
cubic_coeff = B_poly.coeff_monomial(s**3)
print("  coeff of s^3:", cubic_coeff, " (claim: tau^2/9)")
print("  matches tau^2/9 ?", sp.simplify(cubic_coeff - tau**2/9) == 0)

# substitute s = i W/2, keep leading (cubic dominates for large W)
I = sp.I
B_at_sstar_cubic = cubic_coeff * (I*W/2)**3
print("\n  cubic term at s*=iW/2:", sp.simplify(B_at_sstar_cubic))

# on-shell leading: W^2 = 2/tau  => W = sqrt(2/tau), W^3 = (2/tau)^{3/2}
B_onshell = B_at_sstar_cubic.subs(W, sp.sqrt(2/tau))
B_onshell = sp.simplify(B_onshell)
print("  on-shell (W=sqrt(2/tau)):", B_onshell)

target = -I*sp.sqrt(2)/36*sp.sqrt(tau)
print("  target -i sqrt(2)/36 sqrt(tau):", sp.simplify(target))
print("  difference:", sp.simplify(B_onshell - target))
print("  MATCH:", sp.simplify(B_onshell - target) == 0)
