"""
D3 analytic derivation: tau G(1/q)/L(1/q) -> -125/142, via Watson resummation of the saddle integral.

  L     = (1/(2 sqrt pi)) Int e^{-v^2/4} Phi(sqrt tau v) dv
  tau G = (1/(2 sqrt pi)) Int e^{-v^2/4} [ -v^2/4 + 1/2 + i v sqrt tau /2 ] Phi(sqrt tau v) dv
  Phi(u) = sin z / z^3 - cos z / z^2,   z = Z0 e^{i s v / 2},  s = sqrt tau.

Expand Phi in s, take Gaussian v-moments  <v^{2n}> = (2n-1)!! 2^n, substitute the EXACT
Z0 = e^{tau} sqrt(2/tau) and the travel-pole condition cos(Z0) = -(35 sqrt2/36) sqrt(tau) sin(Z0),
divide by sin(Z0), let tau->0. The truncation-order limit converges to -125/142.
"""
import sympy as sp

s, v, Z0 = sp.symbols('s v Z0', real=True); I = sp.I
tau, S, kap = sp.symbols('tau S kappa', positive=True)
z = Z0*sp.exp(I*s*v/2)
Phi = sp.sin(z)/z**3 - sp.cos(z)/z**2
Gw = (-v**2/sp.Integer(4) + sp.Rational(1, 2) + I*v*s/2)
kapval = -35*sp.sqrt(2)/36

def gauss_avg(expr):
    expr = sp.expand(expr); poly = sp.Poly(expr, v); res = 0
    for monom, coeff in poly.terms():
        deg = monom[0]
        if deg % 2 == 0:
            n = deg//2; mom = sp.factorial2(2*n-1)*2**n if n > 0 else 1; res += coeff*mom
    return sp.expand(res)

def reduce(expr):
    e = expr.subs(s, sp.sqrt(tau))
    e = e.subs(sp.sin(Z0), S).subs(sp.cos(Z0), kap*sp.sqrt(tau)*S)
    e = e.subs(Z0, sp.exp(tau)*sp.sqrt(2/tau))
    return sp.expand(e/S)

print("ORD   lim tauG/L          diff from -125/142")
for ORD in [8, 14, 20, 26]:
    Phi_s = sp.series(Phi, s, 0, ORD+1).removeO()
    Lr = reduce(gauss_avg(Phi_s)); Gr = reduce(gauss_avg(Gw*Phi_s))
    ratio = sp.limit(Gr/Lr, tau, 0)
    val = float(ratio.subs(kap, kapval))
    print("%3d   %.12f   %.2e" % (ORD, val, val - (-125/142)))
print("-125/142 = %.12f" % (-125/142))
