import sympy as sp
import sys
sys.path.insert(0,'/tmp')
from gen_an2 import rho_series_fast
from fractions import Fraction as Fr

w, k, t = sp.symbols('w k t', positive=True)   # t = sqrt(tau);  tau=t^2 ; 1/w=t/sqrt2

def G0():
    return 3*sp.sin(w)/w**3 - 3*sp.cos(w)/w**2

def theta(expr):
    return sp.expand(sp.Rational(1,2)*w*sp.diff(expr, w))

def Dj_poly(j):
    nodes = 3*j+4
    ys=[]
    for kk in range(nodes):
        r = rho_series_fast(kk, j)
        ys.append(r[j])
    pts=[(kk, sp.Rational(ys[kk].numerator, ys[kk].denominator)) for kk in range(nodes)]
    poly = sp.interpolate(pts, k)
    poly = sp.expand(poly)
    # verify on extra node
    extra = nodes
    rv = rho_series_fast(extra, j)[j]
    assert poly.subs(k, extra) == sp.Rational(rv.numerator, rv.denominator), f"D_{j} degree too low"
    return sp.Poly(poly, k)

def Dj_theta_G0(j, g0):
    """apply operator D_j(theta) to G0 by replacing k^m with theta^m G0."""
    P = Dj_poly(j)
    # cache theta powers
    coeffs = P.all_coeffs()[::-1]  # coeffs[m] for k^m
    res = 0
    tg = g0
    thetas = [g0]
    for m in range(1, len(coeffs)):
        tg = theta(tg); thetas.append(tg)
    for m,c in enumerate(coeffs):
        if c!=0:
            res += c*thetas[m]
    return sp.expand(res)

def Rj_in_SC(j, g0):
    """R_j(w)=D_j(theta)G0, expressed as Asin(1/w)*sin w + Acos(1/w)*cos w.
    Return (Asin, Acos) as sympy expressions in w (Laurent in w)."""
    R = Dj_theta_G0(j, g0)
    R = sp.expand(R)
    S, C = sp.sin(w), sp.cos(w)
    Asin = R.coeff(S)
    Acos = R.coeff(C)
    # sanity: R == Asin*S+Acos*C
    chk = sp.simplify(R - (Asin*S+Acos*C))
    assert chk==0, f"R_{j} not pure sin/cos combo: {chk}"
    return sp.expand(Asin), sp.expand(Acos)

if __name__=="__main__":
    g0=G0()
    for j in range(3):
        As,Ac=Rj_in_SC(j,g0)
        print(f"R_{j}: Asin={As}")
        print(f"       Acos={Ac}")
