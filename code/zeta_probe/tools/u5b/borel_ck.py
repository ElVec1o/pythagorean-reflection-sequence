import sympy as sp
import sys

# Derive the dev_m asymptotic coefficients c_k to high order.
# dev_m ~ sum_{k>=1} c_k / w^{2k-1},  w=sqrt(2/tau).
# Method (same as derive_c3.py, generalized):
#   Sigma(tau) generating fn -> 1 has solutions w_m; expand Sigma's small-tau
#   structure in tau, organize per-k powers via polynomials in the summation
#   index kk, apply the theta-operator (theta=1/2 w d/dw, thm1=theta-1) to the
#   base 1-cos w, form the correction 'corr', then solve Sigma=1 perturbatively.

NPAIR = int(sys.argv[1]) if len(sys.argv) > 1 else 6   # number of c_k wanted
# we need dev series to order s^{2*NPAIR-1}.  PS goes p=2..2*NPAIR.
PMAX = 2 * NPAIR
PS = list(range(2, PMAX + 1, 2))
ORD = PMAX + 4          # tau-truncation order (a few guard terms)
maxk = 3 * (PMAX // 2) + 3   # need polynomials in kk of degree up to 3*(p/2)

tau, w, s = sp.symbols('tau w s', positive=True)

def qf(a):
    return sp.series(sp.exp(-a * tau), tau, 0, ORD + 1).removeO()

def inv1mq(m):
    return sp.series(1 / (1 - sp.exp(-m * tau)), tau, 0, ORD + 1).removeO()

def fac(j):
    return sp.expand(2 * qf(2 * j + 4) * inv1mq(2 * j + 3) - 2 * qf(2 * j + 3) * inv1mq(2 * j + 2))

def rho(k):
    pr = sp.Integer(1)
    for j in range(k):
        pr = sp.expand(sp.series(pr * fac(j), tau, 0, ORD).removeO())
    term = sp.expand(sp.series(2 * qf(1) * inv1mq(2 * k + 2) * pr, tau, 0, ORD).removeO())
    return sp.expand(sp.series(term * sp.Integer(-1) ** k * sp.factorial(2 * k + 2) * (tau / 2) ** (k + 1),
                              tau, 0, ORD).removeO())

print("building rho(k) for k=0..%d ..." % maxk, flush=True)
allrho = [sp.Poly(rho(k), tau) for k in range(maxk + 1)]
print("rho done", flush=True)

kk = sp.symbols('kk')
polys = {}
for p in PS:
    m = p // 2
    deg = 3 * m
    n = deg + 1
    if n > maxk + 1:
        n = maxk + 1
    ys = [allrho[k].coeff_monomial(tau ** p) for k in range(n)]
    M = sp.Matrix([[sp.Integer(kx) ** d for d in range(n)] for kx in range(n)])
    coef = M.solve(sp.Matrix(ys))
    polys[p] = sp.expand(sum(coef[d] * kk ** d for d in range(n)))
    # sanity: predict the next k
    if n <= maxk:
        chk = sp.simplify(polys[p].subs(kk, n) - allrho[n].coeff_monomial(tau ** p))
        ok = (chk == 0)
    else:
        ok = "n/a"
    print('c_%d poly deg %d  check=%s' % (p, sp.Poly(polys[p], kk).degree(), ok), flush=True)

def theta(f):
    return sp.Rational(1, 2) * w * sp.diff(f, w)

def thm1(f):
    return sp.expand(theta(f) - f)

base = 1 - sp.cos(w)

def apply_cp(poly):
    pol = sp.Poly(poly, kk)
    cur = base
    pw = [cur]
    for d in range(1, pol.degree() + 1):
        cur = thm1(cur)
        pw.append(cur)
    return sp.expand(sum(pol.coeff_monomial(kk ** d) * pw[d] for d in range(pol.degree() + 1)))

print("assembling correction ...", flush=True)
corr = sum(tau ** p * apply_cp(polys[p]) for p in PS)
om = sp.expand(sp.cos(w) - corr)
Ccos = om.coeff(sp.cos(w))
Csin = om.coeff(sp.sin(w))

NS = 2 * NPAIR + 1
Cc = sp.series(sp.expand(Ccos.subs([(w, sp.sqrt(2) / s), (tau, s ** 2)])), s, 0, NS).removeO()
Cs = sp.series(sp.expand(Csin.subs([(w, sp.sqrt(2) / s), (tau, s ** 2)])), s, 0, NS).removeO()
X = sp.series(-Cs / Cc, s, 0, NS).removeO()
dev = sp.series(sp.atan(X), s, 0, NS).removeO()
P = sp.Poly(sp.expand(dev), s)

# dev = sum c_k / w^{2k-1} = sum c_k (s/sqrt2)^{2k-1} = sum c_k s^{2k-1} 2^{-(2k-1)/2}
# so coeff of s^{2k-1} is c_k * 2^{-(2k-1)/2}  => c_k = coeff * 2^{(2k-1)/2}.
print("\n--- c_k ---", flush=True)
cks = []
known = {1: sp.Rational(1, 18), 2: sp.Rational(-41, 600), 3: sp.Rational(-1915, 7056),
         4: sp.Rational(-18617, 51840), 5: sp.Rational(-942829, 29272320)}
for k in range(1, NPAIR + 1):
    e = 2 * k - 1
    val = sp.nsimplify(P.coeff_monomial(s ** e) * sp.Integer(2) ** sp.Rational(e, 2))
    val = sp.simplify(val)
    cks.append(val)
    chk = ''
    if k in known:
        chk = '  match=%s' % (sp.simplify(val - known[k]) == 0)
    print('c_%d = %s%s' % (k, val, chk), flush=True)

# dump rationals for downstream numeric analysis
import json
out = [str(c) for c in cks]
with open('/Users/vico/Documents/elvec1o/u5b/cks.json', 'w') as f:
    json.dump(out, f)
print("\nwrote cks.json with %d coeffs" % len(cks), flush=True)
