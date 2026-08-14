"""
ADVERSARIAL re-derivation of the D1-D3 algebra from scratch.

The travel form factor.  The travel sum is  Sig_t = sum_{j>=0} t^T_j, with
  t^T_0 = Aq(1),  t^T_j = Aq(1+2j) * prod_{i=0}^{j-1} Cq(1+2i).
The "model" giving 1 - cos w is  hat_t_j = (2/tau)^{j+1}/(2j+2)!  with sum_j (-1)^j hat_t_j??
Let's NOT assume the model; let's DISCOVER it numerically and define rho^T_j = t^T_j / hat_t_j
with the SIGN convention used in D4 (t includes its own sign; the alternation is built into
1-cos w = sum_{n>=1} (-1)^{n-1} w^{2n}/(2n)!).

We test the claims:
  (D1) log( |t^T_j/t^T_{j-1}| / (hat_t_j/hat_t_{j-1}) ) = log(rho_j/rho_{j-1})
       = 2y + 2 log( 2y/(e^{2y}-1) ),   y = j*tau.    [exact one-step]
       Its small-y expansion = -y^2/3 + y^4/90 - ...   ; O(tau^1) part of log rho_j step has NO constant.
  (D2) log rho^T_j = -(1/9) tau^2 j^3 + (1/450) tau^4 j^5 - ...   (integrate the step; NO linear -(j+1)tau).
  (D3) vartheta^3(1-cos w) = (w/8)(-w^2 sin w + 3 w cos w + sin w),  vartheta = (1/2) w d/dw.
       and the leading c_T assembly.

Everything checked symbolically (sympy) AND numerically (mpmath).
"""
import sympy as sp
import mpmath as mp

# ============ SYMBOLIC PART ============
print("="*70)
print("SYMBOLIC CHECKS (sympy)")
print("="*70)

y, tau, w, j = sp.symbols('y tau w j', positive=True)

# ---- (D1) the one-step formula and its series ----
# Claim: log(rho_j/rho_{j-1}) = 2y + 2 log( 2y/(e^{2y}-1) ),  y=j tau.
step = 2*y + 2*sp.log(2*y/(sp.exp(2*y)-1))
step_series = sp.series(step, y, 0, 8).removeO()
print("\n(D1) step = 2y + 2 log(2y/(e^{2y}-1)); series in y:")
print("   ", sp.expand(step_series))
# expected -y^2/3 + y^4/90 - ...
print("   claimed: -y^2/3 + y^4/90 - ...")

# ---- (D2) integrate the step to get log rho_j ----
# The step is log rho_j - log rho_{j-1}.  With y = j tau, treat j as continuous,
# step as a function of y; log rho_j = sum over the ladder.  In the continuum (Euler-Maclaurin
# leading term) log rho_j ~ (1/tau) Integral_0^{y} step(y') dy'  because each j-increment is dy'=tau.
# Actually: log rho_j = sum_{i=1}^{j} step(i tau).  ~ (1/tau) int_0^{j tau} step dy.
intg = sp.integrate(step_series, y)   # integrate the y-series
logrho = sp.expand(intg/tau)          # divide by tau (sum spacing) ; substitute y=j tau afterwards
logrho_in_j = sp.expand(logrho.subs(y, j*tau))
print("\n(D2) log rho_j ~ (1/tau) int_0^{j tau} step dy, with y=j tau:")
print("   ", logrho_in_j)
print("   claimed: -(1/9) tau^2 j^3 + (1/450) tau^4 j^5 - (2/19845) tau^6 j^7 + ...")
# extract coefficients
c3 = logrho_in_j.coeff(j,3)
c5 = logrho_in_j.coeff(j,5)
c7 = logrho_in_j.coeff(j,7)
print(f"   coeff j^3 = {c3}   (claim -(1/9)tau^2 = {-sp.Rational(1,9)*tau**2})")
print(f"   coeff j^5 = {c5}   (claim (1/450)tau^4 = {sp.Rational(1,450)*tau**4})")
print(f"   coeff j^7 = {c7}   (claim -(2/19845)tau^6 = {-sp.Rational(2,19845)*tau**6})")

# ---- (D3) vartheta^3(1-cos w),  vartheta = (1/2) w d/dw ----
ws = sp.symbols('w', positive=True)
f = 1 - sp.cos(ws)
def vth(expr):
    return sp.Rational(1,2)*ws*sp.diff(expr, ws)
v3 = sp.simplify(vth(vth(vth(f))))
print("\n(D3) vartheta^3(1-cos w), vartheta=(1/2)w d/dw:")
print("   ", sp.expand_trig(sp.simplify(v3)))
claim_v3 = sp.Rational(1,8)*ws*(-ws**2*sp.sin(ws) + 3*ws*sp.cos(ws) + sp.sin(ws))
print("   claim (w/8)(-w^2 sin w+3w cos w+sin w):", sp.expand(claim_v3))
print("   difference simplifies to:", sp.simplify(v3 - claim_v3))

# leading term of vartheta^3(1-cos w) for large w: -(w^3/8) sin w
print("   leading large-w term: -(w^3/8) sin w  (the -w^2 sin w * w/8 piece)")

# ---- assembly c_T ----
# E^T_lead = -(1/9) tau^2 * vartheta^3(1-cos w)|_lead = -(1/9)tau^2 * (-(w^3/8) sin w)
#          = (1/72) tau^2 w^3 sin w.   tau^2 w^3 with w=sqrt(2/tau): w^3 = (2/tau)^{3/2}=2^{3/2} tau^{-3/2}
#          tau^2 w^3 = 2^{3/2} tau^{1/2} = 2 sqrt2 sqrt(tau).
tauv = sp.symbols('tau', positive=True)
tau2w3 = tauv**2 * (2/tauv)**sp.Rational(3,2)
print("\nAssembly: tau^2 w^3 =", sp.simplify(tau2w3), " (claim 2 sqrt2 sqrt tau =", 2*sp.sqrt(2)*sp.sqrt(tauv), ")")
cT_sym = sp.Rational(1,72)*tau2w3
print("E^T_lead = (1/72) tau^2 w^3 sin w =", sp.simplify(cT_sym), "* sin w")
print("=> c_T =", sp.simplify(cT_sym/sp.sqrt(tauv)), " vs sqrt2/36 =", sp.sqrt(2)/36, "=", float(sp.sqrt(2)/36))
