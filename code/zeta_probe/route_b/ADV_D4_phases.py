"""
ADVERSARIAL: re-derive the phase-shift constants C2,C3 analytically and pin signs.

Setup at a pole: cos w = c_T sqrt(tau) sin w + O(tau^{3/2}), sin w = O(1).
W   = w e^{-tau/2},  W-w = w(e^{-tau/2}-1) = -w tau/2 + w tau^2/8 - ...
W/q = w e^{+tau/2},  W/q - w = w(e^{tau/2}-1) = +w tau/2 + w tau^2/8 + ...
w tau/2 = (1/2) sqrt(2/tau) tau = (1/2) sqrt(2 tau) = sqrt(tau/2) = (1/sqrt2) sqrt tau.

cos(w+d) = cos w cos d - sin w sin d.
For d = W-w = -(1/sqrt2)sqrt tau + O(tau^{3/2}):
  cos d = 1 + O(tau),  sin d = -(1/sqrt2)sqrt tau + O(tau^{3/2}).
  cos W = [c_T sqrt tau sin w](1) - sin w[-(1/sqrt2)sqrt tau] + O(tau^{3/2})
        = sqrt tau sin w (c_T + 1/sqrt2) + O(tau^{3/2}).
  => C2 = c_T + 1/sqrt2.

For d = W/q - w = +(1/sqrt2)sqrt tau:
  cos(W/q) = c_T sqrt tau sin w - sin w (1/sqrt2) sqrt tau = sqrt tau sin w (c_T - 1/sqrt2).
  => C3 = c_T - 1/sqrt2 = -17 sqrt2/36 ?

Check c_T - 1/sqrt2 = sqrt2/36 - 1/sqrt2.  1/sqrt2 = sqrt2/2 = 18 sqrt2/36. So c_T-1/sqrt2 = (1-18)sqrt2/36 = -17 sqrt2/36.  YES.
And c_T + 1/sqrt2 = (1+18) sqrt2/36 = 19 sqrt2/36.  numerically:
"""
import sympy as sp
import mpmath as mp

cT = sp.sqrt(2)/36
print("c_T + 1/sqrt2 =", sp.simplify(cT + 1/sp.sqrt(2)), "=", sp.nsimplify(cT+1/sp.sqrt(2)), "=", float(cT+1/sp.sqrt(2)))
print("   as k sqrt2/36:", sp.simplify((cT+1/sp.sqrt(2))/(sp.sqrt(2)/36)), "* sqrt2/36  => 19 sqrt2/36")
print("c_T - 1/sqrt2 =", sp.simplify(cT - 1/sp.sqrt(2)), "=", float(cT-1/sp.sqrt(2)))
print("   as k sqrt2/36:", sp.simplify((cT-1/sp.sqrt(2))/(sp.sqrt(2)/36)), "* sqrt2/36  => -17 sqrt2/36")
print("   -17 sqrt2/36 =", float(-17*sp.sqrt(2)/36))

# Now a fully symbolic addition-formula expansion to O(sqrt tau), trusting cos w = c_T sqrt tau sin w.
tau, st = sp.symbols('tau s', positive=True)   # st = sqrt(tau)
sw = sp.symbols('sw')  # sin w (O(1))
cw = cT*st*sw          # cos w to leading order at pole
# W-w to O(tau^{3/2}): -(1/sqrt2) st + O(st^3); cos(W-w)=1+O(tau), sin(W-w)=-(1/sqrt2)st+O(st^3)
d_W = -1/sp.sqrt(2)*st
cosW = cw*1 - sw*sp.sin(d_W)
cosW_lead = sp.series(cosW, st, 0, 2).removeO()
print("\ncos W (lead in st) =", sp.simplify(cosW_lead), " => /(st sw) =", sp.simplify(cosW_lead/(st*sw)))
d_Wq = 1/sp.sqrt(2)*st
cosWq = cw*1 - sw*sp.sin(d_Wq)
cosWq_lead = sp.series(cosWq, st, 0, 2).removeO()
print("cos(W/q) (lead) =", sp.simplify(cosWq_lead), " => /(st sw) =", sp.simplify(cosWq_lead/(st*sw)))

# numeric cross check against the C2,C3 limits found in ADV_D4_independent
print("\nNumeric targets: C2 =", float(cT+1/sp.sqrt(2)), " C3 =", float(cT-1/sp.sqrt(2)))
