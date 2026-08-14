"""
ADVERSARIAL deep-dive: the EXACT one-step log-ratio of the travel form factor,
hunting for the correction terms the (D1) 'exact' claim drops, and checking whether
they corrupt the LEADING c_T or only the subleading O(sqrt tau)/O(tau) remainder.

Exact one-step:  t_j/t_{j-1} = Cq(1+2(j-1)) * Aq(1+2j)/Aq(1+2(j-1)).
Model one-step:  hat_t_j/hat_t_{j-1} = (2/tau)/((2j+2)(2j+1)).
rho_j/rho_{j-1} = -(t_j/t_{j-1})/(hat ratio)   [the -1 absorbs (-1)^j alternation: rho def has (-1)^j].

We compute the EXACT log(rho_j/rho_{j-1}) as a function of (q,j) and expand in tau at FIXED y=j*tau.
Compare to the claimed  2y + 2 log(2y/(e^{2y}-1))  and IDENTIFY the leading correction's
order in tau (does it carry a 1/j i.e. tau/y factor => O(tau) per-step => subleading? or O(1)?).
"""
import mpmath as mp
import sympy as sp

# ---------- (A) exact symbolic one-step in q, then expand at fixed y=j tau ----------
print("="*70)
print("(A) EXACT one-step log-ratio, expanded at fixed y = j*tau")
print("="*70)
q, j, tau = sp.symbols('q j tau', positive=True)

def Aq(k): return 2*q/(1 - q**(k+1))
def Cq(k): return 2*q**(k+3)/(1 - q**(k+2)) - 2*q**(k+2)/(1 - q**(k+1))

# t_j/t_{j-1} = Cq(1+2(j-1)) * Aq(1+2j)/Aq(1+2(j-1))
k_prev = 1 + 2*(j-1)
ratio_t = Cq(k_prev) * Aq(1+2*j)/Aq(1+2*(j-1))
# model ratio hat_j/hat_{j-1} = (2/tau)/((2j+2)(2j+1))
ratio_hat = (2/tau)/((2*j+2)*(2*j+1))
# rho ratio with (-1) alternation: rho_j/rho_{j-1} = (t_j/t_{j-1})/((-1)*ratio_hat)
ratio_rho = ratio_t/((-1)*ratio_hat)

# substitute q = exp(-tau), j = y/tau, expand in tau at fixed y
yv = sp.symbols('y', positive=True)
expr = ratio_rho.subs({q: sp.exp(-tau), j: yv/tau})
logexpr = sp.log(expr)
# series in tau at fixed y
ser = sp.series(logexpr, tau, 0, 3)
print("log(rho_j/rho_{j-1}) expanded in tau at fixed y=j tau:")
print("   ", sp.simplify(ser.removeO()))
print()
# leading (tau^0) part should be 2y+2log(2y/(e^{2y}-1)); print it and the tau^1 coefficient
ser0 = sp.series(logexpr, tau, 0, 1).removeO()
print("tau^0 part:", sp.simplify(ser0))
print("claimed   : 2y + 2 log(2y/(e^{2y}-1)) =", sp.simplify(2*yv+2*sp.log(2*yv/(sp.exp(2*yv)-1))))
print("difference:", sp.simplify(ser0 - (2*yv+2*sp.log(2*yv/(sp.exp(2*yv)-1)))))
# tau^1 coefficient
full = sp.series(logexpr, tau, 0, 2).removeO()
coef_tau1 = sp.simplify((full - ser0)/tau)
print("\ntau^1 coefficient of the per-step log ratio:")
print("   ", sp.simplify(coef_tau1))
# small-y behaviour of the tau^1 coeff (does it vanish as y->0? what power?)
print("   small-y series of tau^1 coeff:", sp.series(coef_tau1, yv, 0, 5))

# ---------- (B) Compare to the BULK per-step (alpha,gamma) to see the '-1' ----------
print("\n" + "="*70)
print("(B) BULK per-step for comparison (should carry an extra -1 at tau^1 ... or where?)")
print("="*70)
def alpha(k): return 2/(q**(-(k+1))-1)
def gam(k): return alpha(k+1)-alpha(k)
# bulk term s_j = alpha(1+2j) prod gamma; model same hat.
ratio_s = gam(1+2*(j-1))*alpha(1+2*j)/alpha(1+2*(j-1))
ratio_rho_b = ratio_s/((-1)*ratio_hat)
exprb = ratio_rho_b.subs({q: sp.exp(-tau), j: yv/tau})
logb = sp.log(exprb)
ser0b = sp.series(logb, tau, 0, 1).removeO()
print("BULK tau^0 part:", sp.simplify(ser0b))
fullb = sp.series(logb, tau, 0, 2).removeO()
coef_tau1_b = sp.simplify((fullb - ser0b)/tau)
print("BULK tau^1 coeff:", sp.simplify(coef_tau1_b))
print("travel-minus-bulk tau^1 coeff:", sp.simplify(coef_tau1 - coef_tau1_b))
print("  (claim: bulk has an extra constant '-1' that travel lacks)")
