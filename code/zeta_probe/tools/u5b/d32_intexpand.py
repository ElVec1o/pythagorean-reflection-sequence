#!/usr/bin/env python3
# ROUTE D3.2 -- show the continuum WKB integral I(tau) is ANALYTICALLY tractable:
#   I = (1/tau) INT_{x_*}^{1} arccos(C - D x^2) dx/x,  C=cosh(1.5tau), D=(1-q)q^{1/2},
#       x_*^2=(C-1)/D.
# Substitute u = x^2, du=2x dx => dx/x = du/(2u):
#   I = (1/(2tau)) INT_{u_*}^{1} arccos(C - D u) du/u,  u_*=(C-1)/D.
# This is an ELEMENTARY integral (arccos of linear / u). Its small-tau expansion gives
# the leading w and the -3pi/4 constant in CLOSED FORM. We verify by exact symbolic
# expansion of the integrand's leading behaviour and by matching the numeric I.
#
# Leading order: as tau->0, C->1, D->tau (since (1-q)~tau, q^{1/2}->1), u_*->(C-1)/D.
# C-1 = cosh(1.5tau)-1 ~ (9/8)tau^2; D ~ tau(1 - 3tau/2 ...). So u_* ~ (9/8)tau ->0.
# Near u=u_* the arccos ->0 (turning); near u=1, arccos(C-D) with C-D ~ 1-tau => arccos~sqrt(2tau).
# The integral is dominated by small u (u from u_*~tau up to 1): arccos(C-Du)~sqrt(2(Du-(C-1)))
# = sqrt(2D) sqrt(u-u_*).  So I ~ (1/(2tau)) sqrt(2D) INT_{u_*}^1 sqrt(u-u_*)/u du.
# INT_{u_*}^1 sqrt(u-u_*)/u du = 2 sqrt(1-u_*) - 2 sqrt(u_*) arctan(sqrt((1-u_*)/u_*))?
# Let's just verify the leading w and the constant numerically from this reduced integral
# and confirm it equals the full I, then expand.

import mpmath as mp
mp.mp.dps = 50

def bcoef(n, q):
    return (q**mp.mpf("1.5") + q**mp.mpf("-1.5")) - 2*(1-q)*q**(2*n + mp.mpf("0.5"))

def Ifull(tau):
    q=mp.e**(-tau); C=mp.cosh(mp.mpf("1.5")*tau); D=(1-q)*q**mp.mpf("0.5")
    ustar=(C-1)/D
    g=lambda u: mp.acos(C-D*u)/u
    return mp.quad(g,[ustar,1])/(2*tau), ustar, C, D

# exact elementary antiderivative check: d/du [arccos(C-Du)] = D/sqrt(1-(C-Du)^2).
# INT arccos(C-Du)/u du -- integrate by parts: = arccos(C-Du) ln u |  + INT ln u * D/sqrt(1-(C-Du)^2) du
# (boundary at u=u_* arccos=0; at u=1 ln1=0) => I_int = INT_{u_*}^1 ln u * D/sqrt(1-(C-Du)^2) du.
# So  I = (1/(2tau)) INT_{u_*}^1 (-ln u) * (-D)/sqrt(...) ... let's just verify this rep equals Ifull,
# which proves the reduction (a clean elementary representation good for asymptotics).
def Iparts(tau):
    q=mp.e**(-tau); C=mp.cosh(mp.mpf("1.5")*tau); D=(1-q)*q**mp.mpf("0.5")
    ustar=(C-1)/D
    h=lambda u: mp.log(u)*D/mp.sqrt(1-(C-D*u)**2)
    val=mp.quad(h,[ustar,1])   # = [arccos*ln u] - I_orig boundary...
    # IBP: INT arccos(C-Du)/u du = [arccos(C-Du)*ln u]_{u_*}^1 - INT ln u * d/du arccos du
    #     = (0 - 0) - INT_{u_*}^1 ln u * D/sqrt(1-(C-Du)^2) du = -val
    return (-val)/(2*tau)

print("=== verify elementary IBP representation of the WKB integral ===")
for tau in [mp.mpf("0.01"),mp.mpf("0.003"),mp.mpf("0.001")]:
    If,ustar,C,D=Ifull(tau)
    Ip=Iparts(tau)
    w=mp.sqrt(2/tau)
    print(f"tau={float(tau):.4f}: Ifull={mp.nstr(If,12)}  Iparts={mp.nstr(Ip,12)}  match={mp.nstr(abs(If-Ip),3)}")
    print(f"           I-w={mp.nstr(If-w,9)} (->-3pi/4={mp.nstr(-3*mp.pi/4,9)})  u_*={mp.nstr(ustar,5)}")
print()

# Now expand I - w analytically via the dominant-balance integral.
# With D~tau, C-1~(9/8)tau^2, u_* = (C-1)/D ~ (9/8)tau (small). Leading arccos(C-Du)~sqrt(2(Du-(C-1)))
# for Du-(C-1) small AND <<1; but near u=1, C-Du ~ 1-tau u? C-Du at u=1 is C-D~1-tau, arccos~sqrt(2tau).
# The FULL leading integral (set C=1 region, D=tau, ignore (C-1) i.e. u_*->0 leading):
#   I0 = (1/(2tau)) INT_0^1 arccos(1 - tau u)/u du.  arccos(1-tau u) = sqrt(2 tau u)(1+ (tau u)/12 + ...).
#   => I0 ~ (1/(2tau)) INT_0^1 sqrt(2 tau u)/u du = (1/(2tau)) sqrt(2tau) INT_0^1 u^{-1/2} du
#        = (1/(2tau)) sqrt(2tau) * 2 = sqrt(2tau)/tau = sqrt(2/tau) = w.   GOOD: leading = w.
# The -3pi/4 comes from the NEXT order (the lower cutoff u_* and the arccos correction).
# Verify I0 (with u_*->0, C->1 exactly D=tau) numerically gives w + (a different constant),
# to confirm the constant is a genuine subleading effect captured by the exact integral.
print("=== toy integral I0 = (1/2tau) INT_0^1 arccos(1-tau u)/u du  -> w + const? ===")
for tau in [mp.mpf("0.01"),mp.mpf("0.003"),mp.mpf("0.001"),mp.mpf("0.0003")]:
    g=lambda u: mp.acos(1-tau*u)/u
    # integrand ~ sqrt(2tau u)/u = sqrt(2tau) u^{-1/2} near 0 (integrable)
    I0=mp.quad(g,[0,1])/(2*tau)
    w=mp.sqrt(2/tau)
    print(f"  tau={mp.nstr(tau,5)}: I0={mp.nstr(I0,10)}  I0-w={mp.nstr(I0-w,8)}  (I0-w)/sqrt(tau)={mp.nstr((I0-w)/mp.sqrt(tau),6)}")
