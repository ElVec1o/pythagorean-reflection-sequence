"""
Verify the candidate's no-go technical claims on the IZ Gaussian rep of Y3(1/q):
  exponent of integrand ~ Psi(xi)/tau with Psi = -xi^2/4 + (1/2)Li2(-e^{i xi}) + O(tau).
Claims to check:
 (A) saddle xi*(tau) ~ pi/2 - i*eta, eta ~ (1/2)log(1/tau) (recedes).
 (B) tau*Psi''(xi*) -> 0 like 1/log(1/tau)  [degenerate Hessian -- the obstruction].
 (C) the leading exponent uses ONLY the O(1/tau) dilog piece; the 2(1-q)q factor stays O(1).
We work with the LEADING (tau->0) exponent  P(xi) = -xi^2/4 + (1/2) Li2(-e^{i xi}),
solve P'(xi*)=0, and report tau*P''(xi*)... but note P is tau-independent, so the
tau-dependence of the saddle enters through the FULL exponent. We instead use the
exact log-D form so the saddle is tau-dependent and honest.
"""
import mpmath as mp
mp.mp.dps = 50

def qpoch_inf(a, p, NM=400000):
    tol = mp.mpf(10)**(-(mp.mp.dps+8))
    r = mp.mpc(1); ai = a
    for _ in range(NM):
        r *= (1-ai); ai *= p
        if abs(ai) < tol: break
    return r

# full log integrand exponent (excluding the gaussian prefactor constant):
#   integrand = exp(xi^2/log(p^2)) / D(xi),  log(p^2) = -4 tau
#   so exponent F(xi) = xi^2/(-4 tau) - log D(xi).
# Psi/tau form: F = (1/tau)[ -xi^2/4 - tau log D ].  As tau->0, log(-q^4 e^{ixi};p)_inf ~ -(1/2tau)Li2(-e^{ixi}).
def logD(xi, q):
    p = q*q
    e = mp.e**(1j*xi)
    return mp.log(qpoch_inf(p,p)) + mp.log(qpoch_inf(-q**4*e,p)) + mp.log(qpoch_inf(-2*(1-q)*q*e,p))

def F(xi, q):
    tau = -mp.log(q)
    return xi*xi/(-4*tau) - logD(xi, q)

print("Saddle of FULL exponent F(xi)=xi^2/(-4tau)-logD(xi), Newton from xi0=pi/2 - i*0.5*log(1/tau):")
print(f"{'tau':>12} {'Re xi*':>11} {'Im xi*':>11} {'eta/(.5 log 1/t)':>17} {'tau*F''(xi*)':>14} {'/(1/log(1/t))':>14}")
for taus in ['0.02','0.01','0.005','0.002','0.001','0.0005','0.0002']:
    tau = mp.mpf(taus); q = mp.e**(-tau)
    eta0 = mp.mpf('0.5')*mp.log(1/tau)
    xi = mp.mpf('1.5707963') - 1j*eta0
    f1 = lambda z: mp.diff(lambda zz: F(zz,q), z)
    try:
        xs = mp.findroot(f1, xi)
    except Exception as ex:
        print(f"{float(tau):>12.2e}  root fail: {ex}"); continue
    Fpp = mp.diff(lambda zz: F(zz,q), xs, 2)
    eta = -xs.imag
    ratio_eta = eta/eta0
    tFpp = tau*Fpp
    invlog = 1/mp.log(1/tau)
    print(f"{float(tau):>12.2e} {float(xs.real):>11.5f} {float(xs.imag):>11.5f} {float(ratio_eta):>17.4f} {mp.nstr(tFpp,5):>14} {float(abs(tFpp)/invlog):>14.4f}")

print()
print("INTERPRETATION:")
print(" - If Im xi* -> -inf (eta grows ~ 0.5 log(1/tau)): saddle RECEDES (claim A).")
print(" - If |tau*F''(xi*)| -> 0 and |tau F''|/(1/log(1/t)) -> const: Hessian degenerates")
print("   logarithmically (claim B) => naive steepest-descent next order ~ 1/(tau F'') DIVERGES.")
