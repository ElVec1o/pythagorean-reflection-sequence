"""
BREAK test (3): Re-derive a1 INDEPENDENTLY of the q-series and of the saddle reconstruction.

Compute Y3(1/q) by DIRECT high-precision quadrature of the Ismail-Zhang integral:
  Y3 = q^{-3} (q^2;q^2)_inf / [ (q^5;q^2)_inf sqrt(4 pi tau) ] * INT e^{-xi^2/(4tau)}/D(xi) dxi
  D(xi) = (q^2;q^2)_inf (-q^4 e^{ixi};q^2)_inf (-2(1-q)q e^{ixi};q^2)_inf
The (q^2;q^2)_inf cancels: prefactor numerator (q^2;q^2)_inf / D-internal (q^2;q^2)_inf.
So integrand uses only the two e^{ixi}-products.

Then at each travel pole q_m:
  a1_true(m) = (Y3_quad/target - 1)/tau,  target=(3/sqrt2)tau^{3/2} sin w
Extrapolate a1_true(m) -> tau=0 by Richardson. Compare with q-series value and 1.75077.

This is a CROSS-CHECK that the q-series Y3 used elsewhere is correct and that a1=1.75077
is a property of the FUNCTION (not the series truncation). Scalar mpmath quad, dps<=50.
"""
import mpmath as mp

def poch(a, p, tol=None):
    if tol is None: tol = mp.mpf(10)**(-(mp.mp.dps+12))
    s = mp.mpf(1); ai = a
    while abs(ai) > tol:
        s *= (1-ai); ai *= p
    return s

def Dprod(xi, tau):
    q = mp.e**(-tau); e = mp.e**(1j*xi)
    out = mp.mpc(1)
    for a in [q**4, 2*(1-q)*q]:
        # (-a e^{ixi}; q^2)_inf = prod (1 + a q^{2n} e^{ixi})
        tol = mp.mpf(10)**(-(mp.mp.dps+12)); pr = mp.mpc(1); u = a*e
        while abs(u) > tol:
            pr *= (1 + u); u *= q**2
        out *= pr
    return out

def Y3_quad(tau):
    q = mp.e**(-tau)
    # integrand: e^{-xi^2/4tau}/Dprod(xi)
    f = lambda xi: mp.e**(-xi**2/(4*tau))/Dprod(xi, tau)
    # integrate over real line; e^{-xi^2/4tau} width ~ sqrt(2tau) small; but D varies O(1).
    # use mp.quad with split points; width scale sqrt(tau)
    W = mp.sqrt(tau)
    I = mp.quad(f, [-40*W, -8*W, -2*W, 0, 2*W, 8*W, 40*W])
    p52 = poch(q**5, q**2)
    norm = q**(-3)/(p52*mp.sqrt(4*mp.pi*tau))
    return norm*I

def Y3_series(x, q, K=20000):
    def qk(a, p, k):
        r = mp.mpf(1); aj = a
        for _ in range(k): r *= (1-aj); aj *= p
        return r
    s = mp.mpf(0)
    for k in range(K):
        dk = (mp.mpf(-2))**k*(1-q)**k*q**(k*k+3*k)/(qk(q**2, q**2, k)*qk(q**5, q**2, k))
        t = dk*x**(2*k+3); s += t
        if k > 12 and abs(t) < mp.mpf(10)**(-(mp.mp.dps+6))*max(abs(s),1): break
    return s

with open("poles.txt") as f:
    polesq = [mp.mpf(l.strip()) for l in f if l.strip()]

print("Direct-quadrature Y3 vs q-series Y3, and a1_true extraction:")
print(f"{'m':>3} {'tau':>9} {'Y3_quad/Y3_ser':>16} {'a1_true(quad)':>14} {'a1_true(ser)':>13}")
rows=[]
for m, qp in enumerate(polesq):
    if m < 3 or m > 8: continue
    tau = -mp.log(qp); mp.mp.dps = max(40, int(40 + 1.0/float(tau)))
    q = mp.e**(-tau); w = mp.sqrt(2/tau); sinw = mp.sin(w)
    target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
    Yq = Y3_quad(tau)
    Ys = Y3_series(1/q, q)
    a1q = (Yq/target - 1)/tau
    a1s = (Ys/target - 1)/tau
    rows.append((float(tau), float(a1q.real), float(a1s.real)))
    print(f"{m:>3} {float(tau):>9.5f} {mp.nstr(Yq/Ys,12):>16} {mp.nstr(a1q,8):>14} {mp.nstr(a1s,8):>13}", flush=True)

# Richardson extrapolation a1_true -> 0 using all rows (linear-in-tau fit, last 3)
def lin_extrap(col):
    import numpy as np  # only tiny arrays, no OOM
    T = [r[0] for r in rows[-3:]]; V = [r[col] for r in rows[-3:]]
    # fit V = a + b*tau
    A = np.array([[1.0, t] for t in T]); b = np.array(V)
    sol,*_ = np.linalg.lstsq(A, b, rcond=None)
    return sol[0]
print()
print(f"EXTRAP a1_true(quad)={lin_extrap(1):.6f}   a1_true(ser)={lin_extrap(2):.6f}   (target 1.75077)")
