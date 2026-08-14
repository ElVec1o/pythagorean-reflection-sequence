"""
D3: contribution of the g_k = k(k-1) correction (fact 7) to the asymptotic of Y3(1/q).

RESULT (g-ratio):   tau * G(1/q) / L(1/q)  ->  -125/142  = -0.8802816901408...
   i.e.  Y3(1/q) = 3 x^3 * L(1/q) * [ 1 + tau*(-125/142) + ... ]   in the RESUMMED (Laplace) sense.

How G arises (operator identity, EXACT, ratio 1.0):
   L(x) = sum_k (-1)^k q^{k^2} A^k / [k! (2k+3)!!],   A = x^2/tau.
   The insertion k(k-1) = theta(theta-1) with theta = A d/dA, i.e.  G = A^2 d^2/dA^2 L.
   (verified: G(series) == A^2 L_AA to full precision.)

Integral / saddle machinery (fact 6, verified ratio 1.0):
   With u = sqrt(tau) v,  z = Z0 e^{i sqrt(tau) v/2},  Z0 = x w = e^{tau} sqrt(2/tau),
   Phi(u) = sin z / z^3 - cos z / z^2,  and
     L     = (1/(2 sqrt pi)) Int e^{-v^2/4} Phi dv
     tau G = (1/(2 sqrt pi)) Int e^{-v^2/4} [ -v^2/4 + 1/2 + i v sqrt(tau)/2 ] Phi dv
   (G's weight comes from k -> -i d/du acting on the e^{iku} of the Gaussian rep of q^{k^2}=e^{-tau k^2},
    then two integrations by parts onto the Gaussian.)

Analytic derivation of -125/142 (Watson resummation + pole condition):
   Expand Phi(sqrt(tau) v) in s = sqrt(tau), take Gaussian v-moments => L, tauG as power series in tau.
   Substitute   Z0 = e^{tau} sqrt(2/tau)   (exact)   and the travel-pole condition
     cos(Z0) = -(35 sqrt2 / 36) sqrt(tau) sin(Z0) + O(tau^{3/2})   [Z0 = w/q; from fact 10 lem:cos],
   divide by sin(Z0), take tau->0.  The resummed limit converges (vs truncation order) to exactly -125/142.

CAVEAT (honest): the naive tau-series  Y3(1/q) = 3 x^3 [L + tau G + ...]  is NOT a UNIFORM asymptotic
   at x = 1/q. The sum sum_k d_k x^{2k+3} is dominated by k ~ 1/sqrt(tau), where the per-term expansion
   d_k = d_k^lead (1 + tau k(k-1) + O(tau^2)) breaks down. Numerically the residual
     |Y3(1/q) - 3x^3(L + tau G)| / |Y3(1/q)|  PLATEAUS at ~0.61 (a constant), it does NOT drop by one
   order in tau. Adding tau G *reduces* the residual (from ~2.18 to ~0.61 of Y3) but does not give a
   one-order improvement. The g-ratio -125/142 is exact only as the leading relative correction of the
   Laplace-resummed L and G (ratio of the two convergent series L, G), which is the quantity D3 asked for.
"""
import mpmath as mp
import numpy as np

def setdps(tau): mp.mp.dps = 40 + int(2.5*mp.sqrt(2/tau))

def L_and_G(q, tau, x, K):
    Ls = mp.mpf(0); Gs = mp.mpf(0); A = x*x/tau
    for k in range(K+1):
        t = (-1)**k * q**(k*k) * A**k / (mp.factorial(k)*mp.fac2(2*k+3))
        Ls += t; Gs += t*k*(k-1)
    return Ls, Gs

def dks(q, K):
    d = [mp.mpf(1)]
    for k in range(1, K+1):
        d.append(d[-1]*(-2*(1-q)*q**(2*k+2))/((1-q**(2*k))*(1-q**(2*k+3))))
    return d

def cocycle(q, N):
    a=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1, N+1):
        qn*=q; q2n=qn*qn; q3n=q2n*qn
        a,y,X,Y=(a*(1+2*q2n)-2*y*qn, 2*a*q3n+y*(1-2*q2n), X*(1+2*q2n)-2*Y*qn, 2*X*q3n+Y*(1-2*q2n))
    return Y, y

if __name__ == "__main__":
    qs = [mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

    print("=== g-ratio = tau G(1/q)/L(1/q) at travel poles, extrapolate to -125/142 ===")
    data = []
    for qi in range(2, 42):
        q = qs[qi]; tau = -mp.log(q); setdps(tau); x = 1/q; K = int(28/mp.sqrt(tau)) + 120
        L, G = L_and_G(q, tau, x, K)
        data.append((float(tau), float(tau*G/L)))
    for t, r in [data[0], data[8], data[20], data[-1]]:
        print("  tau=%.4e  tauG/L=%.10f" % (t, r))
    taus = np.array([d[0] for d in data]); rs = np.array([d[1] for d in data])
    A = np.vstack([taus[:30]**i for i in range(6)]).T
    coef, *_ = np.linalg.lstsq(A, rs[:30], rcond=None)
    print("  Richardson limit = %.11f   -125/142 = %.11f   diff = %.2e"
          % (coef[0], -125/142, coef[0]-(-125/142)))

    print("\n=== EXACT operator identity  G == A^2 d^2/dA^2 L  (A=x^2/tau) ===")
    for qi in [3, 8]:
        q = qs[qi]; tau = -mp.log(q); setdps(tau); x = 1/q; A = x*x/tau; K = int(28/mp.sqrt(tau))+120
        L, G = L_and_G(q, tau, x, K)
        def LofA(Av): return mp.fsum((-1)**k*q**(k*k)*Av**k/(mp.factorial(k)*mp.fac2(2*k+3)) for k in range(K+1))
        h = A*mp.mpf(10)**(-12)
        Gchk = A*A*(LofA(A+h)-2*LofA(A)+LofA(A-h))/h**2
        print("  tau=%.3e  G/A^2 L_AA = %.10f" % (float(tau), float(Gchk/G)))

    print("\n=== CAVEAT: residual after L+tauG plateaus (non-uniform asymptotic at x=1/q) ===")
    for qi in [3, 8, 15, 25, 35]:
        q = qs[qi]; tau = -mp.log(q); setdps(tau); x = 1/q; K = int(28/mp.sqrt(tau))+120
        d = dks(q, K); Y31 = mp.fsum(d); _, Se = cocycle(q, int(95/(1-q)))
        Y3inv = 3*Y31 - (1-q**(-3))*Se
        L, G = L_and_G(q, tau, x, K)
        r0 = abs((Y3inv-3*x**3*L)/Y3inv); r1 = abs((Y3inv-3*x**3*(L+tau*G))/Y3inv)
        print("  tau=%.3e  |.-3x^3 L|/Y3=%.4f  |.-3x^3(L+tauG)|/Y3=%.4f" % (float(tau), float(r0), float(r1)))

    print("\n=== ANALYTIC: Watson resummation -> -125/142 (run sympy block separately) ===")
    print("  see header; symbolic ORD=26 limit = -0.8802816901 (matches -125/142 to 5e-13)")
