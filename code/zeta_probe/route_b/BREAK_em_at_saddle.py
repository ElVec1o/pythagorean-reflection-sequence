"""
BREAK test (1)/(2): Does the Euler-Maclaurin / Faddeev-dilog asymptotic for log D(xi)
keep a GENUINE O(tau)-per-term structure AT THE ACTUAL COMPLEX MOVING SADDLE xi*,
or does the saddle's O(1) proximity to the Li2 branch point poison the expansion
(EM remainder NOT going down, or per-term EM corrections NOT ordered in tau)?

We do NOT assume the saddle. We take the EXACT log D(xi) (sum-of-logs) and its EM
series, evaluate BOTH at the true complex saddle xi*(tau) of the FULL exponent W,
and report:
  - dist(xi*, nearest Li2 branch point)  [branch pt of Li2(-a e^{i xi}): 1+a e^{i xi}=0]
  - per-term EM magnitudes |T1|,|T2|(the 1/tau-Li2 term), |EM_0|, |tau-term|
  - the EM REMAINDER  R_N = exact - EM_N  for N=2,3,4 terms, and R_N/tau^{?}
If R_N shrinks by a clean power of tau as N grows AND as tau->0, EM is healthy at the saddle.
If R_N stalls or the per-term ordering inverts, the saddle proximity breaks it.

Scalar mpmath only. dps<=50.
"""
import mpmath as mp

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+12)); s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1-ai); ai *= p
    return s

def logD_exact(xi, tau):
    # log D(xi) = sum-of-logs of the two infinite products (drop the (q^2;q^2)_inf prefactor-cancel piece)
    q = mp.e**(-tau); e = mp.e**(1j*xi)
    out = mp.mpc(0)
    for a in [q**4, 2*(1-q)*q]:
        out += poch_logsum(-a*e, q**2)
    return out

def logD_EM(xi, tau, nterm):
    # EM series for S(a)=sum log(1+ a q^{2n} e^{ixi}); a in {q^4, 2(1-q)q}
    q = mp.e**(-tau); e = mp.e**(1j*xi)
    out = mp.mpc(0); pieces=[]
    for a in [q**4, 2*(1-q)*q]:
        z = a*e   # argument a*e^{ixi}; factor is (1 + z q^{2n})
        I = -mp.polylog(2, -z)/(2*tau)          # T1: O(1/tau)
        g0 = z/(1+z)
        term0 = mp.mpf(1)/2*mp.log(1+z)         # EM_0: O(1)
        s = I + term0
        if nterm >= 3:
            fp1 = -2*tau*g0
            s += -mp.mpf(1)/12*fp1               # O(tau)
        if nterm >= 4:
            gpp = (2*tau)**2*g0*(1-g0)*(1-2*g0)
            fp3 = -2*tau*gpp
            s += mp.mpf(1)/720*fp3               # O(tau^3)
        out += s; pieces.append((I, term0))
    return out

def Wderiv1(xi, tau):
    # d/dxi of W = -xi^2/(4tau) - logD(xi); exact via sum
    q = mp.e**(-tau); e = mp.e**(1j*xi); tol = mp.mpf(10)**(-(mp.mp.dps+12))
    D1 = mp.mpc(0)
    for a in [q**4, 2*(1-q)*q]:
        uu = a*e
        while abs(uu) > tol:
            g = uu/(1+uu); D1 += 1j*g; uu *= q**2
    return -(2*xi)/(4*tau) - D1

def saddle(tau):
    return mp.findroot(lambda xi: Wderiv1(xi, tau),
                       mp.pi/2 - 0.5j*mp.log(1/tau), tol=mp.mpf(10)**-25)

def branchdist(xi, tau):
    # nearest branch pt: 1 + a e^{i xi_b}=0 => xi_b = -i log(-1/a) (mod 2pi). a near 1 => xi_b near pi.
    q = mp.e**(-tau)
    ds = []
    for a in [q**4, 2*(1-q)*q]:
        xib = -1j*mp.log(-1/a)   # principal; -1/a real negative => log = log|.|+ i pi
        # consider xib and xib+2pi etc; pick nearest in xi-plane
        for k in (-1,0,1):
            ds.append(abs(xi - (xib + 2*mp.pi*k)))
    return min(ds)

print("EM health AT THE COMPLEX SADDLE xi*(tau):")
print(f"{'tau':>8} {'Re xi*':>9} {'Im xi*':>9} {'dist_bp':>8} {'|R2|':>11} {'|R3|':>11} {'|R4|':>11} {'R3/tau^? ':>10}")
prev=None
for tau in [mp.mpf('0.08'),mp.mpf('0.04'),mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005')]:
    mp.mp.dps = max(40, int(40 + 1.0/float(tau)))
    xs = saddle(tau)
    ex = logD_exact(xs, tau)
    R2 = abs(ex - logD_EM(xs,tau,2))
    R3 = abs(ex - logD_EM(xs,tau,3))
    R4 = abs(ex - logD_EM(xs,tau,4))
    db = branchdist(xs, tau)
    print(f"{float(tau):>8.4f} {float(mp.re(xs)):>9.5f} {float(mp.im(xs)):>9.5f} {float(db):>8.4f} "
          f"{mp.nstr(R2,4):>11} {mp.nstr(R3,4):>11} {mp.nstr(R4,4):>11}", flush=True)
    # report R3 scaling vs previous tau
    if prev is not None:
        t0,r0 = prev
        p = float(mp.log(R3/r0)/mp.log(tau/t0))
        print(f"         (R3 power-law exponent vs prev tau: p={p:.3f}  -> EM_N=4 term should make R3~tau^3)")
    prev=(tau,R3)
print()
print("INTERPRETATION:")
print(" - If dist_bp stays O(1) (NOT ->0) AND R_N shrinks by clean powers (R3~tau^3, R4~tau^5),")
print("   the EM/Faddeev series is HEALTHY at the saddle: remainder genuinely O(tau^k), NOT poisoned.")
print(" - If dist_bp ->0 or R_N stalls / power<expected, saddle proximity breaks per-term ordering.")
