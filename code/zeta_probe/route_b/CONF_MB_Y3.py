"""
CONF_MB_Y3.py  —  Mellin-Barnes / confluence attack on the Hahn-Exton q-Bessel Y3.

GOAL (the lone open U-gate input): prove the ABSOLUTE bound
    |Y3(1/q) - (3/sqrt2) tau^{3/2} sin w|  <=  C tau^{5/2}     (relative O(tau)),
w = sqrt(2/tau), at the travel poles.  Y3(x) = sum_k d_k x^{2k+3},
  d_k = (-2)^k (1-q)^k q^{k^2+3k} / [ (q^2;q^2)_k (q^5;q^2)_k ]  (= x^3 0phi1(-;q^5;q^2,2(1-q)q^4 x^2)).

WHAT THIS SCRIPT ESTABLISHES (all scalar mpmath/sympy, dps<=50, no big arrays):

(1) EXACT Mellin-Barnes (Ismail-Zhang Gaussian) rep, VERIFIED to 22-40 digits:
      Y3(1/q) = q^{-3} (q^2;q^2)_inf / [(q^5;q^2)_inf sqrt(4 pi tau)] *
                INT_{-inf}^{inf} e^{-xi^2/(4tau)} / D(xi) dxi,
      D(xi) = (q^2;q^2)_inf (-q^4 e^{i xi};q^2)_inf (-2(1-q)q e^{i xi};q^2)_inf.
    [The literal vertical-Barnes contour with q-Gamma DIVERGES: the theta factor q^{s(s-1)/2}
     blows up like exp(|log q| t^2/2) on Re s = c.  The Gaussian/real-line IZ form is the
     convergent one.]

(2) The absolute-contour bound (V's lem:T2abs model) does NOT transfer:
    on the real axis |integrand| ~ e^{Re Psi} ~ 1e77 while Y3 ~ 1e-4 (deep cancellation);
    the stationary phase is a COMPLEX saddle xi* ~ pi/2 - i*eta(tau), eta ~ (1/2)log(1/tau),
    O(1)-displaced (NOT a clean horizontal shift), so |.| is not harmless on any shifted line.
    Two-saddle leading steepest-descent overshoots by a stable ~17/16 and the next-order SD
    correction DIVERGES (saddle is O(1) from the dilog/pole singularities).  => SD does not
    reach relative O(tau).  (Confirmed: only the conjugate saddle pair exists, no coalescence.)

(3) The PRODUCTIVE route = the elementary q-series operator method (same machinery as
    derive_ck.py for Sig_1^T).  Y3(1/q) = (1/q^3) B, B = sum_k a_k w^{2k} rho_k, with
      a_k w^{2k} = 3 (-w^2/2)^k / [k! (2k+3)!!],   G0 := sum_k a_k w^{2k} = 3 j1(w)/w  (elementary),
      rho_k = 1 + k tau + d_2(k) tau^2 + ...,  d_2(k) = -k^3/9 + k^2/12 - 23k/36  (q-series, exact).
    Operator resummation B = sum_p tau^p d_p(theta) G0,  theta = (w/2) d/dw.

    KEY RESULT:  P2 := (1/q^3)[ G0 + tau theta G0 + tau^2 d_2(theta) G0 ]  captures Y3(1/q) to
    ABSOLUTE O(tau^{5/2}) = relative O(tau):  |Y3 - P2|/(tau^{5/2}|sin w|) -> ~0.045 (bounded,
    monotone over a 170x range in tau, m=4..70).  And via w^2=2/tau plus the pole relation
    cos w_m = +(sqrt2/36) sqrt(tau) sin w + O(tau^{3/2}), P2 reduces to (3/sqrt2) tau^{3/2} sin w
    EXACTLY:  the sin-coefficient 37 sqrt2/24 (from the sin part) minus sqrt2/24 (from the
    cos part via the pole relation) = 36 sqrt2/24 = 3/sqrt2.  CLEAN.

    => The TASK BOUND holds with C ~ 3.72 (vs the bare leading), numerically certain across
    m=4..70 with a clean, bounded, monotone constant.

(4) HONEST RIGOR STATUS: the bound is NOT yet a from-scratch proof.  P2 is exact & elementary,
    but the remainder |Y3 - P2| = |(1/q^3) sum_{p>=3} tau^p d_p(theta) G0| being uniformly
    O(tau^{5/2}) needs a UNIFORM bound on the (divergent, asymptotic) operator tail.  The d_p(k)
    are elementary rationals but their k-degree grows irregularly (d_1:1,d_2:3,d_3:4,d_6:9,
    others >=20 at maxk=20), so term p ~ tau^{p - deg_p/2} does NOT decrease monotonically =>
    Poincare-asymptotic, not convergent.  This uniform-tail bound is exactly the program's
    standing lem:cos-tier open piece (== NS-b/(G2) in lifting_U.tex).  No citable with-remainder
    q-Bessel confluence exists (lit checked: Koornwinder-Swarttouw / Olde Daalhuis 1994 give the
    LEADING pointwise limit only; the growing-argument z~1/sqrt(1-q) regime is an open gap).
"""
import mpmath as mp

POLES = [mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

def qpoch_k(a, p, k):
    r = mp.mpf(1); aj = a
    for _ in range(k):
        r *= (1 - aj); aj *= p
    return r

def qpoch_inf(a, p, tol=None, NM=600000):
    if tol is None: tol = mp.mpf(10) ** (-(mp.mp.dps + 10))
    r = mp.mpc(1) if isinstance(a, (complex, mp.mpc)) else mp.mpf(1)
    ai = a
    for _ in range(NM):
        r *= (1 - ai); ai *= p
        if abs(ai) < tol: break
    return r

def Y3_series(x, q, K=6000):  # well-conditioned at x=1/q
    s = mp.mpf(0)
    for k in range(K):
        dk = (mp.mpf(-2))**k * (1 - q)**k * q**(k*k + 3*k) / (qpoch_k(q**2, q**2, k) * qpoch_k(q**5, q**2, k))
        t = dk * x**(2*k + 3); s += t
        if k > 10 and abs(t) < mp.mpf(10)**(-(mp.mp.dps + 5)) * max(abs(s), mp.mpf(1)): break
    return s

def Y3_IZ(q):  # (1) Ismail-Zhang Gaussian rep at x=1/q (NB: slow + catastrophic AT poles; use off-pole)
    p = q*q; tau = -mp.log(q); Z2 = 2*(1 - q)
    logp2 = mp.log(p*p)  # = -4 tau
    pinf = qpoch_inf(p, p); p52 = qpoch_inf(q**5, p)
    T = float(9*mp.sqrt(-logp2)) + 25
    def integ(xx):
        e = mp.e**(1j*xx)
        den = pinf * qpoch_inf(-q**4*e, p) * qpoch_inf(-q*Z2*e, p)
        return (mp.e**(xx*xx/logp2) / den).real
    val = mp.quad(integ, [-T, -T/2, 0, T/2, T])
    return (1/q**3) / mp.sqrt(4*mp.pi*tau) * val * (pinf/p52)

# (3) the operator approximant P2
def G0(w):  return 3*mp.sin(w)/w**3 - 3*mp.cos(w)/w**2          # = 3 j1(w)/w
def thp(w, d):                                                   # theta^d G0, theta=(w/2)d/dw
    g = G0
    for _ in range(d):
        g = (lambda gg: (lambda x: (x/2)*mp.diff(gg, x)))(g)
    return g(w)
def P2(q):
    tau = -mp.log(q); w = mp.sqrt(2/tau)
    d2op = -thp(w, 3)/9 + thp(w, 2)/12 - mp.mpf(23)/36*thp(w, 1)
    return (1/q**3) * (G0(w) + tau*thp(w, 1) + tau**2*d2op)


if __name__ == "__main__":
    print("="*92)
    print("(1) IZ Gaussian MB rep verified OFF-pole (at poles the real-axis integral is catastrophic):")
    for taus, xs in [('0.2', '1.3'), ('0.05', '1.0')]:
        mp.mp.dps = 40
        tau = mp.mpf(taus); q = mp.e**(-tau); x = mp.mpf(xs)
        # IZ at general x:
        p = q*q; Zx2 = 2*(1-q)*q**2*x**2; logp2 = mp.log(p*p)
        pinf = qpoch_inf(p, p); p52 = qpoch_inf(q**5, p)
        T = float(8*mp.sqrt(-logp2)) + 20
        val = mp.quad(lambda xx: (mp.e**(xx*xx/logp2) /
              (pinf*qpoch_inf(-q**4*mp.e**(1j*xx), p)*qpoch_inf(-q*Zx2*mp.e**(1j*xx), p))).real, [-T, 0, T])
        iz = x**3/mp.sqrt(4*mp.pi*tau)*val*(pinf/p52)
        ser = Y3_series(x, q)
        print(f"   tau={taus} x={xs}: series={mp.nstr(ser,16)}  IZ={mp.nstr(iz,16)}  reldiff={mp.nstr((iz-ser)/ser,4)}")

    print("="*92)
    print("(3) Operator approximant P2 vs Y3 vs target (3/sqrt2)tau^{3/2}sin w, at travel poles:")
    print(f"{'m':>3} {'tau':>12} {'|Y3-P2|/(t^2.5|sinw|)':>21} {'|Y3-target|/t^2.5':>17}")
    for m in [4, 8, 12, 16, 20, 30, 40, 50, 60, 70]:
        if m >= len(POLES): continue
        q = POLES[m]; tau = -mp.log(q); w = mp.sqrt(2/tau)
        mp.mp.dps = 50 + int(2.5*float(w))
        q = POLES[m]; tau = -mp.log(q); w = mp.sqrt(2/tau); sinw = mp.sin(w)
        yt = Y3_series(1/q, q); p2 = P2(q)
        target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
        print(f"{m:>3} {float(tau):>12.5e} {mp.nstr(abs(yt-p2)/(tau**mp.mpf('2.5')*abs(sinw)),7):>21}"
              f" {mp.nstr(abs(yt-target)/tau**mp.mpf('2.5'),7):>17}")
    print("="*92)
    print("BOUND HOLDS numerically: |Y3(1/q)-(3/sqrt2)tau^{3/2}sinw| <= ~3.72 tau^{5/2} (m=4..70);")
    print("P2 remainder constant ~0.045 (rel sin w), bounded & monotone. RIGOR: uniform tail bound")
    print("on sum_{p>=3} tau^p d_p(theta)G0 is the lem:cos-tier open piece (== NS-b/(G2)).")
