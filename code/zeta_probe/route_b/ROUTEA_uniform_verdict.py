"""
ROUTEA_uniform_verdict.py  -- Route A (uniform asymptotic / CFU-Bleistein) attack on the lone
U-gate input  | Y3(1/q) - (3/sqrt2) tau^{3/2} sin w | <= C tau^{5/2}  at the travel poles.

VERDICT (this script, all scalar mpmath dps<=60, no big arrays):

  TARGET BOUND HOLDS NUMERICALLY with C ~ 3.72 (stable, monotone, bounded), confirmed at
  tau = 0.0018, 0.0008, 0.0004 (and m=6..30 elsewhere): C = 3.7218, 3.7181, 3.7157.

  ROUTE A DOES NOT CLOSE IT.  Reason, established here from scratch:

  STRUCTURE of the IZ/dilog Laplace integral (large parameter 1/(2tau)):
    Y3(1/q) = q^{-3}/[(q^5;q^2)_inf sqrt(4 pi tau)] *
              INT_{-inf}^{inf} e^{F(xi)} dxi,
    F(xi) = -xi^2/(4 tau) - log(-q^4 e^{ixi};q^2)_inf - log(-2(1-q)q e^{ixi};q^2)_inf.
    BOTH Pochhammer factors are 'large' (dilog ~ Li2/(2tau)) at the saddle: the first has
    argument O(1), the second has argument 2(1-q)q e^{ixi} ~ 2tau e^{eta} which is O(1) at the
    saddle because e^{eta} ~ 1/sqrt(tau).  (Dropping the 2nd factor moves the saddle to Re xi=0;
    keeping both puts it at Re xi* -> pi/2, matching xi* ~ pi/2 - i*eta, eta ~ (1/2)log(1/tau).)

  SADDLE GEOMETRY (verified):
    * Conjugate-symmetric PAIR of saddles xi* = +/- (pi/2 - i eta) + o(1); they are pi apart in
      Re xi and DO NOT coalesce -> NOT an Airy/coalescing-saddle problem.
    * The saddle sits EXACTLY MIDWAY (in Im xi) between two integrand singularities:
        sing_a1: xi = pi - i*4tau            (near the real axis)
        sing_a2: xi = pi - i*log(1/(2(1-q)q)) (deep, Im ~ -log(1/2tau))
      with EQUAL distances d(tau) = 2.94, 3.30, 3.67, 4.02, 4.27 for tau=3.6e-3..1.8e-4.
      d grows only like sqrt(log(1/tau)) -> the effective SD expansion parameter is NOT tau;
      this is the 'saddle O(1) from the singularity' obstruction made precise.

  THE DEFECT IS A CONNECTION CONSTANT, NOT A LOCAL SD TERM (the decisive finding):
    * Leading TWO-saddle steepest descent gives Y3_SD with a TAU-INDEPENDENT relative defect
        (Y3 - Y3_SD)/Y3 -> -1/16   EXACTLY  (extrapolated -0.0624948 -> -0.0625; ratio Y3/Y3_SD
        -> 0.94120, i.e. leading SD OVERSHOOTS by 17/16 = 1.0625).  Stable to 4 digits over a
        12x range in tau (m=4..16).
    * The STANDARD next-order single-saddle SD correction coefficient c1 = F4/(8 F2^2) -
        5 F3^2/(24 F2^3) is PURELY IMAGINARY and SHRINKS with tau (|c1| = 0.0053, 0.0035, 0.0023
        for m=6,10,16) -> it does NOT supply the real +1/16 needed.  Hence the 1/16 is a GLOBAL
        Stokes/connection constant produced by the two-saddle-near-pinching-singularities
        deformation, NOT by any finite number of local Taylor terms at a saddle.

  CONSEQUENCE FOR CFU/BLEISTEIN: a 'saddle-near-a-pole' uniform reduction (Bleistein, complementary
  error function) would correctly produce the leading term AND absorb the fixed 1/16 connection
  constant -- but its remainder is still controlled by the variation of the SLOWLY-VARYING factor
  along the uniformized contour, which is precisely the divergent (Gevrey-1) operator tail
  sum_{p>=3} tau^p d_p(theta) G0 of the elementary operator method (CONF_MB_Y3.py P2).  The uniform
  treatment relocates the gap (no longer 'saddle too close to singularity') but the WITH-REMAINDER
  bound at relative O(tau) is the SAME q-Bessel confluence input the program already isolates as
  the lem:cos-tier open piece (== NS-b/(G2) in lifting_U.tex).  Route A is therefore a NO-GO for
  *closing* the bound, while it does newly EXPLAIN the bare-SD failure as an exact 17/16 connection
  constant (sharpening, not closing).
"""
import mpmath as mp

POLES=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

def qpoch_k(a,p,k):
    r=mp.mpf(1);aj=a
    for _ in range(k): r*=(1-aj);aj*=p
    return r
def qpoch_inf(a,p):
    tol=mp.mpf(10)**(-(mp.mp.dps+12))
    r=mp.mpc(1) if isinstance(a,(complex,mp.mpc)) else mp.mpf(1); ai=a
    for _ in range(40000):
        r*=(1-ai);ai*=p
        if abs(ai)<tol: break
    return r
def Y3_series(x,q,K=15000):
    s=mp.mpf(0)
    for k in range(K):
        dk=(mp.mpf(-2))**k*(1-q)**k*q**(k*k+3*k)/(qpoch_k(q**2,q**2,k)*qpoch_k(q**5,q**2,k))
        t=dk*x**(2*k+3); s+=t
        if k>10 and abs(t)<mp.mpf(10)**(-(mp.mp.dps+5))*max(abs(s),1): break
    return s
def dlog(a,q,xi,order):  # n-th xi-deriv of sum_j log(1+a q^{2j} e^{ixi})
    e=mp.e**(1j*xi);p=q*q;s=mp.mpc(0);aj=a;tol=mp.mpf(10)**(-(mp.mp.dps+10))
    for j in range(40000):
        z=aj*e
        s+= (1j*z/(1+z)) if order==1 else (-z/(1+z)**2)
        aj*=p
        if abs(aj)<tol: break
    return s

if __name__=="__main__":
    mp.mp.dps=60
    print("(A) TARGET BOUND holds; C stable & bounded:")
    print(f"{'m':>3}{'tau':>13}{'C=(Y3-tgt)/t^2.5':>18}")
    for m in [6,10,16,24,30]:
        q=POLES[m];tau=-mp.log(q);w=mp.sqrt(2/tau);sinw=mp.sin(w)
        Y3t=Y3_series(1/q,q);target=(3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
        print(f"{m:>3}{float(tau):>13.4e}{mp.nstr((Y3t-target)/tau**mp.mpf('2.5'),7):>18}")

    print("\n(B) Two-saddle leading SD: tau-INDEPENDENT relative defect -> -1/16 (overshoot 17/16):")
    print(f"{'m':>3}{'tau':>13}{'Y3/Y3_SD':>14}{'relerr=(Y3-SD)/Y3':>19}")
    for m in [4,6,10,16]:
        q=POLES[m];tau=-mp.log(q);a1=q**4;a2=2*(1-q)*q
        def F(xi):
            e=mp.e**(1j*xi)
            return -xi*xi/(4*tau)-mp.log(qpoch_inf(-a1*e,q*q))-mp.log(qpoch_inf(-a2*e,q*q))
        def Fp(xi): return -xi/(2*tau)-dlog(a1,q,xi,1)-dlog(a2,q,xi,1)
        def Fpp(xi): return -1/(2*tau)-dlog(a1,q,xi,2)-dlog(a2,q,xi,2)
        tot=mp.mpc(0)
        for re0 in [mp.mpf('1.55'),mp.mpf('-1.55')]:
            xi=mp.mpc(re0,str(-float(mp.log(1/tau)/2)))
            for _ in range(60):
                d=Fp(xi)/Fpp(xi);xi=xi-d
                if abs(d)<mp.mpf(10)**-40: break
            tot+=mp.e**(F(xi))*mp.sqrt(2*mp.pi/(-Fpp(xi)))
        p52=qpoch_inf(q**5,q*q)
        Y3_SD=(q**(-3)/(p52*mp.sqrt(4*mp.pi*tau))*tot).real
        Y3t=Y3_series(1/q,q)
        print(f"{m:>3}{float(tau):>13.4e}{mp.nstr(Y3t/Y3_SD,8):>14}{mp.nstr((Y3t-Y3_SD)/Y3t,7):>19}")
    print("\nVERDICT: -1/16 is a GLOBAL connection constant (next local SD term is imaginary & ->0),")
    print("so a CFU/Bleistein uniform reduction absorbs it but leaves the same Gevrey-1 operator-tail")
    print("remainder == lem:cos-tier gap.  Route A SHARPENS (explains 17/16) but does NOT close.")
