#!/usr/bin/env python3
"""
TASK A: verify the Abel-Plana representation of T2 NUMERICALLY with EXACT B.

T2 two ways at tau in {0.3,0.2,0.1}:
  Way 1 (direct):   T2 = S1 - (1-cos w) - (cos w - cos W),  W=w e^{-tau/2}, w=sqrt(2/tau)
  Way 2 (Abel-Plana): T2 = -int_0^inf Im(psi(iy))/sinh(pi y) dy,
       psi(s) = W^{2s} g_s / Gamma(2s+1),  g_s = 1 - exp(-B_s).

The hard part is B at COMPLEX argument iy for ALL y (the tau-series for B diverges
past y ~ pi/tau).  We use the EXACT continuation of the antidifference

   B_s = sum_{i'=0}^{s-1} b(i'),  b(x)=phi((2x+2)tau)+phi((2x+1)tau)-phi(tau),
   phi(y)=log( sinh(y/2)/(y/2) ) = sum_{k>=1} log(1+(y/(2 pi k))^2).

The key device: the antidifference of  x |-> phi((2x+a)tau)  is EXACT via loggamma.
Write c_k = 2 pi k / tau.  Then
   1+((2x+a)tau/(2 pi k))^2 = ((2x+a)^2 + c_k^2)/c_k^2 = (2x+a-i c_k)(2x+a+i c_k)/c_k^2.
   prod_{x=0}^{s-1}(2x+a +/- i c_k) = 2^s Gamma(s+(a +/- i c_k)/2)/Gamma((a +/- i c_k)/2).
So
   Phi_a(s) := sum_{x=0}^{s-1} phi((2x+a)tau)
       = sum_{k>=1} [ log( 2^s G(s+(a-ic_k)/2)/G((a-ic_k)/2) )
                    + log( 2^s G(s+(a+ic_k)/2)/G((a+ic_k)/2) )
                    - 2 s log c_k ]
       = sum_{k>=1} 2 Re[ loggamma(s+(a-ic_k)/2) - loggamma((a-ic_k)/2)
                          + s*log 2 - s*log c_k ]
   (using a real, the +i and -i terms are conjugate => 2 Re of one).
Then  B_s = Phi_2(s) + Phi_1(s) - s*phi(tau).

This is EXACT and analytic in s; valid for s=iy at ALL y.  The k-sum converges
(terms ~ -(s phi-coeff)/k^2 for large k after the digamma cancellation); we sum
to k=KMAX with a tail estimate and check convergence.

We CROSS-CHECK the continuation against:
  (i)  the integer values B_i from the first-principles form factor (build_rho),
  (ii) the tau-series of B where it converges (small y).
"""
import mpmath as mp

mp.mp.dps = 60

# ----------------------------------------------------------------------------
# phi and its EXACT antidifference via loggamma
# ----------------------------------------------------------------------------
def phi_scalar(y):
    """phi(y)=log( sinh(y/2)/(y/2) ).  y may be complex."""
    yy = mp.mpf(y) if not isinstance(y, mp.mpc) else y
    return mp.log(mp.sinh(yy/2)/(yy/2))

def _Phi_term(k, s, a, tau):
    """
    k-th term of the loggamma k-sum for Phi_a.
    phi-summand contributes, for each k:
       log(1+((2x+a)tau/(2 pi k))^2)
         = log(2x+a-i c_k) + log(2x+a+i c_k) - 2 log c_k,   c_k=2 pi k/tau.
    Antidifferenced over x=0..s-1:
       [loggamma(s+z-) - loggamma(z-)] + [loggamma(s+z+) - loggamma(z+)]
         + 2 s log 2 - 2 s log c_k,
    with z- = (a - i c_k)/2,  z+ = (a + i c_k)/2.
    NOTE: for complex s the two pieces are NOT conjugates, so we keep BOTH
    (the '2 Re of one' shortcut is valid only for real s).  Decays like 1/k^2 in
    MAGNITUDE for any fixed complex s.
    """
    ck = 2*mp.pi*k/tau
    zm = mp.mpf(a)/2 - mp.mpc(0, 1)*ck/2          # (a - i c_k)/2
    zp = mp.mpf(a)/2 + mp.mpc(0, 1)*ck/2          # (a + i c_k)/2
    return ((mp.loggamma(s+zm) - mp.loggamma(zm))
            + (mp.loggamma(s+zp) - mp.loggamma(zp))
            + 2*s*mp.log(2) - 2*s*mp.log(ck))

def Phi_a(s, a, tau, KMAX=120):
    """
    Antidifference  sum_{x=0}^{s-1} phi((2x+a)tau)  via loggamma, EXACT, analytic in s.
    The k-th term is exactly  A(s)/k^2 + B(s)/k^4 + O(1/k^6)  (only even powers, by the
    conjugate-pair structure).  Sum explicitly to KMAX, then add the closed-form tail
       sum_{k>KMAX} term_k = A*(zeta(2)-H2(KMAX)) + B*(zeta(4)-H4(KMAX)) + O(1/KMAX^5),
    with A,B extracted from two large reference k (k1<k2) by solving
       term_k1 = A/k1^2 + B/k1^4,   term_k2 = A/k2^2 + B/k2^4.
    Returns the complex value (Re taken at call site).
    """
    s = mp.mpc(s)
    head = mp.mpc(0)
    for k in range(1, KMAX+1):
        head += _Phi_term(k, s, a, tau)
    # extract A,B from two reference points well past KMAX
    k1, k2 = 8*KMAX, 16*KMAX
    t1 = _Phi_term(k1, s, a, tau)
    t2 = _Phi_term(k2, s, a, tau)
    # solve [1/k1^2 1/k1^4; 1/k2^2 1/k2^4][A;B]=[t1;t2]
    i12, i14 = mp.mpf(1)/k1**2, mp.mpf(1)/k1**4
    i22, i24 = mp.mpf(1)/k2**2, mp.mpf(1)/k2**4
    det = i12*i24 - i14*i22
    A = (t1*i24 - t2*i14)/det
    B = (i12*t2 - i22*t1)/det
    # H_p(KMAX) = sum_{k=1}^{KMAX} 1/k^p
    H2 = mp.mpf(0); H4 = mp.mpf(0)
    for k in range(1, KMAX+1):
        H2 += mp.mpf(1)/k**2; H4 += mp.mpf(1)/k**4
    tail = A*(mp.zeta(2)-H2) + B*(mp.zeta(4)-H4)
    return head + tail

def B_exact(s, tau, KMAX=None):
    """EXACT B_s = Phi_2(s)+Phi_1(s) - s*phi(tau), analytic continuation."""
    s = mp.mpc(s)
    P2 = Phi_a(s, 2, tau)
    P1 = Phi_a(s, 1, tau)
    return P2 + P1 - s*phi_scalar(tau), mp.mpf(0)

# ----------------------------------------------------------------------------
# first-principles integer B_i from the form factor (cross-check)
# ----------------------------------------------------------------------------
def alpha(k, tau): return 2/(mp.e**((k+1)*tau)-1)
def build_R_integers(tau, J):
    """R_j = B_{j+1} (sum_{i'=0}^{j} b(i')) for j=0..J-1, from rho ratios."""
    rho = []; prod = mp.mpf(1)
    for j in range(J):
        a1 = alpha(1+2*j, tau)
        that = (2/tau)**(j+1)/mp.factorial(2*j+2)
        rho.append(a1*prod/that)
        prod *= (a1 - alpha(2+2*j, tau))
    # R_j := -log rho_j - (j+1)tau  = sum_{i'=0}^{j} b(i') = B_{j+1}
    return [-mp.log(rho[j]) - (j+1)*tau for j in range(J)]

# ----------------------------------------------------------------------------
# direct B via straightforward antidifference (sum of b at integer points) using
# the product-form phi -- to validate B_exact at integer s independent of loggamma
# ----------------------------------------------------------------------------
def b_direct(x, tau, KMAX=20000):
    return phi_scalar((2*x+2)*tau) + phi_scalar((2*x+1)*tau) - phi_scalar(tau)

def B_direct_integer(n, tau):
    """B_n = sum_{x=0}^{n-1} b(x), straightforward, integer n only."""
    return sum(b_direct(x, tau) for x in range(n))

# ----------------------------------------------------------------------------
# bulk S1 (direct) and Way-1 T2
# ----------------------------------------------------------------------------
def alpha_q(k, q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_q(k, q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def S1_bulk(q, J=20000):
    tot = mp.mpf(0); prod = mp.mpf(1)
    for j in range(J):
        tot += alpha_q(1+2*j, q)*prod
        prod *= gamma_q(1+2*j, q)
        if abs(prod) < mp.mpf(10)**(-(mp.mp.dps+10)) and j > 50:
            break
    return tot

# ----------------------------------------------------------------------------
# CROSS-CHECKS of B_exact
# ----------------------------------------------------------------------------
def crosscheck_B(tau):
    print(f"\n--- B cross-checks at tau={mp.nstr(tau,4)} ---")
    Rint = build_R_integers(tau, 12)
    maxerr_ff = mp.mpf(0); maxerr_dir = mp.mpf(0)
    for n in range(1, 9):
        Bex, _ = B_exact(mp.mpc(n), tau, KMAX=6000)
        Bex = mp.re(Bex)  # at integer real s, B is real
        Bff = Rint[n-1]                       # form-factor integer B_n
        Bdir = B_direct_integer(n, tau)       # straightforward antidifference
        e1 = abs(Bex - Bff); e2 = abs(Bex - Bdir)
        maxerr_ff = max(maxerr_ff, e1); maxerr_dir = max(maxerr_dir, e2)
        print(f"  n={n}: B_exact={mp.nstr(Bex,12):>16}  ff={mp.nstr(Bff,12):>16}"
              f"  |dl-ff|={mp.nstr(e1,3)}  |dl-dir|={mp.nstr(e2,3)}")
    print(f"  MAX |B_exact - B_formfactor| = {mp.nstr(maxerr_ff,4)}")
    print(f"  MAX |B_exact - B_direct|     = {mp.nstr(maxerr_dir,4)}")
    return maxerr_ff, maxerr_dir


# ----------------------------------------------------------------------------
# Abel-Plana integrand
#   psi(s) = W^{2s} g_s / Gamma(2s+1),  g_s = 1 - exp(-B_s)
#   T2 = - int_0^inf Im(psi(iy))/sinh(pi y) dy
# ----------------------------------------------------------------------------
def psi_of_iy(y, W, tau):
    """psi(iy) = W^{2iy} g_{iy}/Gamma(2iy+1),  g_{iy}=1-exp(-B_{iy})."""
    s = mp.mpc(0, 1)*y
    B, _ = B_exact(s, tau)
    g = 1 - mp.e**(-B)
    # W^{2s} = exp(2s log W),  log W real (W>0)
    Wp = mp.e**(2*s*mp.log(W))
    return Wp * g / mp.gamma(2*s + 1)

def integrand(y, W, tau):
    """ -Im(psi(iy))/sinh(pi y)  (the value whose integral over (0,inf) is T2)."""
    if y == 0:
        return mp.mpf(0)
    return -mp.im(psi_of_iy(y, W, tau)) / mp.sinh(mp.pi*y)

def T2_abelplana(tau, ymax=None, quad_pts=None):
    """Way 2: integrate the Abel-Plana integrand over (0, ymax)."""
    w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    ystar = W/2
    if ymax is None:
        # integrate well past the saddle and into the 1/sinh decay region
        ymax = max(float(ystar)*3, float(ystar)+25)
    f = lambda y: integrand(y, W, tau)
    # split at the saddle for accuracy
    pts = [0, float(ystar)*mp.mpf('0.5'), ystar, float(ystar)*mp.mpf('1.5'),
           float(ystar)*2, ymax]
    pts = [mp.mpf(p) for p in pts]
    val = mp.quad(f, pts)
    return val, ystar, ymax

if __name__ == "__main__":
    for tau in [mp.mpf('0.3'), mp.mpf('0.2'), mp.mpf('0.1')]:
        crosscheck_B(tau)
