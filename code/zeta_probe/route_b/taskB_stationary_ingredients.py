#!/usr/bin/env python3
"""
TASK B: verify the stationary-phase INGREDIENTS numerically at tau in {0.02,0.005,0.001}.

Setup (from lemcos_context.md):
  tau = -ln q,  w = sqrt(2/tau),  W = w e^{-tau/2}.
  psi(s) = W^{2s} g_s / Gamma(2s+1),   g_s = 1 - e^{-B_s}.
  B_s = sum_{i'=0}^{s-1} b(i'),  b(x) = phi((2x+2)tau)+phi((2x+1)tau)-phi(tau),
       phi(y) = log( sinh(y/2)/(y/2) ).
  T2 = - int_0^infty Im(psi(iy)) / sinh(pi y) dy.

  integrand = -A(y) sin Phi(y),
     A(y)   = |g_{iy}| sqrt( coth(pi y)/(pi y) ),
     Phi(y) = 2 y log W + arg(g_{iy}) - arg Gamma(1+2 i y).

  Stationary phase: y* = W/2,  Phi''(y*) = -4/W,
     amplitude*sqrt(2pi/|Phi''|) ~ O(sqrt tau),
     T2 ~ A(y*) sqrt(2 pi/|Phi''|) sin(Phi(y*) - pi/4)  ==  Re[g_{s*} e^{iW}],  s*=iW/2.

CRITICAL: B_s must be computed by ANALYTIC CONTINUATION of  sum_{i'=0}^{s-1} b(i').
We use the exact antidifference of phi via its Hurwitz/log-Gamma representation, valid
for COMPLEX s, with NO restriction |y|<pi/tau.  We cross-check against the tau-series
where the latter converges (|y| < pi/tau).
"""
import mpmath as mp
mp.mp.dps = 60

# ---------- exact phi and its antidifference ----------
def phi(y):
    # phi(y) = log( sinh(y/2)/(y/2) ), analytic, even, entire-ish (poles of log at sinh zeros => y=2pi i k)
    return mp.log(mp.sinh(y/2)/(y/2))

# Antidifference of phi(a*x+c) in x:  we need
#   Sum_{x=0}^{s-1} phi((2x+2)tau) etc.  But the cleaner route:
# B_s = sum_{i'=0}^{s-1} b(i'),  with  b(x)=phi((2x+2)tau)+phi((2x+1)tau)-phi(tau).
# phi(y) = log sinh(y/2) - log(y/2).
# log sinh(z) part:  sinh(z) = (e^z - e^{-z})/2;  log-Gamma antidifference is messy.
# Instead use the PRODUCT formula  phi(y) = sum_{k>=1} log(1 + (y/(2 pi k))^2).
# Then  Sum_x log(1+((a x + c)/(2 pi k))^2)  has closed antidifference via log-Gamma:
#   1 + (u/(2 pi k))^2 = (1 + i u/(2 pi k))(1 - i u/(2 pi k)).
# Sum_{x=0}^{s-1} log(1 + i(ax+c)/(2 pi k))
#   = sum log( (a/(2 pi k)) ( x + (c/a) + 2 pi k/(i a) ) ) ... -> Gamma ratio.
# We package it directly: define the FULL B_s via the analytic continuation of the partial
# sum using mpmath's ability to handle the *finite-difference* through a convergent-in-k series
# whose each term has a closed Gamma antidifference.

def Bs_product(s, tau, Kmax=4000):
    """
    B_s analytic in s, via product formula of phi summed over Fourier modes k>=1.
    For each k:  contribution_k(s) = Sum_{x=0}^{s-1} [ L((2x+2)tau,k) + L((2x+1)tau,k) - L(tau,k) ]
    where L(y,k) = log(1 + (y/(2 pi k))^2) = log(1+ i y/(2pi k)) + log(1 - i y/(2pi k)).
    Antidifference of log(1 + i(ax+b)/(2pi k)) over x=0..s-1:
       = sum_{x} log( a/(2pi k) * (x + b/a - 2pi k i/a) )    [factor a/(2pi k) i out carefully]
    We instead just use loggamma:  Sum_{x=0}^{s-1} log(x + r) = loggamma(s+r) - loggamma(r).
    Write 1 + i(ax+b)/(2pi k) = (i a/(2pi k)) ( x + (b/a) + (2pi k/(i a)) )
       = (i a/(2pi k)) ( x + r ),  r = b/a + 2pi k/(i a) = b/a - i*2pi k/a.
    So Sum_{x=0}^{s-1} log(1 + i(ax+b)/(2pi k))
       = s*log(i a/(2pi k)) + loggamma(s+r) - loggamma(r).
    Similarly for the conjugate (-i) sign.  And the -phi(tau) term is just -s*phi(tau).
    Two pieces: y=(2x+2)tau -> a=2tau,b=2tau ; y=(2x+1)tau -> a=2tau,b=tau.
    """
    s = mp.mpc(s)
    twopi = 2*mp.pi
    total = mp.mpc(0)
    # the -phi(tau) constant part summed s times:
    total += -s*phi(tau)
    for k in range(1, Kmax+1):
        denom = twopi*k
        for (a, b) in ((2*tau, 2*tau), (2*tau, tau)):
            a = mp.mpf(a); b = mp.mpf(b)
            # + i branch
            for sign in (mp.mpc(0,1), mp.mpc(0,-1)):
                coef = sign*a/denom
                r = b/a + denom/(sign*a)   # x + r form;  sign*a => careful
                # log(1 + sign*(ax+b)/denom) ... wait we want 1 + sign*i? recompute below
                pass
            # do it explicitly to avoid sign confusion:
            # term = log(1 + i(ax+b)/denom) + log(1 - i(ax+b)/denom)
            # piece +i:
            coef_p = mp.mpc(0,1)*a/denom
            r_p = b/a + denom/(mp.mpc(0,1)*a)
            sum_p = s*mp.log(coef_p) + mp.loggamma(s+r_p) - mp.loggamma(r_p)
            # piece -i:
            coef_m = mp.mpc(0,-1)*a/denom
            r_m = b/a + denom/(mp.mpc(0,-1)*a)
            sum_m = s*mp.log(coef_m) + mp.loggamma(s+r_m) - mp.loggamma(r_m)
            total += sum_p + sum_m
        # convergence check: contribution decays like 1/k^2 * |s|^2-ish; break when tiny
        if k > 50:
            # crude tail magnitude
            mag = abs((mp.mpf(tau)*float(abs(s))/denom))
            if mag < mp.mpf(10)**(-40) and k > 200:
                break
    return total

# ---------- tau-series cross check for B_s (valid |s|<pi/tau) ----------
import sympy as sp
def Bs_tauseries(s, tau, Nmax=40):
    # B_s = sum_{n>=1} f_n tau^{2n} Q_n(s-1),  f_n=[y^{2n}]phi,  Q_n(m)=sum_{i=0}^m[(2i+2)^{2n}+(2i+1)^{2n}-1]
    # phi(y)=log(sinh(y/2)/(y/2)); its even Taylor coeffs f_n = B_{2n}/(2n*(2n)!)*? -> get numerically.
    # f_n from series of log(sinh(y/2)/(y/2)) at 0.
    yv = sp.symbols('y')
    ser = sp.series(sp.log(sp.sinh(yv/2)/(yv/2)), yv, 0, 2*Nmax+2).removeO()
    poly = sp.Poly(ser, yv)
    fdict = {int(m): c for (m,), c in poly.terms()}
    s = mp.mpc(s)
    tot = mp.mpc(0)
    for n in range(1, Nmax+1):
        fn = fdict.get(2*n, 0)
        if fn == 0:
            continue
        fn = mp.mpf(sp.nsimplify(fn)) if not isinstance(fn, sp.Float) else mp.mpf(str(fn))
        # Q_n(m) with m = s-1 :  sum_{i=0}^{m}[(2i+2)^{2n}+(2i+1)^{2n}-1] -> Faulhaber, analytic in m.
        # Use direct analytic continuation via Hurwitz: sum_{i=0}^{m} (2i+c)^{2n}
        #   = 2^{2n} sum_{i=0}^m (i + c/2)^{2n} = 2^{2n}(zeta(-2n, c/2) - zeta(-2n, m+1+c/2))
        m = s-1
        def powsum(c):  # sum_{i=0}^m (2i+c)^{2n}
            return (mp.mpf(2)**(2*n))*(mp.zeta(-2*n, mp.mpf(c)/2) - mp.zeta(-2*n, m+1+mp.mpf(c)/2))
        Qn = powsum(2) + powsum(1) - (m+1)  # -1 summed m+1 times
        tot += fn * mp.mpf(tau)**(2*n) * Qn
    return tot

# ---------- exact B_s on integers from first principles (form factor) ----------
def alpha_t(k, t): return 2/(mp.e**((k+1)*t)-1)
def buildR(t, J):
    rho = []; prod = mp.mpf(1)
    out = []
    for jj in range(J):
        a1 = alpha_t(1+2*jj, t); that = (2/t)**(jj+1)/mp.factorial(2*jj+2)
        rho.append(a1*prod/that); prod *= (a1-alpha_t(2+2*jj, t))
        out.append(-mp.log(rho[jj])-(jj+1)*t)
    return out  # out[j] = B_{j+1}

# ============ sanity: B at integers matches all three routes ============
print("="*90)
print("SANITY 0: B_s at integer s -- product vs tau-series vs first-principles form factor")
print("="*90)
for tau in [mp.mpf('0.02'), mp.mpf('0.005')]:
    R = buildR(tau, 6)
    print(f"\ntau={mp.nstr(tau,4)}")
    for si in range(1, 5):
        bp = Bs_product(si, tau)
        bt = Bs_tauseries(si, tau)
        bff = R[si-1]  # B_si
        print(f"  s={si}: product={mp.nstr(bp.real,12)}  tauser={mp.nstr(bt.real,12)}  formfac={mp.nstr(bff,12)}")
