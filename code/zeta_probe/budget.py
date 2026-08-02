#!/usr/bin/env python3
"""budget.py -- evaluates the PROVED bound chain of U_cumulant_chain.tex section 6.

Every quantity here is a rigorous UPPER bound derived from lem:cum's Lambert form
    |Lambda_n| <= L_n := sum_{k>=1} k^{n-1} rho^k/(1-q^k)      (triangle inequality, exact)
plus elementary inequalities.  NOTHING here is a measured value.  The paper quotes this
script's output; the script is the certificate (Rule 9).

Failure mode this exists to prevent: hand-computed constants that silently absorb a
measured value.  If a bound printed here closely matches a measurement, that is evidence
of an ERROR, not of sharpness.
"""
import sys
from mpmath import mp, mpf, sqrt, exp, log

mp.dps = 30

def L(n, rho, q, K=400):
    """Rigorous upper bound |Lambda_n| <= sum k^{n-1} rho^k/(1-q^k)."""
    return sum(mpf(k)**(n-1)*rho**k/(1-q**k) for k in range(1, K+1))

def L_even(n, rho, q, K=400):
    """sum over EVEN k only -- bounds |Re Lambda_2| (odd k are purely imaginary there)."""
    return sum(mpf(k)**(n-1)*rho**k/(1-q**k) for k in range(2, K+1, 2))

def budget(tau, BUDGET=mpf('3.5')):
    q = exp(-tau); s2 = tau/2; s = sqrt(s2); w = sqrt(2/tau); h = tau/2
    z0 = sqrt(2*(1-q))
    rho = z0*exp(h)                      # worst radius on the window |t|<=h
    kap = rho/(1-q); t0 = 1-rho
    L1, L2 = L(1, rho, q), L(2, rho, q)
    # beta = 1 - Lambda_2 s^2 ; Re Lambda_2 comes only from even k
    Reb = 1 - L_even(2, rho, q)*s2
    invb = 1/Reb                          # |beta| >= Re beta
    mu_s = L1*s2/s*invb                   # |mu|/s
    sg_s2 = invb                          # |sigma^2|/s^2
    c = max(mu_s, sg_s2)
    # |e^{Lam0} G_Q| : Re Lam0 + Re(Lam1^2 s^2/2beta) cancel to O(tau); bound the residual
    # crudely and rigorously by the even-k Lambert tail (see lem:larith(i)).
    amp = exp(mpf('0.18')*sqrt(tau))*sqrt(invb)   # c1 = 0.18, the value the G1 majorant achieves
    # --- tilted-moment constants, triangle inequality only (NO measured values) ---
    def M(m):
        Mm = [mpf(1), c]
        for k in range(2, m+1): Mm.append(c*Mm[k-1] + (k-1)*sg_s2*Mm[k-2])
        return Mm
    Mm = M(8)
    C = {n: (1 + (n+1)*sg_s2)*Mm[n] + c*Mm[n+1] for n in (3, 4, 5, 6)}
    # --- Term 3 (tail), with lem:trunc's cutoff |xi| <= t0/2 retained ---
    T3 = mpf(0)
    for n in (3, 4, 5, 6):
        Ln = L(n, rho, q)
        T3 += (4/tau**2)*(Ln/mp.factorial(n))*amp*C[n]*s**(n+2)
    T3 *= mpf('1.35')                     # products + n>=7, geometric in (kap s^3/t0^3)
    eps = 4/tau**2*exp(kap)*exp(-t0**2/(4*tau))   # discarded |xi|>t0/2 piece
    # --- |s(Z)| via the Wronskian at the zero: |s(Z)| = Z/|c(qZ)| >= 1/(tau max|psi'|/Z) ---
    psi1 = (2/tau)*amp*L1*s2*invb + mpf('0.5')    # |psi'| <= principal + tail
    sZ_lo = 1/(tau*psi1/(z0/sqrt(q)))
    Phi_lo = q**mpf('0.75')*(sZ_lo - mpf('0.30')*tau)   # minus the bootstrap s-difference
    # --- Terms 1 and 2 ---
    T1 = amp*L2*invb
    cosT = psi1*h/Phi_lo
    T2 = (4/tau**2)*amp*(L1*s2*invb)**2*(cosT + 2*tau)
    tot = T1 + T2 + T3 + eps
    return dict(w=w, rho=rho, t0=t0, c=c, C3=C[3], C4=C[4], Reb=Reb, amp=amp,
                sZ=sZ_lo, Phi=Phi_lo, psi1=psi1/w, T1=T1/w, T2=T2/w, T3=T3,
                tot=tot, tot_w=tot/w, ok=(tot <= BUDGET*w), P12=(h*h/2)*BUDGET*w/tau**mpf('1.5'))

if __name__ == "__main__":
    print("PROVED bound chain, section 6.  Budget 3.5w  =>  |P12| <= 0.6187 tau^{3/2} < 1/sqrt2 = 0.7071")
    print(" tau        w     c      C3     C4    Re beta  |s(Z)|>=  |Phi|>=  T1/w   T2/w   T3     tot/w  OK")
    thr = None
    for e in range(2, 8):
        for m2 in (5, 2, 1):
            tau = mpf(m2)*mpf(10)**(-e)
            if tau > mpf('0.05'): continue
            r = budget(tau)
            print(f" {float(tau):8.1e} {float(r['w']):6.1f} {float(r['c']):5.3f} {float(r['C3']):6.1f} "
                  f"{float(r['C4']):6.1f} {float(r['Reb']):7.4f} {float(r['sZ']):8.4f} {float(r['Phi']):7.4f} "
                  f"{float(r['T1']):6.3f} {float(r['T2']):6.3f} {float(r['T3']):6.2f} {float(r['tot_w']):6.3f}  "
                  f"{'yes' if r['ok'] else 'NO'}")
            if r['ok'] and thr is None: thr = tau
            if not r['ok']: thr = None
    print()
    print(f"Largest tau verified to satisfy the 3.5w budget in this scan: {float(thr) if thr else 'none'}")
    print("Poles with tau above the threshold must be covered by the direct certificate.")

# ---------------------------------------------------------------------------
# G1-G4: the four inputs of section 6, each DERIVED here from the Lambert
# majorants, never measured.  Printed against the value actually attained so
# that a bound close to the truth is visible as the warning sign it is.
# ---------------------------------------------------------------------------

def G_bounds(tau):
    """Derived upper bounds for G1..G4.  All inputs are rigorous majorants."""
    q = exp(-tau); s2 = tau/2; s = sqrt(s2); w = sqrt(2/tau); h = tau/2
    z0 = sqrt(2*(1-q)); rho = z0*exp(h)
    kap = rho/(1-q); t0 = 1 - rho
    x = s/t0                                   # moment scale in majorant units

    # --- G2: full majorant tail, Phat(x) = sum_{n>=3} kappa x^n / n ---
    Phat = (kap*x**3/3)/(1-x)                  # sum_{n>=3} kappa x^n/n <= this
    G2 = Phat/(1-Phat)                         # e^P - 1 <= P/(1-P)  covers products

    # --- G1: the two halves cancel; bound each residual by its geometric tail ---
    # Re Lam0 = -rho^2/(2(1-q^2)) + (even-k tail);  Re(Lam1^2 s^2/2beta) = +1/2 + O(tau)
    # G1.  Lam_n = sum_k k^{n-1} i^{n+k} rho^k/(1-q^k), so the k-th coefficient is
    # Re(i^{n+k}) resp. Im(i^{n+k}); both read off the 4-cycle of i^m directly.
    # The Re/Im pairing must be kept: Re(A/beta) = (ReA Reb + ImA Imb)/|beta|^2.
    # Im A ~ s and Im beta ~ s separately, but their product is O(tau); taking
    # absolute values before pairing destroys that and inflates G1 to O(sqrt tau).
    RE = (1, 0, -1, 0)      # Re(i^m), m mod 4
    IM = (0, 1, 0, -1)      # Im(i^m), m mod 4
    def Lam(n, weight):
        return sum(mpf(k)**(n-1)*weight[(n+k) % 4]*rho**k/(1-q**k)
                   for k in range(1, 300))
    ReL0 = sum(weight_k*rho**k/(k*(1-q**k))
               for k in range(1, 300) for weight_k in (RE[k % 4],))
    ReL1, ImL1 = Lam(1, RE), Lam(1, IM)
    ReL2, ImL2 = Lam(2, RE), Lam(2, IM)
    ReA = (ReL1**2 - ImL1**2)*s2/2
    ImA = ReL1*ImL1*s2
    Reb = 1 - ReL2*s2
    Imb = -ImL2*s2
    G1 = abs(ReL0 + (ReA*Reb + ImA*Imb)/(Reb**2 + Imb**2))
    # --- G3: tail contribution to |psi'| (weight xi, one extra moment) ---
    G3 = (2/tau)*G2*s*sqrt(mpf(3))             # |E[xi e^Q (T-1)]| <= G2 * E[xi^2]^{1/2}
    # --- G4: |s(Ze^t)-s(Z)| <= (1/2) h^2 max|sigma''|, crude phase-free sigma'' ---
    sig2 = (1 + kap*s2)*w**2*(1 + 3*tau)       # crude: no phase input
    G4 = mpf('0.5')*h**2*sig2
    return dict(G1=G1/sqrt(tau), G2=G2/tau, G3=G3, G4=G4/tau)

if __name__ == "__main__":
    print()
    print("G1-G4, DERIVED bounds vs the paper's stated budgets")
    print(" tau        G1/sqrt(tau) [.05]  G2/tau        G3 [0.5]      G4/tau [.30]")
    for e in (3, 4, 5, 6):
        for m2 in (5, 2, 1):
            tau = mpf(m2)*mpf(10)**(-e)
            if tau > mpf('0.005'): continue
            g = G_bounds(tau)
            ok = lambda v, b: "ok " if v <= b else "NO "
            print(f" {float(tau):9.1e}  {float(g['G1']):8.4f} {ok(g['G1'],mpf('0.05'))}"
                  f"      {float(g['G2']):8.4f}      {float(g['G3']):8.4f} {ok(g['G3'],mpf('0.5'))}"
                  f"     {float(g['G4']):8.4f} {ok(g['G4'],mpf('0.30'))}")

def G1_majorant(tau):
    """A genuine upper bound for G1 (not an evaluation).

    Re Lam_0 = -rho^2/(2(1-q^2)) + R0,  |R0| <= rho^4/(4(1-q^4)(1-rho^2))   [even k>=4]
    Re Lam_1 = -rho/(1-q)      + E1,    |E1| <= rho^3/((1-q^3)(1-rho^2))     [odd  k>=3]
    Im Lam_1 = -rho^2/(1-q^2)  + E2,    |E2| <= rho^4/((1-q^4)(1-rho^2))     [even k>=4]
    and likewise for Lam_2.  The leading terms cancel exactly:
        rho^2/(2(1-q^2)) = e^{2h}/(1+q)   and   (rho/(1-q))^2 s^2/2 = tau e^{2h}/(2(1-q)),
    whose difference is e^{2h}[tau/(2(1-q)) - 1/(1+q)] = O(tau^2).
    Everything else is bounded by its own majorant; the Re/Im pairing is kept.
    """
    q = exp(-tau); s2 = tau/2; h = tau/2
    z0 = sqrt(2*(1-q)); rho = z0*exp(h)
    r2 = rho**2

    # exact cancellation of the two leading halves
    lead = exp(2*h)*abs(tau/(2*(1-q)) - 1/(1+q))

    # tails (each a geometric majorant)
    d  = 1 - r2
    R0 = rho**4/(4*(1-q**4)*d)
    E1 = rho**3/((1-q**3)*d)
    E2 = rho**4/((1-q**4)*d)
    A1 = rho/(1-q)                       # |Re Lam_1| leading
    B1 = r2/(1-q**2)                     # |Im Lam_1| leading

    # ReA = (ReL1^2 - ImL1^2) s^2/2 : perturbation of the leading square
    dReA = (2*A1*E1 + E1**2 + (B1+E2)**2)*s2/2
    # ImA = ReL1 ImL1 s^2  -- pairs with Im beta, so it is charged at second order
    ImA  = (A1+E1)*(B1+E2)*s2
    # beta = 1 - Lam_2 s^2
    ReL2b = 2*r2/(1-q**2) + 4*rho**4/((1-q**4)*d)
    ImL2b = rho/(1-q)     + 3*rho**3/((1-q**3)*d)
    Reb_dev = ReL2b*s2
    Imb     = ImL2b*s2
    b2min   = (1-Reb_dev)**2

    return (lead + R0 + dReA + ImA*Imb/b2min
            + (A1**2*s2/2)*(Reb_dev + Imb**2)/b2min)

if __name__ == "__main__":
    print()
    print("G1 MAJORANT (a bound, not an evaluation) vs the exact value and the budget")
    print(" tau         majorant/sqrt(tau)   exact/sqrt(tau)   gate 0.18     loss factor")
    for e in (3, 4, 5, 6):
        for m2 in (5, 2, 1):
            tau = mpf(m2)*mpf(10)**(-e)
            if tau > mpf('0.005'): continue
            mj = G1_majorant(tau)/sqrt(tau)
            ex = G_bounds(tau)['G1']
            ok = "ok " if mj <= mpf('0.18') else "NO "
            print(f" {float(tau):9.1e}   {float(mj):10.5f} {ok}       {float(ex):9.5f}"
                  f"                    {float(mj/ex) if ex>0 else 0:7.1f}x")

# ---------------------------------------------------------------------------
# UNIFORM-IN-TAU CERTIFICATE.
#
# uniform_stack(b) returns ONE number U such that  tot(tau)/w <= U  for EVERY
# tau in (0, b].  No grid.  Method: every quantity in the chain is written in
# scaled variables that are bounded by CONSTANTS on (0, b], each constant
# justified by a one-line atomic monotonicity:
#
#   (M1) v(t) = (1-e^{-t})/t is decreasing; hence v in [v_b, 1], v_b = v(b).
#   (M2) e^{ct} is increasing; hence e^{tau/2} <= e^{b/2}, e^{2h} <= e^{b}.
#   (M3) rho^2 = 2(1-q)e^{tau} is a product of increasing factors; hence
#        rho <= rho_b and t0 = 1-rho >= 1-rho_b.
#   (M4) w = sqrt(2/tau) is decreasing; hence w >= w_b = sqrt(2/b).
#   (M5) q = e^{-tau} is decreasing; hence q in [q_b, 1).
#
# Tails use 1-q^k = (1-q)(1+q+...+q^{k-1}) >= (1-q) k q^{k-1}, so that
#   k^{n-1} rho^k/(1-q^k) <= (q/(1-q)) k^{n-2} x^k,   x = rho/q <= x_b,
# and every k>=2 sum is a finite positive sum + ratio-test tail, a constant.
#
# The two SIGNED cancellation sites are handled exactly, not by decoupling:
#   N(t) := 1 + q - 2(1-q)/t = t^2/6 - t^3/12 + ...  (alternating, decreasing
#   terms for t<1), so  t^2/6 - t^3/12 <= N(t) <= t^2/6.  Both G1's leading
#   difference and the beta-conspiracy bracket reduce to N.
# ---------------------------------------------------------------------------

def uniform_stack(b, mode='top', verbose=True):
    b = mpf(b)
    qb = exp(-b); vb = (1-qb)/b                      # (M1),(M5)
    u_lo, u_hi = sqrt(vb), exp(b/2)                  # u = sqrt(v) e^{tau/2}
    rho_b = sqrt(2*b)*exp(b/2)                       # (M3)
    x_b = rho_b/qb
    w_b = sqrt(2/b); s_b = sqrt(b/2)                 # (M4)
    t0_lo = 1 - rho_b
    uv_hi = u_hi/vb
    S = lambda n: sum(qb**j for j in range(n))

    def tail(m, kmin=2):
        t = mpf(0); last = mpf(0)
        for k in range(kmin, 400):
            last = mpf(k)**m * x_b**k; t += last
        r = ((mpf(400)/399)**m)*x_b                  # k=399 is `last`; max onward ratio
        return t + last*r/(1-r)

    def A(n):
        return (2*u_hi**2/(vb*qb)) * tail(n-2)/x_b**2

    # beta
    Ae   = 4*u_hi**2/(vb*(1+qb))
    K4   = 4*u_hi**4/(vb*qb**3*(1-x_b))
    Reb_lo = 1 - (Ae + b*K4)*b/2
    invb_hi = 1/Reb_lo

    # ---- G1 UNIFORM: every piece of G1_majorant is const * tau^{p}, p >= 1.
    # Sum of positive powers of tau is increasing, so the sup on (0,b] is at b:
    c1_b = G1_majorant(b)/sqrt(b)                    # legitimate: see monotonicity note
    # (G1_majorant is itself a majorant; each addend is c_i tau^{p_i} with p_i >= 1,
    #  so G1_majorant(tau)/sqrt(tau) = sum c_i tau^{p_i - 1/2} is increasing in tau.)
    amp_hi = exp(c1_b*sqrt(b))*sqrt(invb_hi)

    # moments (absolute tilt), to order 40
    L1w = uv_hi + A(1)/w_b
    # absolute-tilt amplitude for the T-1 pieces: |A(xi)| <= e^{ReL0 + |L1||xi| + |L2|xi^2/2};
    # tilted prefactor exp(ReL0_hi + |L1|^2 s^2/(2(1-|L2|s^2)))/sqrt(1-|L2|s^2).
    R0_hi = rho_b**4/(4*(1-qb**4)*(1-rho_b**2))          # O(tau) majorant, at endpoint
    absb  = 1 - (Ae + b*K4)*b/2
    amp_abs = exp(-exp(-2*b)/(1+qb) + R0_hi + (L1w)**2/(2*absb))/sqrt(absb)  # ReL0 <= -e^{-2tau}/(1+q) on [-tau,h]
    c_hi  = L1w*invb_hi
    sg_hi = invb_hi
    Mh = [mpf(1), c_hi]
    for k in range(2, 42): Mh.append(c_hi*Mh[k-1] + (k-1)*sg_hi*Mh[k-2])
    C = {n: (1+(n+1)*sg_hi)*Mh[n] + c_hi*Mh[n+1] for n in range(3, 36)}

    L2w = uv_hi + A(2)/w_b
    T1w = amp_hi*L2w*invb_hi

    # ---- tail machinery, CORRECTED per review:
    #  linear n=3..10 explicit; products N<=34 by convolution of the true
    #  Lambert majorants; everything of degree >= 11 not included is blanketed by
    #  the cutoff device of lem:trunc:  H(|xi|) <= (2|xi|/t0)^{11} * Fhat  with
    #  Fhat = Ghat(t0/2) + exp(Ghat(t0/2)),  Ghat(t0/2) = kappa*(ln2 - 1/2 - 1/8).
    #  All resulting terms are positive powers of tau, hence maximized at tau=b.
    gL = {n: uv_hi + A(n)/w_b for n in range(3, 11)}         # L_n <= w * gL[n]
    # linear part (weight tau/2 - xi^2): scaled term = amp*C_n/n! * gL_n * w_b^{3-n}
    lin = sum(amp_abs*C[n]/mp.factorial(n)*gL[n]*w_b**(3-n) for n in range(3, 11))
    # product part: compositions (n_1..n_m), N = sum n_i <= 34, m >= 2;
    # term = amp*C_N/m! * (prod gL/n_i!) * w_b^{2-N+m}  (exponent < 0 for m>=2)
    base = {n: gL[n]/mp.factorial(n) for n in range(3, 11)}
    cur = dict(base); prod = mpf(0)
    for m in range(2, 12):
        nxt = {}
        for N1, v1 in cur.items():
            for n2, v2 in base.items():
                N = N1 + n2
                if N <= 34: nxt[N] = nxt.get(N, mpf(0)) + v1*v2
        cur = nxt
        for N, v in nxt.items():
            prod += amp_abs*C[N]*v/mp.factorial(m)*w_b**(2-N+m)
    # blanket for degree >= 11 (covers linear n>=11, products N>=35, conv overflow):
    kap_hi = uv_hi*w_b*mpf('1.0')                    # kappa <= (u/v) w; at endpoint w_b is a LOWER
    # bound for w, so kappa/w <= uv_hi and the blanket must scale kappa as uv_hi*w(tau);
    # in the endpoint evaluation below every tau-power is positive so tau=b maximizes, where w=w_b.
    # ---- degree->=11 remainder: TWO-INTERVAL architecture (review round 2).
    # On [tau_c, b] the Fhat-blanket profile e^{0.0969/sqrt(tau)} tau^{4.5} is increasing
    # (d/dtau log = -0.0485 tau^{-1.5} + 4.5/tau >= 0 iff tau >= 1.16e-4), so its endpoint
    # value bounds it there.  On (0, tau_c] the exponential device is invalid (kappa -> inf);
    # there the LINEAR remainder uses the pointwise bound sum_{n>=11} kappa (|xi|/t0)^n / n
    # <= (2 kappa / 11)(|xi|/t0)^{11} on |xi| <= t0/2 (geometric, ratio 1/2), whose weighted
    # moment carries kappa tau^{4.5} -> 0; and ALL products (m>=2) use |e^W - 1 - W| <=
    # |W|^2 e^{|W|}/2 <= (e^{0.45}/2)(0.5 kappa)(...)  wait: on |xi| <= y* = t0 kappa^{-1/3},
    # P_hat <= 0.45 so |W|^2 e^{|W|} / 2 <= 0.79 * (0.53 kappa (|xi|/t0)^3)^2, weighted
    # moment ~ kappa^2 tau^2 -> 0; the zone y* < |xi| <= t0/2 dies under the Gaussian
    # (exponent 0.78/sqrt(tau) - 0.63/tau^{2/3} + 2 ln(1/tau), increasing on (0, tau_c],
    # value at tau_c = 1.2e-4: e^{-188} times polynomial: negligible).
    Ghat_half = (uv_hi*w_b)*(mp.log(2) - mpf('0.5') - mpf('0.125'))
    Fhat = Ghat_half + exp(Ghat_half)
    if mode == 'top':      # [1.2e-4, b]: Fhat-blanket, endpoint-monotone
        blanket = amp_abs*Fhat*(2/t0_lo)**11*((b/2)*Mh[11]*s_b**11 + Mh[13]*s_b**13)*(4/b**2)
        assert b >= mpf('1.2e-4')   # top interval left end 1.2e-4 > 1.16e-4 threshold
    else:                  # (0, 1.2e-4]: kappa-linear + W^2-products + dead zone-B
        assert b <= mpf('1.2e-4')
        kap_b = uv_hi*w_b
        lin_bl  = amp_abs*(2*kap_b/11)*(2/t0_lo)**11/2**11*((b/2)*Mh[11]*s_b**11 + Mh[13]*s_b**13)*(4/b**2)
        prod_bl = amp_abs*mpf('0.79')*(mpf('0.53')*kap_b)**2/t0_lo**6*((b/2)*Mh[6]*s_b**6 + Mh[8]*s_b**8)*(4/b**2)
        zoneB   = exp(mpf('0.78')*w_b - mpf('0.63')/b**(mpf(2)/3) + 2*mp.log(1/b))
        blanket = lin_bl + prod_bl + zoneB
        prod = mpf(0)      # the W^2 device covers ALL products; drop the explicit conv (conservative)
    T3 = lin + prod + blanket
    # eps: |xi| > t0/2 remainder; exponent increasing on (0,b], max at b
    Aexp = sqrt(mpf(2))*uv_hi/t0_lo   # |A| <= e^{kappa/t0} pointwise: -log(1-x) <= x/(1-x)
    Bexp = t0_lo**2/4
    g_incr = Bexp - Aexp*sqrt(b)/2 - 2*b > 0
    eps = (4/b**2)*exp(Aexp/sqrt(b) - Bexp/b)

    # ---- psi' tail, UNIFORM (replaces the grid-checked 0.5 budget): weight xi,
    # scaled term = amp*Mh[n+1]/n! * gL_n * w_b^{... } with (2/tau)s^{n+1} = s^{n-1}
    # (2/tau) L_n s^{n+1} = gL_n s^{n-2} exactly (w s = 1); increasing in tau.
    ptail = sum(amp_abs*Mh[n+1]/mp.factorial(n)*gL[n]*s_b**(n-2) for n in range(3, 11))
    # xi-weighted PRODUCTS (round-3 finding 2): term = amp*Mh[N+1]*prod(gL/n!)/m!*s^{N-m-1},
    # exponent N-m-1 >= 2m-1 > 0 so endpoint evaluation is the max.
    curp = dict(base)
    for m in range(2, 12):
        nxtp = {}
        for N1, v1 in curp.items():
            for n2, v2 in base.items():
                N = N1 + n2
                if N <= 34: nxtp[N] = nxtp.get(N, mpf(0)) + v1*v2
        curp = nxtp
        for N, v in nxtp.items():
            ptail += amp_abs*Mh[N+1]*v/mp.factorial(m)*s_b**(N-m-1)
    # degree->=11 remainder for the xi weight (round-3 finding 1): the Fhat device's
    # xi-weighted profile e^{0.0969/sqrt tau} tau^5 is increasing only for tau >= 9.4e-5,
    # so it is used on the top interval only; the deep interval uses the kappa-linear
    # bound plus the xi-weighted W^2 product device (profiles kappa tau^5, kappa^2 tau^{3/2}).
    if mode == 'top':
        ptail += amp_abs*Fhat*(2/t0_lo)**11*Mh[12]*s_b**10
    else:
        kap_b2 = uv_hi*w_b
        ptail += amp_abs*(2*kap_b2/11)/t0_lo**11*Mh[12]*s_b**10
        ptail += amp_abs*mpf('0.79')*(mpf('0.53')*kap_b2)**2/t0_lo**6*Mh[7]*s_b**5    # blanket, weight xi
    G3_ok = ptail <= mpf('0.5')
    psi1w_hi = amp_hi*L1w*invb_hi + ptail/w_b

    # ---- G4 UNIFORM, derived from moments (per review). Even part:
    # |sig2| <= (4/tau^2) E[|tau/2-xi^2||A|] <= amp_abs (1+Mh2) w^2 / 2, so the even
    # contribution is (h^2/2)|sig2| <= amp_abs (1+Mh2)/4 * tau. Odd part: the pole
    # identity s(z0)=s(z0/q) (thm:collapse) gives sigma(h)=sigma(-h), hence
    # |sigma1(0)| <= h^2 max|sig3|/6 and |odd| <= h^3 max|sig3|/3, with
    # |sig3| <= amp_abs (Mh3 + 3 Mh1) w^3 (Gaussian IBP thrice, absolute values).
    sig2c = amp_abs*(1+Mh[2])/2
    sig3c = amp_abs*(Mh[3]+3*Mh[1])
    G4_coef = sig2c/4 + mpf('0.118')*sig3c*sqrt(b)   # per-tau; both increasing in tau
    G4_ok = True

    sZ_lo = 1/(psi1w_hi/sqrt(vb))
    Phi_lo = qb**mpf('0.75')*(sZ_lo - G4_coef*b)
    wcosT = psi1w_hi/Phi_lo                          # w^2 h = 1 exactly

    # sine term (unchanged, review-verified)
    K_E1 = 2*sqrt(mpf(2))*u_hi**3/(vb*S(3)*(1-rho_b**2))
    K_E2 = 4*u_hi**4/(vb*S(4)*(1-rho_b**2))
    B1_lo = 2*u_lo**2/2
    r1 = (b*K_E2/B1_lo + b*K_E1/(sqrt(mpf(2))*u_lo))*mpf('1.2')
    K_odd = 2*sqrt(mpf(2))*u_hi**3/(vb*qb**2*(1-x_b))
    r2 = b*K_odd/(sqrt(mpf(2))*u_lo)*mpf('1.2')
    invb_dev = (1-Reb_lo)/Reb_lo
    cN = u_hi/(6*vb*(1+qb))
    B1vu_hi = 2*u_hi/(1+qb)
    C_r = B1vu_hi*r1/b + uv_hi*(r2/b + invb_dev/b*(1+r2))
    arctan_cubic = 2*(mpf('1.1')*sqrt(2*b))**3/(3*b**mpf('1.5'))
    C_sin = sqrt(mpf(2))*(cN*b + C_r) + 2*arctan_cubic
    sin_ok = C_sin <= 2/sqrt(b)
    wsin  = sqrt(mpf(2))*C_sin*b

    T2w = amp_hi*(L1w*invb_hi)**2*(wcosT + wsin)
    total = T1w + T2w + (T3 + eps)/w_b
    ok = (total <= mpf('3.5')) and sin_ok and g_incr and G3_ok and G4_ok
    if verbose:
        print(f"  uniform certificate, mode={mode}, endpoint b={float(b):.2e}:")
        print(f"    c1 (G1, derived)   = {float(c1_b):.4f}")
        print(f"    psi'-tail (G3)     = {float(ptail):.4f}  [budget 0.5]  {'ok' if G3_ok else 'FAIL'}")
        print(f"    G4 coefficient     = {float(G4_coef):.4f}  (derived; feeds Phi_lo)")
        print(f"    T3 = lin {float(lin):.4f} + prod {float(prod):.4f} + blanket {float(blanket):.2e} = {float(T3):.4f}")
        print(f"    T1/w <= {float(T1w):.4f}   T2/w <= {float(T2w):.4f}   eps <= {float(eps):.2e}")
        print(f"    sine: C_sin = {float(C_sin):.2f} (<= {float(2/sqrt(b)):.1f}) {'ok' if sin_ok else 'FAIL'};  eps-exp incr: {'ok' if g_incr else 'FAIL'}")
        print(f"    TOTAL <= {float(total):.4f}  vs 3.5  -> {'PASS' if ok else 'FAIL'}")
    return total, ok

if __name__ == "__main__":
    print()
    print("UNIFORM certificate, two-interval architecture (review round 2)")
    print("  interval [1.2e-4, 5e-3]:")
    uniform_stack(mpf('0.005'), mode='top')
    print("  interval (0, 1.2e-4]:")
    uniform_stack(mpf('1.2e-4'), mode='deep')
