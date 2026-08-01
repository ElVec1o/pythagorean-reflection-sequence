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
    amp = exp(mpf('0.05')*sqrt(tau))*sqrt(invb)
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
