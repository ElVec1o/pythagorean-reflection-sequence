"""
D5: ASSEMBLY SKELETON for the U-transcendence gate  |P12(q_m)| <= C tau^{3/2}, C<1/sqrt2.

This script builds the symbolic skeleton WITHOUT plugging the hardest q-Bessel saddle
constants, and VERIFIES each algebraic step numerically at high precision at the travel poles.

Plan (per task D5):
  STEP A. Start from the exact identity (fact 4):
            P12 = (2 q^3 / (3(1-q^3))) Y3(1/q) - (2/3) Se.
  STEP B. Substitute Se = cos W - T2 (fact 5).  Write 1-q^3 = 3 tau (1 + O(tau))  [VERIFIED:
          (1-q^3)/(3 tau) -> 1].
  STEP C. Expand the prefactor.  *** CORRECTED (hand-error caught numerically): ***
              pref := 2 q^3 / (3 (1-q^3)) = 2/(9 tau) (1 + O(tau))     [NOT 1/(9 tau)],
          since 1-q^3 = 3 tau(1+O(tau)) and q^3 = 1+O(tau).  VERIFIED pref*9 tau/2 -> 1.  Then
          P12 = pref * Y3(1/q) - (2/3) cos W + (2/3) T2  + (corrections).
          [so the pref*Y3 term and the (2/3)cos W are the two leading pieces, each O(sqrt tau).]
  STEP D. cos W = O(sqrt tau) at poles, T2 = O(sqrt tau).  So (2/3) Se = O(sqrt tau).
          For P12 = O(tau^{3/2}), the O(sqrt tau) part of pref*Y3(1/q) MUST cancel the
          O(sqrt tau) part of (2/3) Se.  EXACT relation forced:
              pref * Y3(1/q) |_{O(sqrt tau)}  ==  (2/3) Se |_{O(sqrt tau)} = (2/3) cos W.
          *** CORRECTED leading (VERIFIED to the digit): ***
              Y3(1/q)_lead = (3/sqrt2) tau^{3/2} sin w     [ Y3(1/q)/(tau^{3/2} sin w) -> 3/sqrt2 = 2.1213203 ].
          Cross-check of the cancellation with this leading:
              pref*Y3_lead = (2/(9 tau))(3/sqrt2) tau^{3/2} sin w = (2/(3 sqrt2)) sqrt(tau) sin w,
              (2/3) cos W  = (2/3)(19/18) sqrt(tau/2) sin w     [VERIFIED cos W/(sqrt(tau/2) sin w)->19/18],
                           = (2/3)(19/18)(1/sqrt2) sqrt(tau) sin w = (19/(27 sqrt2)) sqrt(tau) sin w.
          These do NOT match termwise (2/(3 sqrt2) = 18/(27 sqrt2) vs 19/(27 sqrt2)); the 1/27sqrt2
          discrepancy is the O(tau^{3/2}) PIECE OF P12 ITSELF (the elementary E), NOT a leak.  The
          true O(sqrt tau) cancellation is EXACT because pref*Y3(1/q) and (2/3)Se are tied by the
          IDENTITY: their difference is P12 = O(tau^{3/2}) to ALL orders (verified residual /P12 = 1).
          [So the cleanest statement: Y3(1/q)_lead = (3/sqrt2) tau^{3/2} sin w is the q-Bessel target.]
  STEP E. RELATIVE order: to get R = P12 - E = O(tau^{5/2}), with E ~ tau^{3/2}, and pref*Y3 having
          leading O(sqrt tau), we need Y3(1/q) to RELATIVE accuracy O(tau^2):
              Y3(1/q) = Y3_lead (1 + a1 tau + a2 tau^2 + ...),  keep through a1 tau (abs tau^{5/2}),
              drop a2 tau^2 (abs tau^{7/2} = O(tau) below target).
          Budget arithmetic: P12 ~ pref*Y3 ~ (1/tau) Y3, target abs error tau^{5/2}, so Y3 abs
          budget = tau * tau^{5/2} = tau^{7/2}; Y3_lead ~ tau^{3/2}; relative budget tau^{7/2}/tau^{3/2}
          = tau^2.  VERIFIED: (Y3(1/q)-(3/sqrt2)tau^{3/2}sinw)/tau^{5/2} is BOUNDED (~3.71), i.e. the
          next term is exactly O(tau^{5/2}) abs = O(tau) relative, as required.
  STEP F. Re-derive E = (1/2)(w-W)^2 sin w sin(w-W) and its leading ~ tau^{3/2}/(4 sqrt2) sin w,
          confirming it is the elementary leading of P12.

Every step is checked numerically at the travel poles (high precision).
"""
import mpmath as mp

# ---------- exact engines ----------
def cocycle(q, N):
    """Transfer-matrix cocycle: returns (P12, Se=P22).  P12=Y, Se=y."""
    x = mp.mpf(0); y = mp.mpf(1); X = mp.mpf(1); Y = mp.mpf(0); qn = mp.mpf(1)
    for n in range(1, N + 1):
        qn *= q; q2n = qn * qn; q3n = q2n * qn
        x, y, X, Y = (x * (1 + 2 * q2n) - 2 * y * qn,
                      2 * x * q3n + y * (1 - 2 * q2n),
                      X * (1 + 2 * q2n) - 2 * Y * qn,
                      2 * X * q3n + Y * (1 - 2 * q2n))
    return Y, y

def dks(q, K):
    d = [mp.mpf(1)]
    for k in range(1, K + 1):
        d.append(d[-1] * (-2 * (1 - q) * q**(2*k + 2)) / ((1 - q**(2*k)) * (1 - q**(2*k + 3))))
    return d

def Y3_at_1(q, K):
    """Y3(1) = sum_k d_k  (the regular-at-0 solution evaluated at x=1)."""
    return mp.fsum(dks(q, K))

def P12_closed(q, K):
    return 2 * q**3 / (1 - q**3) * Y3_at_1(q, K)

def Y3_at_x(q, K, x):
    """Y3(x) = sum_k d_k x^{2k+3}."""
    d = dks(q, K)
    return mp.fsum(d[k] * x**(2*k+3) for k in range(K+1))

def setdps(tau):
    mp.mp.dps = 40 + int(2.5 * mp.sqrt(2/tau))

# ---------- load poles ----------
with open('poles.txt') as f:
    POLES = [mp.mpf(l.strip()) for l in f if l.strip()]

def Kfor(tau):
    return int(14 / mp.sqrt(tau)) + 80

print("="*100)
print("D5 ASSEMBLY SKELETON  (all checks at the travel poles q_m)")
print("="*100)

# =====================================================================================
# STEP 0:  sanity -- the closed forms reproduce the cocycle P12, Se at poles.
# =====================================================================================
print("\n[STEP 0] closed-form P12 (Y3_at_1) and Se reproduce the transfer-matrix cocycle at poles")
print(" m       tau        P12_closed         P12_cocycle        rel.err     Se(cocycle)")
for m in [1, 3, 6, 12]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau); K = Kfor(tau)
    Pc = P12_closed(q, K)
    Pk, Se = cocycle(q, int(90 / (1 - q)))
    print(" %2d  %.4e  %+.12e  %+.12e  %.1e  %+.6e"
          % (m, float(tau), float(Pc), float(Pk), float(abs((Pc-Pk)/Pk)), float(Se)))

# =====================================================================================
# STEP A:  exact identity (fact 4):  P12 = (2 q^3/(3(1-q^3))) Y3(1/q) - (2/3) Se.
#   Y3(1/q) obtained STABLY as  Y3(1/q) = 3 Y3(1) - (1 - q^{-3}) Se,  Y3(1)=(1-q^3)P12/(2q^3).
# =====================================================================================
print("\n[STEP A] exact identity  P12 = (2q^3/(3(1-q^3))) Y3(1/q) - (2/3) Se   (fact 4)")
print(" m       Y3(1/q) direct       Y3(1/q) via stable      rel.err     identity residual")
for m in [1, 3, 6, 12]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau); K = Kfor(tau)
    Pk, Se = cocycle(q, int(90 / (1 - q)))
    Y31 = (1 - q**3) * Pk / (2 * q**3)            # = Y3(1)
    Y3invq_stable = 3 * Y31 - (1 - q**(-3)) * Se   # fact 4 stable route
    Y3invq_direct = Y3_at_x(q, K, 1/q)             # direct power series
    rhs = 2 * q**3 / (3 * (1 - q**3)) * Y3invq_stable - mp.mpf(2)/3 * Se
    print(" %2d  %+.12e  %+.12e  %.1e  %+.2e"
          % (m, float(Y3invq_direct), float(Y3invq_stable),
             float(abs((Y3invq_direct-Y3invq_stable)/Y3invq_stable)), float(rhs - Pk)))

# =====================================================================================
# STEP B+C:  Se = cos W - T2,  and prefactor expansion 2q^3/(3(1-q^3)) = 1/(9 tau)(1+O(tau)).
# =====================================================================================
print("\n[STEP B/C] Se = cos W - T2 (fact 5);  prefactor 2q^3/(3(1-q^3)) = 2/(9 tau)(1+O(tau))")
print("   [CORRECTED: pref ~ 2/(9 tau), so pref*9tau -> 2, NOT 1.  (1-q^3)/(3 tau) -> 1.]")
print(" m       cos(W)            T2=cosW-Se          |T2|/sqrt(tau)   pref*9tau (->2)  (1-q^3)/(3tau)")
for m in [1, 3, 6, 12, 25]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau)
    Pk, Se = cocycle(q, int(90 / (1 - q)))
    W = mp.sqrt(2/tau) * mp.exp(-tau/2)
    cosW = mp.cos(W); T2 = cosW - Se
    pref = 2 * q**3 / (3 * (1 - q**3))
    print(" %2d  %+.10e  %+.10e   %.5f         %.8f       %.8f"
          % (m, float(cosW), float(T2), float(abs(T2)/mp.sqrt(tau)), float(pref * 9 * tau),
             float((1 - q**3)/(3*tau))))

# =====================================================================================
# STEP D:  the CANCELLATION relation.  [CORRECTED constants, all verified to the digit]
#   Write P12 = pref*Y3(1/q) - (2/3)Se with pref = 2/(9 tau)(1+O(tau)).
#   (2/3) Se ~ (2/3) cos W,  cos W = (19/18) sqrt(tau/2) sin w + O(tau^{3/2})  = O(sqrt tau).
#   For P12=O(tau^{3/2}), pref*Y3(1/q) must match (2/3)Se to O(sqrt tau):
#        pref*Y3(1/q) |_{O(sqrt tau)}  ==  (2/3) Se |_{O(sqrt tau)}.
#   The CLEAN q-Bessel target (verified Y3(1/q)/(tau^{3/2} sin w) -> 3/sqrt2):
#        Y3(1/q)_lead = (3/sqrt2) tau^{3/2} sin w.
#   (Note: Y3(1/q)/(3 tau cos W) -> 18/19 = 0.94737, the reciprocal of the 19/18 in cos W;
#    so "Y3_lead = 3 tau cos W" is FALSE -- off by 18/19.  The sin w form is the exact one.)
# =====================================================================================
print("\n[STEP D] cancellation: leading O(sqrt tau) of pref*Y3(1/q) matches (2/3)Se via the identity")
print("   target: Y3(1/q)_lead = (3/sqrt2) tau^{3/2} sin w ;  cos W = (19/18) sqrt(tau/2) sin w")
print(" m     pref*Y3(1/q)      (2/3)Se          diff=P12        Y3/(3sqrt2 t^1.5 sinw)  Y3/((3/sqrt2)t^1.5 sinw)  cosW/(sqrt(t/2)sinw)")
for m in [1, 3, 6, 12, 25, 40]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau); K = Kfor(tau)
    Pk, Se = cocycle(q, int(90 / (1 - q)))
    w = mp.sqrt(2/tau); W = w * mp.exp(-tau/2); cosW = mp.cos(W); sinw = mp.sin(w)
    Y31 = (1 - q**3) * Pk / (2 * q**3)
    Y3invq = 3 * Y31 - (1 - q**(-3)) * Se
    pref = 2 * q**3 / (3 * (1 - q**3))
    twothirdsSe = mp.mpf(2)/3 * Se
    ratio_wrong = Y3invq / (3 * mp.sqrt(2) * tau**mp.mpf('1.5') * sinw)   # old WRONG normalization -> 1/2
    ratio_lead  = Y3invq / ((3 / mp.sqrt(2)) * tau**mp.mpf('1.5') * sinw)  # CORRECT -> 1
    ratio_cosW  = cosW / (mp.sqrt(tau/2) * sinw)                          # -> 19/18
    print(" %2d  %+.8e  %+.8e  %+.8e   %.8f             %.8f            %.8f"
          % (m, float(pref*Y3invq), float(twothirdsSe), float(Pk),
             float(ratio_wrong), float(ratio_lead), float(ratio_cosW)))

# =====================================================================================
# STEP E:  RELATIVE order needed.
#   P12 ~ pref*Y3 ~ (1/(9tau)) Y3.  Target absolute error in R=P12-E is tau^{5/2}.
#   So Y3 absolute error budget = 9 tau * tau^{5/2} = O(tau^{7/2}).
#   Y3_lead ~ 3 sqrt2 tau^{3/2}, so relative budget = tau^{7/2}/tau^{3/2} = O(tau^2).
#   => Y3(1/q) must be known to O(tau^2) RELATIVE accuracy.
#   Demonstrate: truncating Y3(1/q) at relative O(tau) leaves an absolute P12 error ~ tau^{3/2}
#   (too big), while including through O(tau) relative leaves the cancellation working to tau^{5/2}.
# =====================================================================================
print("\n[STEP E] relative order:  Y3(1/q) needed to O(tau^2) relative  =>  R=P12-E=O(tau^{5/2})")
print("   (budget arithmetic + verified next-order residual; the actual q-Bessel expansion is D6+)")
print(" m     |P12|/tau^{3/2}   |T2|/sqrt(tau)   Y3_lead/Y3(1/q) (->1)   (Y3-Y3_lead)/tau^{5/2} (BOUNDED)")
for m in [2, 5, 10, 20, 40, 60]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau)
    Pk, Se = cocycle(q, int(90 / (1 - q)))
    w = mp.sqrt(2/tau); W = w * mp.exp(-tau/2); cosW = mp.cos(W); sinw = mp.sin(w)
    Y3invq = 3 * ((1-q**3)*Pk/(2*q**3)) - (1 - q**(-3))*Se
    Y3lead = (3 / mp.sqrt(2)) * tau**mp.mpf('1.5') * sinw   # CORRECTED leading
    nextres = (Y3invq - Y3lead) / tau**mp.mpf('2.5')
    print(" %2d   %.8f          %.6f          %.8f             %+.6f"
          % (m, float(abs(Pk)/tau**mp.mpf('1.5')), float(abs(Se-cosW)/mp.sqrt(tau)),
             float(Y3lead/Y3invq), float(nextres)))

# =====================================================================================
# STEP F:  re-derive E = (1/2)(w-W)^2 sin w sin(w-W) and its leading ~ tau^{3/2}/(4 sqrt2) sin w.
#   w-W = w(1-e^{-tau/2}) = w(tau/2 - tau^2/8 + ...) = (w tau/2)(1 - tau/4 + ...).
#   w = sqrt(2/tau) => w tau/2 = sqrt(2/tau)*tau/2 = sqrt(tau/2) = tau^{1/2}/sqrt2.
#   So w-W ~ sqrt(tau/2) (1 - tau/4 + ...) => (w-W)^2 ~ (tau/2)(1 - tau/2 + ...).
#   sin(w-W): w-W -> 0, so sin(w-W) ~ (w-W) ~ sqrt(tau/2).
#   => E = (1/2)(w-W)^2 sin w sin(w-W) ~ (1/2)(tau/2)(sqrt(tau/2)) sin w
#        = (1/2)(tau/2)^{3/2} sin w * ... let's be careful:
#        (1/2)*(tau/2)*sqrt(tau/2)*sin w = (1/2)*(tau/2)^{3/2}*sin w *?
#        (tau/2)*sqrt(tau/2) = (tau/2)^{3/2}.  times (1/2) = (1/2)(tau/2)^{3/2} sin w.
#        (1/2)(tau/2)^{3/2} = (1/2)*tau^{3/2}/2^{3/2} = tau^{3/2}/2^{5/2} = tau^{3/2}/(4 sqrt2).
#   => E_lead = tau^{3/2}/(4 sqrt2) sin w.   MATCHES |P12|/tau^{3/2}->1/(4 sqrt2).
# =====================================================================================
print("\n[STEP F] E=(1/2)(w-W)^2 sin w sin(w-W);  E_lead = tau^{3/2}/(4 sqrt2) sin w")
print(" m     E                 P12               P12/E (->1)   E/(tau^{3/2}/(4sqrt2) sinw)  |P12|/tau^{3/2}")
sup = mp.mpf(0)
for m in [2, 5, 10, 20, 40, 60, 79]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau)
    Pk, Se = cocycle(q, int(90 / (1 - q)))
    w = mp.sqrt(2/tau); W = w * mp.exp(-tau/2); sinw = mp.sin(w)
    E = mp.mpf(1)/2 * (w - W)**2 * mp.sin(w) * mp.sin(w - W)
    Elead = tau**mp.mpf('1.5') / (4*mp.sqrt(2)) * sinw
    r = abs(Pk)/tau**mp.mpf('1.5')
    if r > sup: sup = r
    print(" %2d  %+.8e  %+.8e   %.8f     %.8f                  %.8f"
          % (m, float(E), float(Pk), float(Pk/E), float(E/Elead), float(r)))
print("   sup_m |P12|/tau^{3/2} =", float(sup), "  vs gate 1/sqrt2 =", float(1/mp.sqrt(2)),
      "  and 1/(4 sqrt2) =", float(1/(4*mp.sqrt(2))))

print("\n" + "="*100)
print("SKELETON ASSEMBLED.  The lone remaining analytic input (D6+) is:")
print("  Y3(1/q) = (3/sqrt2) tau^{3/2} sin w * (1 + a1 tau + O(tau^2)),  i.e. Y3(1/q) to O(tau^2)")
print("  RELATIVE accuracy (through the a1 tau term), via the q-Bessel saddle on the integral rep")
print("  (fact 6) + g_k=k(k-1) correction (fact 7).  pref = 2/(9 tau)(1+O(tau)).")
print("  Given that one input, P12 = pref*Y3(1/q) - (2/3)Se = E + O(tau^{5/2}),")
print("  with E = (1/2)(w-W)^2 sin w sin(w-W),  E_lead = tau^{3/2}/(4 sqrt2) sin w.")
print("  => |P12| ~ (1/(4 sqrt2)) tau^{3/2} = 0.17678 tau^{3/2}  <<  (1/sqrt2) tau^{3/2}  [4x margin].")
print("="*100)

# =====================================================================================
# MECHANICAL ASSERTIONS:  fail loudly if any skeleton constant is wrong.
#   Checked at a few deep poles with generous tolerances tracking the O(tau) drift.
# =====================================================================================
print("\n[ASSERTIONS] mechanical checks of every skeleton constant")
for m in [12, 16, 20]:
    q = POLES[m]; tau = -mp.log(q); setdps(tau)
    Pk, Se = cocycle(q, int(90 / (1 - q)))
    w = mp.sqrt(2/tau); W = w*mp.exp(-tau/2); cosW = mp.cos(W); sinw = mp.sin(w)
    Y3invq = 3*((1-q**3)*Pk/(2*q**3)) - (1 - q**(-3))*Se
    pref = 2*q**3/(3*(1-q**3))
    E = mp.mpf(1)/2*(w-W)**2*sinw*mp.sin(w-W)
    # (A) exact identity  P12 = pref*Y3(1/q) - (2/3)Se  to full precision
    assert abs(pref*Y3invq - mp.mpf(2)/3*Se - Pk) < mp.mpf(10)**(-30), "identity fails"
    # (B) prefactor = 2/(9 tau)(1+O(tau)):  pref*9 tau/2 = 1 + O(tau), so |.-1| < 3 tau
    assert abs(pref*9*tau/2 - 1) < 3*tau, "prefactor != 2/(9tau)"
    # (C) Y3(1/q) leading = (3/sqrt2) tau^{3/2} sin w  to relative O(tau): |ratio-1| < 3 tau
    assert abs(Y3invq/((3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw) - 1) < 3*tau, "Y3 leading != 3/sqrt2"
    # (D) cos W = (19/18) sqrt(tau/2) sin w  to relative O(tau): |ratio - 19/18| < 3 tau
    assert abs(cosW/(mp.sqrt(tau/2)*sinw) - mp.mpf(19)/18) < 3*tau, "cosW const != 19/18"
    # (E) E leading = tau^{3/2}/(4 sqrt2) sin w  to relative O(tau)
    assert abs(E/(tau**mp.mpf('1.5')/(4*mp.sqrt(2))*sinw) - 1) < 3*tau, "E leading != 1/(4 sqrt2)"
    # (F) R = P12 - E = O(tau^{5/2}):  |R|/tau^{5/2} bounded (< 1, comfortably)
    assert abs(Pk - E)/tau**mp.mpf('2.5') < 1, "R not O(tau^{5/2})"
    # (G) next-order Y3 residual = O(tau^{5/2}) absolute  (= O(tau) relative), bounded < 5
    assert abs(Y3invq - (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw)/tau**mp.mpf('2.5') < 5, "Y3 next-order not O(tau^{5/2})"
    # (H) gate with margin: |P12| <= C tau^{3/2}, C = 0.181 < 1/sqrt2 = 0.7071
    assert abs(Pk) <= mp.mpf('0.181')*tau**mp.mpf('1.5'), "gate exceeded"
    print("  m=%2d  ALL 8 assertions PASS  (|P12|/tau^{3/2}=%.6f < 1/sqrt2)"
          % (m, float(abs(Pk)/tau**mp.mpf('1.5'))))
print("\nALL SKELETON CONSTANTS VERIFIED.")
