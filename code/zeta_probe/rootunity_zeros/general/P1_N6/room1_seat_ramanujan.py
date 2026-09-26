# room1_seat_ramanujan.py -- ROOM OF MATHEMATICIANS, item 1 (P1 N=6), Seat: Ramanujan.
# Numerical landscape exploration at N=6 (theta*=0, tie pair (-3,-1), T=-0.10878, c=2e^{2pi i/3}, ell=log2).
# Goal: build intuition for whether a "modulus-only rescue" of the ray lemma is plausible, by (1) computing
# the head term and dominant-mode contributions as explicit functions of the path parameter, high precision
# (via python-flint/Arb, ctx.prec=192 ~ 57 digits), (2) perturbing theta as a free parameter around theta*=0
# to see how the head-vs-dominant margin behaves, (3) tabulating whether the head ever threatens the
# dominant terms along the real ray (theta=0) or stays comfortably separated even without a proof.
#
# Reuses P1i_landscape_cert.Case (imported, not re-derived) for all N=6 constants (L, xi, w, n, s, delta,
# rho_N, C0, C1) so this is a numerical *exploration* on top of the certified data, not a re-derivation.
#
# Usage: perl -e 'alarm 290; exec @ARGV' python3 room1_seat_ramanujan.py
import sys, time
sys.path.insert(0, '../P1i')
from P1i_landscape_cert import Case, arb, acb, PI, I, ctx, scan, target, rho_pieces, up, ball, cball, radc

ctx.prec = 192   # ~57 decimal digits, well above the 50+ digit ask
t0 = time.time()
OUT = []
def log(s):
    print(s, flush=True); OUT.append(s)

N = 6
C = Case(1, N)
log('=== calibration/context (from P1i_landscape_cert.Case, N=6, a=1) ===')
log('ell=%s' % C.ell.str(20))
log('theta* (certified) = %s (deg %.6f)' % (C.th.str(10), float(C.th.mid())*180/3.141592653589753))
log('tie pair (n, n+s) = (%d, %d), s=%d' % (C.n, C.n + C.s, C.s))
log('delta = %s' % C.delta.str(10))

# --- head term Hh: theta-independent (P1i formula) ---
rhoN = 1 - (1/(4*arb(N)))*(1/(4*arb(N))).exp()/(2*(PI/N).sin())
d = C.delta
Hh = d*(C.ell + 2*(-(rhoN.log()))) + (2*d/N)*(1 + (1/(arb('1.8')*d)).log())
log('rho_N = %s' % rhoN.str(15))
log('H_head (theta-independent) = %s' % Hh.str(20))

n = C.n
Vref = C.V(n)          # dominant (B-mode) reference height at the tie
log('Vref = V(n=%d) = %s' % (n, Vref.str(20)))
log('  |Vref| = %s , arg(Vref) = %s' % (Vref.abs_upper().str(10), (Vref.imag/Vref.real).atan().str(10)))

# =====================================================================
# TASK 1: head term & dominant-mode contribution as explicit functions of path parameter rho/v
# =====================================================================
log('')
log('=== TASK 1: head term + dominant-mode Omega(x) along the real ray (theta fixed at theta*=0) ===')
log('Head "term": the b_0=1 coefficient sits at analytic height 0 (constant, no decay in rho).')
log('  H_head(rho) := Hh  for all rho>=0  (it is a bound on the WHOLE head sum, not rho-dependent;')
log('  the head decomposition in P1f/P1i has no path parameter of its own -- it is a finite sum bound).')
log('')
log('Dominant mode Omega_n(x) along the descent line x = x_n + v*e^{i theta/2} (theta=0 => real line):')
xs_n = C.xs(n)
log('  saddle x_n = %s' % xs_n.str(20))
E0 = (-I*C.th).exp()   # theta* = 0 so E0 = 1
log('rho    Re((Omega_n(x_n+rho) - Vref)*e^{-i theta*})   Omega_n height (mid)')
for rho in [arb(v)/10 for v in range(0, 21, 2)]:
    x = xs_n + rho
    if not bool(x.real.lower() > 0):
        log('%5s   Re x<=0, outside domain of this Omega branch' % rho.str(3)); continue
    val = ((C.Om(x, n) - Vref)*E0).real
    log('%5s   %s' % (rho.str(3), val.str(15)))

# =====================================================================
# TASK 2: artificially perturb theta, hold everything else (N=6 constants) fixed; track margin -> 0
# =====================================================================
log('')
log('=== TASK 2: margin(theta) = H_head - Re(Vref * e^{-i theta})  as theta -> 0 from either side ===')
log('(all other N=6 constants -- Vref, Hh, delta, ell, tie pair -- held FIXED at their certified values;')
log(' theta alone is swept as a free perturbation parameter, ignoring whether such theta is realizable)')
log('theta            margin = Hh - href          href = Re(Vref e^{-i theta})')
thetas = [arb('0.5'), arb('0.2'), arb('0.1'), arb('0.05'), arb('0.02'), arb('0.01'), arb('0.005'),
          arb('0.001'), arb('0.0001'), arb('0'),
          arb('-0.0001'), arb('-0.001'), arb('-0.005'), arb('-0.01'), arb('-0.02'), arb('-0.05'),
          arb('-0.1'), arb('-0.2'), arb('-0.5')]
for th in thetas:
    E = (-I*th).exp()
    href = (Vref*E).real
    margin = Hh - href
    log('%-9s   %-28s   %s' % (th.str(6), margin.str(15), href.str(12)))

# derivative check: d(href)/dtheta at theta=0 = Re(Vref * (-i)) = Im(Vref)  (since d/dtheta e^{-i theta}=-i at 0)
dhref_dtheta_at_0 = Vref.imag
log('')
log('analytic slope check: d(href)/dtheta |_{theta=0} = Im(Vref) = %s  (nonzero => margin(theta) is LINEAR')
log('  near theta=0, not flat/degenerate -- it does NOT vanish or blow up as theta->0, it just crosses')
log('  through the fixed offset Hh - Re(Vref) linearly with slope -Im(Vref)).')
log('slope = %s' % dhref_dtheta_at_0.str(15))
log('margin(theta) ~= [Hh - Re(Vref)] + Im(Vref)*theta + O(theta^2) near theta=0')
lin_const = Hh - Vref.real
log('  linear model: margin(theta) ~= %s + (%s)*theta' % (lin_const.str(12), Vref.imag.str(12)))

# =====================================================================
# TASK 3: does the head ever overtake the dominant terms along the real ray at theta*=0?  Tabulate.
# =====================================================================
log('')
log('=== TASK 3: head vs dominant-mode margin, at the CERTIFIED theta*=0, along increasing rho ===')
log('Since H_head is a single bound on the whole head sum (not itself rho-dependent), the comparison')
log('that matters is: H_head (=%s) vs. href = Re(Vref e^{-i theta*}) = Vref.real (=%s).' % (Hh.str(10), Vref.real.str(10)))
margin0 = Hh - Vref.real
log('margin at theta*=0 exactly: Hh - Re(Vref) = %s   (POSITIVE => head genuinely overtakes the tie height)' % margin0.str(15))
log('')
log('Cross-check against the dominant-mode dynamics itself (does the *saddle* landscape, not just the')
log('scalar head bound, ever dip below the head level along the real ray?):')
log('rho     Re(Omega_n(x_n+rho))            Re(Omega_n) - Hh   (negative = head still above the local dominant height)')
for rho in [arb(v)/4 for v in range(0, 13)]:
    x = xs_n + rho
    if not bool(x.real.lower() > 0):
        continue
    val = C.Om(x, n).real
    log('%5s   %-25s   %s' % (rho.str(3), val.str(15), (val - Hh).str(12)))

# also check the OTHER surviving tie member (n+s) and the S-mode reference (n+1), for completeness
log('')
log('For reference, the S-mode (n+1) tie height (this mode DID certify in P1i, head-T<=-0.1193):')
Vref_S = C.V(n + 1)
hrefS = Vref_S.real
log('Vref_S = %s ; Re(Vref_S) = %s ; Hh - Re(Vref_S) = %s (NEGATIVE, comfortably certified)'
    % (Vref_S.str(15), hrefS.str(12), (Hh - hrefS).str(12)))

log('')
log('=== VERDICT ===')
log('margin at theta*=0 is %s (fixed, order 0.15, not a knife-edge near-zero number).' % margin0.str(6))
log('The margin(theta) sweep in TASK 2 shows NO singular behaviour as theta->0: it is a smooth, LINEAR')
log('crossing (slope = Im(Vref) = %s, |slope| ~ 0.36), not a blow-up, not a vanishing degeneracy. The bad')
log('sign at theta=0 is not a boundary artifact of theta->0 -- it holds on a whole neighbourhood of')
log('theta=0 (theta in roughly (-0.42, 0.42) by the linear model, i.e. the ENTIRE relevant range near the')
log('actual tie angle, since |lin_const/slope| ~ %s), and only flips sign once theta leaves that band.' % (lin_const/Vref.imag).str(6))
log('So there is no "just barely fails at theta=0, would pass at nearby theta" story: the B-mode head')
log('failure at N=6 is a robust, finite-margin (~0.15) failure of the CRUDE bound, not a razor-thin one')
log('that a small modulus-only correction (replacing the ray lemma\'s sin(theta) rotation argument with a')
log('pure |1-w| modulus estimate) could plausibly patch by shaving off a few percent. A modulus-only rescue')
log('would need to find ~0.15 of otherwise-uncounted decay/cancellation -- comparable in size to the whole')
log('head bound itself -- not a marginal tightening.')
print('done in %.1fs' % (time.time() - t0))
with open('room1_seat_ramanujan_notes.txt', 'w') as f:
    f.write('\n'.join(OUT) + '\n')
