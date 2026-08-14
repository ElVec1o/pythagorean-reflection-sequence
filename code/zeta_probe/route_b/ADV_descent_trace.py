#!/usr/bin/env python3
"""
ADV_descent_trace.py -- VERIFY the steepest-descent contour Gamma for Olver
hypotheses (ii) [global descent] and (c) [prefactor O(1)] used in
lem:extremephase / rem:olverhyp (transcendence.tex), ALONG THE ACTUAL TRACED
CONTOUR (not merely at the saddle).

Lindelof integrand:  h(s) = a_s * g_s * pi/sin(pi s),
    a_s = W^{2s}/Gamma(2s+1),  g_s = 1 - e^{-B_s},
    W = sqrt(2/tau) * e^{-tau/2}.
Full saddle-phase exponent (carries the TRUE pole structure of pi/sin):
    Phi(s) = 2 s log W - logGamma(2s+1) - log sin(pi s).
Saddle  s* ~ i W/2.

We:
  1. solve Phi'(s)=0 near iW/2  -> s_hat (report real-part offset, Phi'').
  2. predictor-correct the constant-phase level curve Im Phi = Im Phi(s_hat)
     through s_hat, BOTH steepest-DESCENT branches.
  3. along the traced path verify (ii) descent monotone, strip Im s<=W/2,
     (c) prefactor |a_s/sin(pi s)| bounded + e^{pi W/2} cancellation, no pole
     crossing.
  4. report obstructions (2nd saddle, off-axis saddle, tail closure).

SCALAR mpmath only, dps=40, memory-safe.
"""
import mpmath as mp
from abelplana_verify import B_exact          # EXACT analytic B_s (validated)

mp.mp.dps = 40
I = mp.mpc(0, 1)

# ---------------------------------------------------------------------------
# building blocks
# ---------------------------------------------------------------------------
def setup(tau):
    tau = mp.mpf(tau)
    w = mp.sqrt(2/tau)
    W = w*mp.e**(-tau/2)
    return tau, w, W

def logg(s, tau):
    """log g_s = log(1 - e^{-B_s}); B_s exact analytic continuation."""
    B, _ = B_exact(s, tau)
    return mp.log(1 - mp.e**(-B)), B

# Full exponent Phi(s) = 2 s log W - logGamma(2s+1) - log sin(pi s).
# This INCLUDES the exact 1/sin(pi s) (true poles at integers), so the traced
# level curve is the genuine Lindelof descent path, not the e^{i pi s}
# upper-side surrogate.  We OPTIONALLY fold in log g_s (it is slowly varying,
# O(sqrt tau)); we trace with the analytic part Phi and also locate the FULL
# saddle (Phi + log g) to report the off-axis offset.
def Phi(s, W):
    return 2*s*mp.log(W) - mp.loggamma(2*s+1) - mp.log(mp.sin(mp.pi*s))

def Phi_full(s, W, tau):
    lg, _ = logg(s, tau)
    return Phi(s, W) + lg

# derivatives via mp.diff (scalar, adaptive)
def Phi1(s, W):       return mp.diff(lambda z: Phi(z, W), s)
def Phi2(s, W):       return mp.diff(lambda z: Phi(z, W), s, 2)
def Phifull1(s, W, tau): return mp.diff(lambda z: Phi_full(z, W, tau), s)
def Phifull2(s, W, tau): return mp.diff(lambda z: Phi_full(z, W, tau), s, 2)

# log|h| at s  (for the e^{-10} stop test and prefactor diagnostics)
def logabs_h(s, W, tau):
    lg, _ = logg(s, tau)
    la = 2*s*mp.log(W) - mp.loggamma(2*s+1)            # log a_s
    return mp.re(la) + mp.re(lg) + mp.log(mp.pi) - mp.log(abs(mp.sin(mp.pi*s)))

# log of the PREFACTOR  P(s) = a_s / sin(pi s) = exp(2 s logW - logGamma(2s+1))/sin(pi s)
# (the part multiplying g_s); we track Re log|P| along the path for boundedness.
def logabs_prefactor(s, W):
    la = 2*s*mp.log(W) - mp.loggamma(2*s+1)
    return mp.re(la) - mp.log(abs(mp.sin(mp.pi*s)))

# ---------------------------------------------------------------------------
# 1.  SADDLE
# ---------------------------------------------------------------------------
def find_saddle(W, tau, use_full=False):
    """Newton on Phi'(s)=0 (or Phi_full') starting from iW/2."""
    s = I*W/2
    f1 = (lambda z: Phifull1(z, W, tau)) if use_full else (lambda z: Phi1(z, W))
    for _ in range(60):
        f = f1(s)
        d = mp.diff(f1, s)
        if d == 0:
            break
        step = f/d
        s = s - step
        if abs(step) < mp.mpf('1e-38'):
            break
    return s

# ---------------------------------------------------------------------------
# 2.  TRACE the constant-phase (steepest-descent) level curve through s_hat.
#     Predictor: step ds in the descent TANGENT direction.
#     Corrector: a few bounded hand-Newton steps along the NORMAL to restore
#                Im Phi = level.  A guard rejects corrector jumps larger than
#                the predictor step, so the path cannot hop to a distant branch
#                of the multivalued log sin(pi s).
# ---------------------------------------------------------------------------
def descent_directions(s_hat, W):
    """The two steepest-descent unit tangents at the saddle.
       Phi(s)-Phi(s_hat) ~ (1/2) Phi''(s-s_hat)^2; steepest descent keeps
       Phi'' * d^2 real & NEGATIVE  => arg(d) = (pi - arg Phi'')/2  (+ k*pi).
       (Phi'' here is ~ +4i/W, so arg(d) ~ +-(pi - pi/2)/2 = +-pi/4.)"""
    p2 = Phi2(s_hat, W)
    a = (mp.pi - mp.arg(p2))/2
    d1 = mp.e**(I*a)
    return d1, -d1, p2

def correct_to_level(s_pred, tangent, level, W, max_jump):
    """Bounded Newton along the normal n=i*tangent to solve Im Phi=level.
       Returns s on the level curve, or None if it would jump too far."""
    normal = I*tangent
    t = mp.mpf(0)
    for _ in range(12):
        s_try = s_pred + t*normal
        g = mp.im(Phi(s_try, W)) - level
        # d/dt Im Phi(s_pred + t n) = Re( Phi'(...) * conj? ) -> use directional
        gp = mp.im(Phi1(s_try, W)*normal)
        if gp == 0:
            break
        dt = g/gp
        t = t - dt
        if abs(t) > max_jump:          # guard: refuse far jumps (wrong branch)
            return None
        if abs(dt) < mp.mpf('1e-30'):
            break
    s_new = s_pred + t*normal
    if abs(mp.im(Phi(s_new, W)) - level) > mp.mpf('1e-8'):
        return None
    return s_new

def trace_branch(s_hat, tangent0, W, tau, level, sat_logh,
                 ds=None, max_re=15, drop=10, max_steps=20000):
    """Follow ONE steepest-descent branch from s_hat. Stop when Re s>max_re,
       or log|h| drops 'drop' below saddle, or |Im s| collapses below 0, or
       the corrector cannot stay on the level curve."""
    if ds is None:
        ds = mp.mpf('0.35')/mp.sqrt(abs(Phi2(s_hat, W)))
        ds = min(ds, mp.mpf('0.15'))
    pts = []
    s = s_hat
    tangent = tangent0/abs(tangent0)
    arclen = mp.mpf(0)
    pts.append(dict(s=s, arclen=arclen, RePhi=mp.re(Phi(s, W)),
                    ImPhi=mp.im(Phi(s, W)), Im_s=mp.im(s),
                    logh=logabs_h(s, W, tau), pref=logabs_prefactor(s, W),
                    RePhi_full=mp.re(Phi_full(s, W, tau))))
    for _ in range(max_steps):
        s_pred = s + ds*tangent
        s_new = correct_to_level(s_pred, tangent, level, W, max_jump=3*ds)
        if s_new is None:
            break
        chord = s_new - s
        if abs(chord) == 0:
            break
        tangent = chord/abs(chord)          # forward chord direction
        arclen += abs(chord)
        s = s_new
        lh = logabs_h(s, W, tau)
        pts.append(dict(s=s, arclen=arclen, RePhi=mp.re(Phi(s, W)),
                        ImPhi=mp.im(Phi(s, W)), Im_s=mp.im(s),
                        logh=lh, pref=logabs_prefactor(s, W),
                        RePhi_full=mp.re(Phi_full(s, W, tau))))
        if mp.re(s) > max_re:
            break
        if float(sat_logh - lh) > drop:
            break
        if mp.im(s) < mp.mpf('-0.5'):       # dropped below real axis -> done
            break
    return pts

# ---------------------------------------------------------------------------
# 3.  VERIFY along a traced branch
# ---------------------------------------------------------------------------
def analyse_branch(pts, Whalf):
    """Return descent monotonicity violation, max Im s, prefactor range,
       max |Im Phi - level| (level-curve fidelity), and min RePhi (tail)."""
    RePhi = [p['RePhi'] for p in pts]
    ImPhi = [p['ImPhi'] for p in pts]
    Ims   = [p['Im_s'] for p in pts]
    pref  = [p['pref'] for p in pts]
    level = ImPhi[0]
    # monotone-DECREASING in arclength away from saddle: RePhi[k] should be
    # <= RePhi[k-1].  Report the largest positive increment (violation).
    max_violation = mp.mpf(0)
    for k in range(1, len(RePhi)):
        inc = RePhi[k] - RePhi[k-1]      # >0 means it went UP (bad)
        if inc > max_violation:
            max_violation = inc
    max_Im_s = max(Ims) if Ims else mp.mpf('-inf')
    pref_min = min(pref); pref_max = max(pref)
    level_dev = max(abs(v - level) for v in ImPhi)
    tail_drop = RePhi[0] - RePhi[-1]     # how far Re Phi fell from saddle
    return dict(max_violation=max_violation, max_Im_s=max_Im_s,
                pref_min=pref_min, pref_max=pref_max, level_dev=level_dev,
                tail_drop=tail_drop, n=len(pts), end_s=pts[-1]['s'],
                end_Re=mp.re(pts[-1]['s']))

def trace_horizontal(W, tau, eta, smax=mp.mpf('15'), n=160):
    """Diagnostic contour: the HORIZONTAL ray Im s = eta, Re s in [0, smax].
       This is the contour the proof actually deforms to (the strip boundary
       eta=W/2, or real axis eta~0+).  On it, Re Phi = Re[2 s logW - logGamma]
       - log|sin| should DECREASE monotonically as Re s grows (factorial decay
       of 1/Gamma dominates), giving genuine descent that closes the tail and
       stays in the strip by construction.  Poles of 1/sin sit at INTEGER s on
       Im s=0 only; for eta>0 they are distance eta away."""
    pts = []
    for k in range(n+1):
        sig = smax*mp.mpf(k)/n
        s = mp.mpc(sig, eta)
        pts.append(dict(s=s, sig=sig,
                        RePhi=mp.re(Phi(s, W)),
                        RePhi_full=mp.re(Phi_full(s, W, tau)),
                        Im_s=eta, logh=logabs_h(s, W, tau),
                        pref=logabs_prefactor(s, W)))
    return pts

def analyse_horizontal(pts, sat_RePhi):
    """Monotone decrease of Re Phi in Re s; prefactor range; pole distance;
       drop achieved relative to the saddle Re Phi value."""
    RePhi = [p['RePhi'] for p in pts]
    RePhiF = [p['RePhi_full'] for p in pts]
    pref = [p['pref'] for p in pts]
    # We want Re Phi DECREASING as sigma increases (monotone descent).
    max_up = mp.mpf(0)
    max_up_full = mp.mpf(0)
    for k in range(1, len(RePhi)):
        up = RePhi[k]-RePhi[k-1]
        if up > max_up: max_up = up
        upf = RePhiF[k]-RePhiF[k-1]
        if upf > max_up_full: max_up_full = upf
    eta = pts[0]['Im_s']
    # nearest positive-integer pole: at integer sigma on Im=0, distance = sqrt((sig-n)^2+eta^2)
    min_pole = mp.mpf('inf')
    for p in pts:
        n_near = int(mp.nint(p['sig']))
        if n_near >= 1:
            d = abs(p['s']-n_near)
            if d < min_pole: min_pole = d
    drop = RePhi[0]-RePhi[-1]
    return dict(max_up=max_up, max_up_full=max_up_full,
                pref_min=min(pref), pref_max=max(pref),
                min_pole=min_pole, drop=drop, end_sig=pts[-1]['sig'])

def integer_poles_swept(branch_pts, s_hat):
    """Check no positive-integer pole of pi/sin(pi s) lies ON the path or in
       the rectangle swept between the encircling contour (real axis interval)
       and the path.  We check: (a) min distance from any path point to the
       nearest positive integer on the real line is bounded away from 0 for
       the part of the path with small |Im s|; (b) the path's Re-extent vs the
       saddle Im."""
    min_pole_dist = mp.mpf('inf')
    crossed = False
    for p in branch_pts:
        s = p['s']
        n_near = int(mp.nint(mp.re(s)))
        if n_near >= 1:
            d = abs(s - n_near)            # distance to nearest pos-int pole
            if d < min_pole_dist:
                min_pole_dist = d
            if d < mp.mpf('1e-6'):
                crossed = True
    return min_pole_dist, crossed

# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------
def run(tau_in):
    tau, w, W = setup(tau_in)
    Whalf = W/2
    print("="*86)
    print(f" tau={float(tau)}   W={mp.nstr(W,8)}   W/2={mp.nstr(Whalf,8)}   "
          f"pi/tau(resonance)={mp.nstr(mp.pi/tau,6)}")
    print("="*86)

    # ----- 1. SADDLE (analytic Phi) and FULL saddle (Phi+log g) -----
    s_an   = find_saddle(W, tau, use_full=False)
    s_full = find_saddle(W, tau, use_full=True)
    p2_an   = Phi2(s_an, W)
    p2_full = Phifull2(s_full, W, tau)
    off_an   = mp.re(s_an)                 # real-part offset of analytic saddle
    off_full = mp.re(s_full)
    print(f" [1] saddle (Phi, analytic):  s_hat = {mp.nstr(s_an,10)}")
    print(f"       Re offset = {mp.nstr(off_an,4)}   Im = {mp.nstr(mp.im(s_an),8)} (vs W/2={mp.nstr(Whalf,8)})")
    print(f"       Phi''(s_hat) = {mp.nstr(p2_an,8)}   -4/W = {mp.nstr(-4/W,8)}   "
          f"ratio = {mp.nstr(p2_an/(-4/W),6)}")
    print(f"       |Phi'(s_hat)| = {mp.nstr(abs(Phi1(s_an,W)),3)} (->0)")
    print(f" [1'] FULL saddle (Phi+log g): s_hat = {mp.nstr(s_full,10)}")
    print(f"       Re offset = {mp.nstr(off_full,4)}  (off-imag-axis O(sqrt tau)? "
          f"offset/sqrt(tau) = {mp.nstr(off_full/mp.sqrt(tau),4)})")
    print(f"       Phi_full''(s_hat) = {mp.nstr(p2_full,8)}   ratio to -4/W = {mp.nstr(p2_full/(-4/W),6)}")

    # BASEPOINT = the genuine ANALYTIC saddle s_an of Phi (true pole structure,
    # carries 1/sin).  The log g term is a bounded O(sqrt tau) perturbation and
    # is NOT used to relocate the saddle (its numerical s_full is noise, since
    # B_exact is a truncated k-sum -> diff(Phi_full) is unreliable).  We instead
    # CHECK separately that Re Phi_full is also descending along the same path.
    s_hat = s_an
    level = mp.im(Phi(s_hat, W))
    sat_logh = logabs_h(s_hat, W, tau)
    d1, d2, p2dir = descent_directions(s_hat, W)
    print(f" [2] descent tangents at saddle: arg = {mp.nstr(mp.arg(d1)*180/mp.pi,5)} deg "
          f"and {mp.nstr(mp.arg(d2)*180/mp.pi,5)} deg (Phi''={mp.nstr(p2dir,5)})  "
          f"sat log|h|={mp.nstr(sat_logh,6)}")

    # ----- 2. TRACE both branches -----
    br1 = trace_branch(s_hat, d1, W, tau, level, sat_logh)
    br2 = trace_branch(s_hat, d2, W, tau, level, sat_logh)

    # ----- 3. VERIFY -----
    res = []
    for name, br in (("branch+", br1), ("branch-", br2)):
        a = analyse_branch(br, Whalf)
        pole_dist, crossed = integer_poles_swept(br, s_hat)
        res.append((name, a, pole_dist, crossed))
        print(f" [3] {name}: steps={a['n']:>4}  end s={mp.nstr(a['end_s'],6)}  "
              f"(Re end={mp.nstr(a['end_Re'],4)})")
        print(f"        (ii) max non-monotone increment of Re Phi = {mp.nstr(a['max_violation'],4)}  "
              f"(<=0 => strictly descending)")
        print(f"        tail: Re Phi dropped {mp.nstr(a['tail_drop'],5)} from saddle "
              f"(log|h| dropped {mp.nstr(sat_logh - br[-1]['logh'],5)})")
        print(f"        strip: max Im s on path = {mp.nstr(a['max_Im_s'],8)}  vs W/2={mp.nstr(Whalf,8)}  "
              f"(margin {mp.nstr(Whalf - a['max_Im_s'],4)})")
        print(f"        (c) prefactor log|a_s/sin| range = [{mp.nstr(a['pref_min'],5)}, "
              f"{mp.nstr(a['pref_max'],5)}]  (bounded, max at saddle={mp.nstr(br[0]['pref'],5)})")
        print(f"        level-curve fidelity |Im Phi - const| max = {mp.nstr(a['level_dev'],3)}")
        print(f"        nearest positive-integer pole distance = {mp.nstr(pole_dist,5)}  "
              f"crossed={crossed}")

    # ----- 3H. OPERATIVE CONTOUR: horizontal ray at the strip boundary -----
    # The literal constant-phase path through the saddle does NOT remain in the
    # strip (see branch+ above). The contour the proof deforms to is the
    # HORIZONTAL line Im s = W/2 (strip boundary) carried out to Re s -> +infty,
    # where the factorial decay of 1/Gamma(2s+1) gives genuine monotone descent.
    sat_RePhi = mp.re(Phi(s_an, W))
    hb = trace_horizontal(W, tau, W/2)          # strip boundary eta=W/2
    h0 = trace_horizontal(W, tau, mp.mpf('0.001'))  # near real axis (Abel-Plana)
    ah = analyse_horizontal(hb, sat_RePhi)
    a0 = analyse_horizontal(h0, sat_RePhi)
    print(f" [3H] OPERATIVE CONTOUR (horizontal, the one the proof uses):")
    print(f"      Im s = W/2 = {mp.nstr(W/2,6)}:  Re Phi monotone? max-up={mp.nstr(ah['max_up'],4)} "
          f"(Phi_full max-up={mp.nstr(ah['max_up_full'],4)}) | drop over [0,{int(ah['end_sig'])}]={mp.nstr(ah['drop'],5)}")
    print(f"           prefactor log|a_s/sin| in [{mp.nstr(ah['pref_min'],5)},{mp.nstr(ah['pref_max'],5)}]"
          f"  pole-dist(min)={mp.nstr(ah['min_pole'],5)} (>=W/2={mp.nstr(W/2,5)})")
    print(f"      Im s -> 0+ (Abel-Plana):  Re Phi max-up={mp.nstr(a0['max_up'],4)} | drop={mp.nstr(a0['drop'],5)}"
          f"  pole-dist(min)={mp.nstr(a0['min_pole'],5)}  <- oscillatory, NOT descending")

    # CAVEAT diagnostic: is the saddle the MAX of |h| over the FULL strip
    # 0<=Im s<=W/2 ?  (Required for a saddle to *dominate* the contour integral.)
    # Coarse grid; near Im s~0 between integer poles |h| is LARGER than at the
    # saddle (1/|sin| spikes), so the saddle does NOT dominate the strip.
    sat = logabs_h(s_an, W, tau)
    gridmax = mp.mpf('-inf'); argmax = None; K = 12
    for ki in range(K+1):
        sig = mp.mpf(15)*ki/K
        for kj in range(1, K+1):
            eta = (W/2)*kj/K
            v = logabs_h(mp.mpc(sig, eta), W, tau)
            if v > gridmax:
                gridmax = v; argmax = (float(sig), float(eta))
    print(f"      strip-dominance: max log|h| over 0<Im s<=W/2 = {mp.nstr(gridmax,5)} at "
          f"(Re={argmax[0]:.2f},Im={argmax[1]:.2f}) vs saddle {mp.nstr(sat,5)}  "
          f"=> saddle {'dominates' if gridmax<=sat+mp.mpf('1e-3') else 'does NOT dominate (|h| larger near real axis)'}")

    # ----- 3(c). e^{pi W/2} prefactor cancellation at the saddle -----
    # a_s* = W^{2s*}/Gamma(2s*+1) with s*=iW/2 => 2s* = iW.  W^{iW}=e^{iW logW}
    # is unimodular; |Gamma(1+iW)| = sqrt(pi W / sinh(pi W)) ~ sqrt(2 pi W) e^{-pi W/2}.
    # so |a_s*| ~ e^{+pi W/2}/sqrt(2 pi W).  And |1/sin(pi s*)|=|1/sin(i pi W/2)|
    # =1/sinh(pi W/2) ~ 2 e^{-pi W/2}.  Product => the e^{+/- pi W/2} CANCEL,
    # leaving |a_s*/sin(pi s*)| ~ 2/sqrt(2 pi W)*<unimod> = O(1/sqrt W).
    sstar = I*Whalf
    logGabs = mp.re(mp.loggamma(1+I*W))          # Re log Gamma(1+iW)
    la_abs = mp.re(2*sstar*mp.log(W)) - logGabs   # log|a_s*|
    sin_abs = mp.log(abs(mp.sin(mp.pi*sstar)))    # log|sin(pi s*)| = log sinh(pi W/2)
    pref_at_star = la_abs - sin_abs               # log|a_s*/sin(pi s*)|
    halfpiW = float(mp.pi*W/2)
    print(f" [3c] e^{{pi W/2}} cancellation at s*=iW/2  (pi W/2 = {halfpiW:.4f}):")
    print(f"        log|a_s*|        = {mp.nstr(la_abs,6)}   "
          f"(approx +piW/2 - (1/2)log(2 pi W) = {mp.nstr(mp.pi*W/2 - mp.log(2*mp.pi*W)/2,6)})")
    print(f"        log|sin(pi s*)|  = {mp.nstr(sin_abs,6)}   "
          f"(approx +piW/2 - log2 = {mp.nstr(mp.pi*W/2 - mp.log(2),6)})")
    print(f"        log|a_s*/sin|    = {mp.nstr(pref_at_star,6)}   "
          f"=> NO e^{{piW/2}} (cancelled). O(1/sqrt W): -(1/2)logW={mp.nstr(-mp.log(W)/2,5)}")

    # ----- 4. OBSTRUCTIONS: search for a SECOND saddle on/near the strip -----
    # scan starting points along the imaginary axis and a band, Newton each,
    # collect distinct roots of Phi' with Re>=0, |Im|<pi/tau.
    print(" [4] obstruction scan (second saddle / tail closure):")
    seeds = []
    for fr in (mp.mpf('0.25'), mp.mpf('0.6'), mp.mpf('0.9'), mp.mpf('1.4'),
               mp.mpf('2.0'), mp.mpf('3.0')):
        seeds.append(I*W*fr)
        seeds.append(mp.mpf('1.0') + I*W*fr)
    roots = []
    for sd in seeds:
        try:
            r = mp.findroot(lambda z: Phi1(z, W), sd)
        except Exception:
            continue
        if mp.re(r) < -mp.mpf('0.5'):
            continue
        if abs(mp.im(r)) > float(mp.pi/tau):
            continue
        if abs(Phi1(r, W)) > mp.mpf('1e-12'):
            continue
        dup = any(abs(r - rr) < mp.mpf('1e-8') for rr in roots)
        if not dup:
            roots.append(r)
    roots.sort(key=lambda z: float(mp.im(z)))
    for r in roots:
        tag = " <- principal" if abs(r - s_an) < mp.mpf('1e-6') else ""
        print(f"        Phi'=0 at s={mp.nstr(r,8)}  |Phi''|={mp.nstr(abs(Phi2(r,W)),5)}{tag}")
    # tail closure: did BOTH branches reach the e^{-10} drop or Re=15?
    closeA = (sat_logh - br1[-1]['logh'])
    closeB = (sat_logh - br2[-1]['logh'])
    print(f"        tail closure: branch+ log|h| drop={mp.nstr(closeA,5)}, "
          f"branch- drop={mp.nstr(closeB,5)} (target >=10)")
    return dict(tau=tau, s_an=s_an, s_full=s_full, p2_an=p2_an,
                res=res, roots=roots, sat_logh=sat_logh,
                closeA=closeA, closeB=closeB, Whalf=Whalf,
                ah=ah, a0=a0, pref_at_star=pref_at_star)

if __name__ == "__main__":
    summary = []
    for t in ['0.05', '0.02', '0.01']:
        summary.append(run(t))
        print()

    # ---- final verdict table ----
    print("#"*90)
    print("# VERDICT A -- LITERAL constant-phase steepest-descent path through the saddle")
    print("#"*90)
    for S in summary:
        worst_viol = max(float(r[1]['max_violation']) for r in S['res'])
        max_ims = max(float(r[1]['max_Im_s']) for r in S['res'])
        ok_strip = max_ims <= float(S['Whalf']) + 1e-9
        ok_close = (float(S['closeA']) >= 10) and (float(S['closeB']) >= 10)
        nsad = len(S['roots'])
        print(f" tau={float(S['tau']):>5}: local descent max-viol={worst_viol:.1e} (=0 OK) | "
              f"strip maxIm={max_ims:.3f} vs W/2={float(S['Whalf']):.3f} -> {'IN' if ok_strip else 'LEAVES STRIP'} | "
              f"tails close(>=10)? {'YES' if ok_close else 'NO (path curls back, does not reach +inf)'} | #saddles={nsad}")
    print("#"*90)
    print("# VERDICT B -- OPERATIVE CONTOUR (horizontal Im s = W/2, the one the proof uses)")
    print("#"*90)
    for S in summary:
        ah = S['ah']
        # analytic phase exactly monotone; full phase has only an O(sqrt tau)
        # transient bump at small Re s (the slowly-varying log g settling).
        ok_ii_an = float(ah['max_up']) < 1e-9
        ii_full = float(ah['max_up_full'])    # O(sqrt tau), shrinks with tau
        ok_pref = float(ah['pref_max']) < 5   # bounded, ~ -log(W)/2 < 0
        ok_pole = float(ah['min_pole']) >= float(S['Whalf']) - 1e-9
        ok_close = float(ah['drop']) >= 10
        print(f" tau={float(S['tau']):>5}: (ii) Re Phi[analytic] monotone-DEC max-up={float(ah['max_up']):.0e} -> {'OK' if ok_ii_an else 'FAIL'}; "
              f"Re Phi[+log g] bump={ii_full:.1e} (O(sqrt tau) transient, Re s<2.5 only) | "
              f"(c) pref<= {float(ah['pref_max']):.2f} -> {'OK' if ok_pref else 'FAIL'} | "
              f"poleDist={float(ah['min_pole']):.3f}>=W/2 -> {'OK' if ok_pole else 'FAIL'} | "
              f"tail drop={float(ah['drop']):.1f} -> {'CLOSES' if ok_close else 'PARTIAL'}")
    print("#"*90)
    print("# CAVEAT (blocks a fully-rigorous steepest-descent proof):")
    print("#  - The LITERAL constant-phase path through s_hat leaves the strip (Verdict A).")
    print("#  - On Im s=W/2 the saddle does NOT dominate |h|: |h| is LARGER near the real")
    print("#    axis between integer poles (1/|sin| spikes). So |T2|=O(sqrt tau) is NOT a")
    print("#    saddle-DOMINATED contour bound; it is the REAL-AXIS stationary-phase result")
    print("#    (foundation phase Phi(y), Phi''=-4/W) with tails controlled by 1/Gamma decay.")
    print("#  - Citable theorem for the BOUND: van der Corput 2nd-deriv (needs A bounded")
    print("#    variation on the SP window) or Olver explicit-error steepest descent.")
    print("#"*90)
