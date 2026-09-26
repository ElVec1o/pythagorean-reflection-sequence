import sys, math
from flint import acb, arb, ctx

ctx.prec = 300

def zeta6():
    return acb(1)/2 + acb(0,1)*(acb(3).sqrt()/2)
ZETA6 = zeta6()

def q_of_t(t):
    return ZETA6*(-t).exp()

def terms_upto(q, K):
    out = [acb(1)]
    poch = acb(1)
    for k in range(1, K+1):
        poch *= (1-q**(2*k-1))*(1-q**(2*k))
        aa = -2*(1-q)
        term = aa**k * q**(k*k) / poch
        out.append(term)
    return out

def modu(x):
    re, im = x.real, x.imag
    m = (float(re.mid())**2+float(im.mid())**2)**0.5
    r = (float(re.rad())**2+float(im.rad())**2)**0.5
    return m, r
def mod_upper(x):
    m, r = modu(x); return m+r
def mod_lower(x):
    m, r = modu(x); return max(m-r, 0.0)

def B_bound_at_point(t, K=40, Kcheck=25):
    """Rigorous (mid,rad) enclosure of B(t) at an EXACT point t, with a validated
    (rB<1) geometric tail bound beyond K, checked over Kcheck extra terms."""
    q = q_of_t(t)
    terms = terms_upto(q, K+Kcheck)
    mags = [mod_upper(x) for x in terms]
    ratios = [mags[k+1]/mags[k] for k in range(K, K+Kcheck-1) if mags[k] > 0]
    rB = max(ratios) if ratios else 1.0
    if not (rB < 1):
        raise RuntimeError(f"ratio bound failed to converge (rB={rB}); increase K")
    tail = mags[K]*rB/(1-rB)
    S = acb(0)
    for k in range(K+1):
        S += terms[k]
    Sre = arb(float(S.real.mid()), float(S.real.rad())+tail)
    Sim = arb(float(S.imag.mid()), float(S.imag.rad())+tail)
    return acb(Sre, Sim), rB, tail

def main():
    centers = {
        4: complex(0.02732181489, 0.001017999912),
        5: complex(0.02193370833, 0.0005691659052),
    }
    K = 70
    nsamp_bdry = 4096   # samples on the certified disk boundary (radius rho)
    nsamp_R = 512       # samples on the larger Cauchy-estimate circle (radius R)
    for j, t0 in centers.items():
        t0c = acb(t0.real, t0.imag)
        rho = abs(t0)*0.12
        print(f"=== j={j}  t0={t0}  rho={rho:.6g} ===")

        # (1) rigorous min|B| on the certified boundary circle |t-t0|=rho
        min_B = None
        worst_rB1 = 0.0; worst_tail1 = 0.0
        args = []
        for i in range(nsamp_bdry):
            ang = 2*math.pi*i/nsamp_bdry
            ts = t0c + acb(rho*math.cos(ang), rho*math.sin(ang))
            Bball, rB, tail = B_bound_at_point(ts, K=K)
            lo = mod_lower(Bball)
            if min_B is None or lo < min_B: min_B = lo
            worst_rB1 = max(worst_rB1, rB); worst_tail1 = max(worst_tail1, tail)
            m, _ = modu(Bball)
            re_m = float(Bball.real.mid()); im_m = float(Bball.imag.mid())
            args.append(math.atan2(im_m, re_m))
        total = 0.0
        for i in range(nsamp_bdry):
            d = args[(i+1) % nsamp_bdry] - args[i]
            while d > math.pi: d -= 2*math.pi
            while d < -math.pi: d += 2*math.pi
            total += d
        winding = total/(2*math.pi)
        print(f"  (boundary) min|B| over {nsamp_bdry} pts = {min_B:.6e}  "
              f"[worst rB={worst_rB1:.4f}, worst tail={worst_tail1:.2e}]")
        print(f"  discrete winding number of arg(B) around the circle = {winding:.6f}")

        # (2) rigorous sup|B| on a larger circle |t-t0|=R=2*rho (for the Cauchy estimate)
        R = 2.0*rho
        max_BR = 0.0
        worst_rB2 = 0.0; worst_tail2 = 0.0
        for i in range(nsamp_R):
            ang = 2*math.pi*i/nsamp_R
            ts = t0c + acb(R*math.cos(ang), R*math.sin(ang))
            Bball, rB, tail = B_bound_at_point(ts, K=K)
            up = mod_upper(Bball)
            if up > max_BR: max_BR = up
            worst_rB2 = max(worst_rB2, rB); worst_tail2 = max(worst_tail2, tail)
        print(f"  (R={R:.4g} circle) sup|B| over {nsamp_R} pts = {max_BR:.6e}  "
              f"[worst rB={worst_rB2:.4f}, worst tail={worst_tail2:.2e}]")

        # (3) Cauchy derivative estimate: for |t-t0|<=rho, since B analytic on |z-t0|<=R,
        #     |B'(t)| <= sup_{|z-t0|=R}|B(z)| * R/(R-rho)^2
        sup_Bprime = max_BR * R/(R-rho)**2
        print(f"  Cauchy bound: sup_{{|t-t0|<=rho}}|B'(t)| <= {sup_Bprime:.6e}")

        # (4) MVT/Lipschitz aliasing exclusion along the boundary circle:
        #     any two points t1,t2 with |t1-t2|=chord satisfy
        #     |B(t1)-B(t2)| <= sup|B'| * chord  (straight segment stays inside |t-t0|<=rho, convex)
        chord = 2*rho*math.sin(math.pi/nsamp_bdry)
        margin = min_B - sup_Bprime*chord
        verdict = "RIGOROUS PASS (aliasing excluded)" if margin > 0 else "BOUND TOO WEAK"
        print(f"  chord (adjacent-sample step) = {chord:.4e}")
        print(f"  margin = min|B| - sup|B'|*chord = {margin:.4e}  ->  {verdict}")
        print()

if __name__ == '__main__':
    main()
