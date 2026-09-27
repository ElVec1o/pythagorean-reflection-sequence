import sys, math, time
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

def B_bound_at_point(t, Kmax=400, Kcheck=30):
    """Fixed-K validated tail bound: K=Kmax (chosen by the caller, comfortably past the
    per-mode magnitude peak for the given t0 but well short of double-underflow), check a
    Kcheck-window geometric ratio bound right after K."""
    K = Kmax
    q = q_of_t(t)
    terms = terms_upto(q, K+Kcheck)
    mags = [mod_upper(x) for x in terms]
    ratios = [mags[k+1]/mags[k] for k in range(K, K+Kcheck-1) if mags[k] > 0]
    rB = max(ratios) if ratios else 1.0
    if not (rB < 1) or rB != rB:
        raise RuntimeError(f"ratio bound failed to converge at K={K} (rB={rB}); increase Kmax/Kcheck")
    tail = mags[K]*rB/(1-rB)
    S = acb(0)
    for k in range(K+1):
        S += terms[k]
    Sre = arb(float(S.real.mid()), float(S.real.rad())+tail)
    Sim = arb(float(S.imag.mid()), float(S.imag.rad())+tail)
    return acb(Sre, Sim), rB, tail, K

def certify_j(j, t0, Kmax, nsamp_bdry, nsamp_R, Kcheck=25, rho_scale=0.12):
    t0c = acb(t0.real, t0.imag)
    rho = abs(t0)*rho_scale
    min_B = None
    args = []
    worst_rB1 = 0.0; worst_tail1 = 0.0; worst_K1 = 0
    for i in range(nsamp_bdry):
        ang = 2*math.pi*i/nsamp_bdry
        ts = t0c + acb(rho*math.cos(ang), rho*math.sin(ang))
        Bball, rB, tail, Kused = B_bound_at_point(ts, Kmax=Kmax, Kcheck=Kcheck)
        lo = mod_lower(Bball)
        if min_B is None or lo < min_B: min_B = lo
        worst_rB1 = max(worst_rB1, rB); worst_tail1 = max(worst_tail1, tail); worst_K1 = max(worst_K1, Kused)
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

    R = 2.0*rho
    max_BR = 0.0
    worst_rB2 = 0.0; worst_tail2 = 0.0; worst_K2 = 0
    for i in range(nsamp_R):
        ang = 2*math.pi*i/nsamp_R
        ts = t0c + acb(R*math.cos(ang), R*math.sin(ang))
        Bball, rB, tail, Kused = B_bound_at_point(ts, Kmax=Kmax, Kcheck=Kcheck)
        up = mod_upper(Bball)
        if up > max_BR: max_BR = up
        worst_rB2 = max(worst_rB2, rB); worst_tail2 = max(worst_tail2, tail); worst_K2 = max(worst_K2, Kused)

    sup_Bprime = max_BR * R/(R-rho)**2
    chord = 2*rho*math.sin(math.pi/nsamp_bdry)
    margin = min_B - sup_Bprime*chord
    passed = margin > 0
    return dict(j=j, t0=t0, rho=rho, min_B=min_B, max_BR=max_BR, sup_Bprime=sup_Bprime,
                chord=chord, margin=margin, winding=winding, passed=passed,
                worst_rB=max(worst_rB1,worst_rB2), worst_tail=max(worst_tail1,worst_tail2),
                K=max(worst_K1,worst_K2))

def main():
    # t*_j candidates from P1f_zeros.py 1 6, j=1..14 (mpmath findroot, 30 digits)
    centers = {
        1: complex(0.08527657336, 0.006563247233),
        2: complex(0.05271445399, 0.00429830755),
        3: complex(0.03509147213, 0.001335741484),
        4: complex(0.02732181489, 0.001017999912),
        5: complex(0.02193370833, 0.0005691659052),
        6: complex(0.01850586705, 0.0004428711925),
        7: complex(0.01591865371, 0.0003101280191),
        8: complex(0.01400655658, 0.0002484074616),
        9: complex(0.01248463283, 0.0001932414934),
        10: complex(0.01127091954, 0.0001595411873),
        11: complex(0.01026720696, 0.0001313345987),
        12: complex(0.009430247745, 0.0001113364088),
        13: complex(0.008718077658, 0.00009486643127),
        14: complex(0.008106642211, 0.00008217672568),
    }
    nsamp_bdry = 2048
    nsamp_R = 512
    ctx.prec = 400
    for j in sorted(centers):
        t0 = centers[j]
        Ret0 = t0.real
        # K fixed per-j, comfortably past the per-mode term-magnitude peak (k* = ln2/(2*Ret0))
        # while staying far short of double-underflow (~1e-308 in |term|).
        K = 20 if j == 1 else (70 if j <= 5 else (150 if j <= 10 else 220))
        scales = [0.12, 0.06, 0.03, 0.015, 0.008] if j <= 5 else [0.06, 0.03, 0.015, 0.008, 0.004, 0.002]
        t1 = time.time()
        result = None
        tried = []
        for scale in scales:
            try:
                res = certify_j(j, t0, K, nsamp_bdry, nsamp_R, Kcheck=30, rho_scale=scale)
            except Exception as ex:
                tried.append(f"scale={scale}: ERR {ex}")
                continue
            tried.append(f"scale={scale}: winding={res['winding']:.3f} margin={res['margin']:.3e}")
            if res['passed'] and abs(res['winding'] - 1.0) < 0.05:
                result = res
                break
        dt = time.time() - t1
        if result is None:
            print(f"j={j:2d} t0={t0}  NOT CERTIFIED at any tried rho_scale  [{'; '.join(tried)}]  t={dt:.2f}s", flush=True)
            continue
        print(f"j={result['j']:2d} t0={t0}  rho_scale used  rho={result['rho']:.4e}  winding={result['winding']:.6f}  "
              f"min|B|={result['min_B']:.4e}  sup|B'|={result['sup_Bprime']:.4e}  chord={result['chord']:.4e}  "
              f"margin={result['margin']:.4e}  CERTIFIED  "
              f"(rB={result['worst_rB']:.3f} tail={result['worst_tail']:.1e} Kmax_used={result['K']} t={dt:.2f}s)", flush=True)

if __name__ == '__main__':
    main()
