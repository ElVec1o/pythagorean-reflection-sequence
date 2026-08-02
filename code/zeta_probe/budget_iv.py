#!/usr/bin/env python3
"""
budget_iv.py -- INTERVAL-ARITHMETIC certification of the uniform stack of budget.py.

budget.py evaluates the psi''-majorant stack at the right endpoint b of each interval and
argues that every atom is monotone in tau, so the endpoint value bounds the whole range.
This file removes both weaknesses on any COMPACT subrange:

  * arithmetic:  every operation is mpmath.iv (directed rounding), so the printed bounds are
    rigorous enclosures, not floating-point evaluations;
  * monotonicity: tau enters as an INTERVAL [lo, hi], so the result encloses the stack for
    EVERY tau in the cell -- no atom needs to be monotone.

What this does NOT do: the interval (0, tau_min] cannot be covered by finitely many cells.
There the paper's power-counting (every term is a positive power of tau times an interval
constant, hence -> 0) remains the argument.  Its role is unchanged; what is new is that the
compact part is now certified rather than evaluated.

Structure mirrors budget.py::G1_majorant and budget.py::uniform_stack line for line.
"""
from math import factorial as _fact
from mpmath import iv, mp

iv.dps = 40
mp.dps = 40

def IV(x):
    return iv.mpf(x)

def F(n):                      # exact factorial as an interval
    return iv.mpf(_fact(n))

def G1_majorant_iv(T):
    """Interval version of budget.py::G1_majorant, T an interval for tau."""
    q = iv.exp(-T); s2 = T/2; h = T/2
    z0 = iv.sqrt(2*(1-q)); rho = z0*iv.exp(h)
    r2 = rho**2
    lead = iv.exp(2*h)*abs(T/(2*(1-q)) - 1/(1+q))
    d = 1 - r2
    R0 = rho**4/(4*(1-q**4)*d)
    E1 = rho**3/((1-q**3)*d)
    E2 = rho**4/((1-q**4)*d)
    A1 = rho/(1-q)
    B1 = r2/(1-q**2)
    dReA = (2*A1*E1 + E1**2 + (B1+E2)**2)*s2/2
    ImA = (A1+E1)*(B1+E2)*s2
    ReL2b = 2*r2/(1-q**2) + 4*rho**4/((1-q**4)*d)
    ImL2b = rho/(1-q) + 3*rho**3/((1-q**3)*d)
    Reb_dev = ReL2b*s2
    Imb = ImL2b*s2
    b2min = (1-Reb_dev)**2
    return (lead + R0 + dReA + ImA*Imb/b2min
            + (A1**2*s2/2)*(Reb_dev + Imb**2)/b2min)

def uniform_stack_iv(lo, hi, mode='top', verbose=True):
    """Rigorous enclosure of the scaled stack over tau in [lo, hi]."""
    T = iv.mpf([lo, hi])
    q = iv.exp(-T); v = (1-q)/T
    u_lo = iv.sqrt(v); u_hi = iv.exp(T/2)
    rho = iv.sqrt(2*T)*iv.exp(T/2)
    x = rho/q
    w = iv.sqrt(2/T); s = iv.sqrt(T/2)
    t0 = 1 - rho
    uv = u_hi/v
    S = lambda n: sum((q**j for j in range(n)), IV(0))

    def tail(m, kmin=2):
        t = IV(0); last = IV(0)
        for k in range(kmin, 400):
            last = IV(k)**m * x**k
            t = t + last
        r = (IV(400)/399)**m * x
        return t + last*r/(1-r)

    def A(n):
        return (2*u_hi**2/(v*q)) * tail(n-2)/x**2

    Ae = 4*u_hi**2/(v*(1+q))
    K4 = 4*u_hi**4/(v*q**3*(1-x))
    Reb_lo = 1 - (Ae + T*K4)*T/2
    invb_hi = 1/Reb_lo

    c1 = G1_majorant_iv(T)/iv.sqrt(T)
    amp_hi = iv.exp(c1*iv.sqrt(T))*iv.sqrt(invb_hi)

    L1w = uv + A(1)/w
    R0_hi = rho**4/(4*(1-q**4)*(1-rho**2))
    absb = 1 - (Ae + T*K4)*T/2
    amp_abs = iv.exp(-iv.exp(-2*T)/(1+q) + R0_hi + L1w**2/(2*absb))/iv.sqrt(absb)
    c_hi = L1w*invb_hi
    sg_hi = invb_hi
    Mh = [IV(1), c_hi]
    for k in range(2, 42):
        Mh.append(c_hi*Mh[k-1] + (k-1)*sg_hi*Mh[k-2])
    C = {n: (1+(n+1)*sg_hi)*Mh[n] + c_hi*Mh[n+1] for n in range(3, 36)}

    L2w = uv + A(2)/w
    T1w = amp_hi*L2w*invb_hi

    gL = {n: uv + A(n)/w for n in range(3, 11)}
    lin = sum((amp_abs*C[n]/F(n)*gL[n]*w**(3-n) for n in range(3, 11)), IV(0))

    base = {n: gL[n]/F(n) for n in range(3, 11)}
    cur = dict(base); prod = IV(0)
    for m in range(2, 12):
        nxt = {}
        for N1, v1 in cur.items():
            for n2, v2 in base.items():
                N = N1 + n2
                if N <= 34:
                    nxt[N] = nxt.get(N, IV(0)) + v1*v2
        cur = nxt
        for N, val in nxt.items():
            prod = prod + amp_abs*C[N]*val/F(m)*w**(2-N+m)

    Ghat_half = (uv*w)*(iv.log(IV(2)) - IV('0.5') - IV('0.125'))
    Fhat = Ghat_half + iv.exp(Ghat_half)
    if mode == 'top':
        assert IV(lo).a >= IV('1.2e-4').a, "top cell must lie in [1.2e-4, .]"
        blanket = amp_abs*Fhat*(2/t0)**11*((T/2)*Mh[11]*s**11 + Mh[13]*s**13)*(4/T**2)
    else:
        assert IV(hi).b <= IV('1.2e-4').b, "deep cell must lie in (., 1.2e-4]"
        kap = uv*w
        lin_bl = amp_abs*(2*kap/11)*(2/t0)**11/IV(2)**11*((T/2)*Mh[11]*s**11 + Mh[13]*s**13)*(4/T**2)
        prod_bl = amp_abs*IV('0.79')*(IV('0.53')*kap)**2/t0**6*((T/2)*Mh[6]*s**6 + Mh[8]*s**8)*(4/T**2)
        zoneB = iv.exp(IV('0.78')*w - IV('0.63')/T**(IV(2)/3) + 2*iv.log(1/T))
        blanket = lin_bl + prod_bl + zoneB
        prod = IV(0)
    T3 = lin + prod + blanket

    Aexp = iv.sqrt(IV(2))*uv/t0
    Bexp = t0**2/4
    g_incr = (Bexp - Aexp*iv.sqrt(T)/2 - 2*T).a > 0
    eps = (4/T**2)*iv.exp(Aexp/iv.sqrt(T) - Bexp/T)

    ptail = sum((amp_abs*Mh[n+1]/F(n)*gL[n]*s**(n-2) for n in range(3, 11)), IV(0))
    curp = dict(base)
    for m in range(2, 12):
        nxtp = {}
        for N1, v1 in curp.items():
            for n2, v2 in base.items():
                N = N1 + n2
                if N <= 34:
                    nxtp[N] = nxtp.get(N, IV(0)) + v1*v2
        curp = nxtp
        for N, val in nxtp.items():
            ptail = ptail + amp_abs*Mh[N+1]*val/F(m)*s**(N-m-1)
    if mode == 'top':
        ptail = ptail + amp_abs*Fhat*(2/t0)**11*Mh[12]*s**10
    else:
        kap2 = uv*w
        ptail = ptail + amp_abs*(2*kap2/11)/t0**11*Mh[12]*s**10
        ptail = ptail + amp_abs*IV('0.79')*(IV('0.53')*kap2)**2/t0**6*Mh[7]*s**5
    G3_ok = ptail.b <= IV('0.5').b
    psi1w_hi = amp_hi*L1w*invb_hi + ptail/w

    sig2c = amp_abs*(1+Mh[2])/2
    sig3c = amp_abs*(Mh[3]+3*Mh[1])
    G4_coef = sig2c/4 + IV('0.118')*sig3c*iv.sqrt(T)

    sZ_lo = 1/(psi1w_hi/iv.sqrt(v))
    Phi_lo = q**IV('0.75')*(sZ_lo - G4_coef*T)
    wcosT = psi1w_hi/Phi_lo

    K_E1 = 2*iv.sqrt(IV(2))*u_hi**3/(v*S(3)*(1-rho**2))
    K_E2 = 4*u_hi**4/(v*S(4)*(1-rho**2))
    B1_lo = 2*u_lo**2/2
    r1 = (T*K_E2/B1_lo + T*K_E1/(iv.sqrt(IV(2))*u_lo))*IV('1.2')
    K_odd = 2*iv.sqrt(IV(2))*u_hi**3/(v*q**2*(1-x))
    r2_ = T*K_odd/(iv.sqrt(IV(2))*u_lo)*IV('1.2')
    invb_dev = (1-Reb_lo)/Reb_lo
    cN = u_hi/(6*v*(1+q))
    B1vu_hi = 2*u_hi/(1+q)
    C_r = B1vu_hi*r1/T + uv*(r2_/T + invb_dev/T*(1+r2_))
    arctan_cubic = 2*(IV('1.1')*iv.sqrt(2*T))**3/(3*T**IV('1.5'))
    C_sin = iv.sqrt(IV(2))*(cN*T + C_r) + 2*arctan_cubic
    sin_ok = C_sin.b <= (2/iv.sqrt(T)).a
    wsin = iv.sqrt(IV(2))*C_sin*T

    T2w = amp_hi*(L1w*invb_hi)**2*(wcosT + wsin)
    total = T1w + T2w + (T3 + eps)/w
    ok = (total.b <= IV('3.5').b) and sin_ok and g_incr and G3_ok
    if verbose:
        print(f"  [{float(lo):.4e}, {float(hi):.4e}] mode={mode}:")
        print(f"    c1={float(c1.b):.4f}  ptail={float(ptail.b):.4f}  G4={float(G4_coef.b):.4f}")
        print(f"    T3 = lin {float(lin.b):.4f} + prod {float(prod.b):.4f} + blanket {float(blanket.b):.3e} = {float(T3.b):.4f}")
        print(f"    T1/w <= {float(T1w.b):.4f}   T2/w <= {float(T2w.b):.4f}   eps <= {float(eps.b):.2e}")
        print(f"    wcosT={float(wcosT.b):.4f} wsin={float(wsin.b):.4f} C_sin={float(C_sin.b):.3f} psi1w={float(psi1w_hi.b):.4f}")
        print(f"    TOTAL <= {float(total.b):.4f}  {'PASS' if ok else 'FAIL'}")
    return total, ok


def safe_stack(a, b, mode):
    """Enclosure, or (None, False) if a wide cell drives an intermediate out of range
       (e.g. Re beta's lower bound crossing 0 under a sqrt).  Such a cell is simply
       refined; no conclusion is drawn from the failure."""
    try:
        return uniform_stack_iv(repr(a), repr(b), mode=mode, verbose=False)
    except Exception:
        return None, False


def certify(lo, hi, mode, maxdepth=22, nseed=32, verbose=False):
    """Adaptive bisection: refine a cell only if its enclosure fails. Returns
       (ok, ncells, worst_upper, maxdepth_used)."""
    r0 = (float(hi)/float(lo))**(1.0/nseed)
    edges = [float(lo)*r0**i for i in range(nseed)] + [float(hi)]
    edges[0] = float(lo)          # clamp both ends exactly: no sliver at either edge,
    stack = [(edges[i], edges[i+1], 0) for i in range(nseed)]   # and no interior gap
    ncells = 0; worst = 0.0; dmax = 0; ok_all = True
    while stack:
        a, b, d = stack.pop()
        t, o = safe_stack(a, b, mode)
        ncells += 1; dmax = max(dmax, d)
        if o:
            worst = max(worst, float(t.b))
            continue
        if d >= maxdepth:
            ok_all = False
            tt = "n/a" if t is None else f"{float(t.b):.3f}"
            print(f"    UNRESOLVED at depth {d}: [{a:.6e},{b:.6e}] total<= {tt}")
            continue
        m = (a*b) ** 0.5          # geometric midpoint
        stack.append((a, m, d+1)); stack.append((m, b, d+1))
    return ok_all, ncells, worst, dmax


if __name__ == "__main__":
    print("=" * 78)
    print("INTERVAL-ARITHMETIC certification of the uniform stack (mpmath.iv, dps=40)")
    print("Adaptive bisection; every bound is a rigorous enclosure valid for EVERY tau")
    print("in the cell -- no atom is assumed monotone.")
    print("=" * 78)

    allok = True

    print("\n(a) endpoint cells (degenerate) -- cross-check against budget.py's floats:")
    t, o = uniform_stack_iv('5e-3', '5e-3', mode='top');  allok &= o
    t, o = uniform_stack_iv('1.2e-4', '1.2e-4', mode='deep'); allok &= o

    print("\n(b) TOP interval [1.2e-4, 5e-3]:")
    ok, nc, worst, dm = certify(1.2e-4, 5e-3, 'top', nseed=160)
    allok &= ok
    print(f"    {nc} cells (max depth {dm}), worst TOTAL <= {worst:.4f} vs 3.5 -> {'PASS' if ok else 'FAIL'}")

    print("\n(c) DEEP interval [1e-8, 1.2e-4]:")
    ok, nc, worst, dm = certify(1e-8, 1.2e-4, 'deep', nseed=160)
    allok &= ok
    print(f"    {nc} cells (max depth {dm}), worst TOTAL <= {worst:.4f} vs 3.5 -> {'PASS' if ok else 'FAIL'}")

    print("\n(0, 1e-8] is NOT covered here: no finite set of cells reaches tau = 0.")
    print("There the paper's power-counting argument (every term a positive power of tau)")
    print("remains the proof; this file certifies the compact part it used to assert.")
    print("\nSUMMARY:", "ALL CELLS PASS" if allok else "*** A CELL FAILED ***")
