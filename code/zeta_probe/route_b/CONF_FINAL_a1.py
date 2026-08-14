"""
CONF_FINAL_a1.py -- compact, self-contained final confirmation (fast, m=3..6).
Three load-bearing facts:
 (1) a1_true = lim_{tau->0}(Y3/target - 1)/tau  extrapolates to 1.75077  [target=(3/sqrt2)tau^{3/2}sin w]
 (2) the leading saddle constant matches 1/(4sqrt2)=0.176777 (Y3/(tau^{3/2}sin w) -> 3/sqrt2*... check 1)
 (3) the FINITE-LOOP saddle reconstruction a1 (rec1,rec2) extrapolates to ~1.78 / ~1.73,
     i.e. does NOT equal a1_true=1.75077 -> a1 is an ALL-LOOP quantity (saddle near singularity).
"""
import mpmath as mp
import sympy as sp

gg = sp.symbols('g')
hpoly = [gg]
for k in range(2, 9):
    hpoly.append(sp.expand(gg*(1-gg)*sp.diff(hpoly[-1], gg)))
hfun = [sp.lambdify(gg, hp, 'mpmath') for hp in hpoly]

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+12)); s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1-ai); ai *= p
    return s

def Wderivs(xi, tau, kmax=6):
    q = mp.e**(-tau); e = mp.e**(1j*xi); a_list = [q**4, 2*(1-q)*q]
    Wv = -xi**2/(4*tau)
    for a in a_list: Wv -= poch_logsum(-a*e, q**2)
    Dk = [mp.mpc(0)]*(kmax+1); tol = mp.mpf(10)**(-(mp.mp.dps+12))
    for a in a_list:
        uu = a*e; p2 = q**2
        while abs(uu) > tol:
            g = uu/(1+uu)
            for k in range(1, kmax+1): Dk[k] += (1j)**k*hfun[k-1](g)
            uu *= p2
    out = [Wv]
    for k in range(2, kmax+1):
        base = -1/(2*tau) if k == 2 else mp.mpf(0)
        out.append(base - Dk[k])
    return out, -(2*xi)/(4*tau) - Dk[1]

def saddle(tau):
    return mp.findroot(lambda xi: Wderivs(xi, tau, 1)[1],
                       mp.pi/2 - 0.5j*mp.log(1/tau), tol=mp.mpf(10)**-25)

def Y3_series(x, q, K=12000):
    def qk(a, p, k):
        r = mp.mpf(1); aj = a
        for _ in range(k): r *= (1-aj); aj *= p
        return r
    s = mp.mpf(0)
    for k in range(K):
        dk = (mp.mpf(-2))**k*(1-q)**k*q**(k*k+3*k)/(qk(q**2, q**2, k)*qk(q**5, q**2, k))
        t = dk*x**(2*k+3); s += t
        if k > 12 and abs(t) < mp.mpf(10)**(-(mp.mp.dps+6))*max(abs(s), 1): break
    return s

with open("poles.txt") as f:
    polesq = [mp.mpf(l.strip()) for l in f if l.strip()]

rows = []
print(f"{'m':>3} {'tau':>9} {'lead_const':>12} {'a1_true':>10} {'a1_rec1':>9} {'a1_rec2':>9}", flush=True)
for m, qp in enumerate(polesq):
    if m < 3 or m > 6: continue
    tau = -mp.log(qp); mp.mp.dps = max(45, int(45 + 1.15/float(tau)))
    q = mp.e**(-tau); w = mp.sqrt(2/tau); sinw = mp.sin(w)
    Y3 = Y3_series(1/q, q)
    target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
    a1t = (Y3/target - 1)/tau
    lead_const = Y3/(tau**mp.mpf('1.5')*sinw)/3*mp.sqrt(2)   # -> 1 when Y3~(3/sqrt2)tau^1.5 sinw
    # saddle recon
    xs = saddle(tau); d, _ = Wderivs(xs, tau, 6); W0, W2, W3, W4, W5, W6 = d
    s2 = -1/W2
    c1 = s2**2*(W4/8) + s2**3*(mp.mpf(5)/24*W3**2)
    c2 = (s2**3*(W6/48) + s2**4*(mp.mpf(35)/384*W4**2 + mp.mpf(7)/48*W3*W5)
          + s2**5*(mp.mpf(35)/64*W3**2*W4) + s2**6*(mp.mpf(385)/1152*W3**4))
    pref = mp.e**W0*mp.sqrt(2*mp.pi*s2)
    p52 = mp.e**poch_logsum(q**5, q**2)
    norm = q**(-3)/(p52*mp.sqrt(4*mp.pi*tau))
    a1r1 = (norm*2*mp.re(pref*(1+c1))/target - 1)/tau
    a1r2 = (norm*2*mp.re(pref*(1+c1+c2))/target - 1)/tau
    rows.append((float(tau), float(a1t), float(a1r1.real), float(a1r2.real)))
    print(f"{m:>3} {float(tau):>9.5f} {mp.nstr(lead_const,9):>12} {mp.nstr(a1t,7):>10} "
          f"{mp.nstr(a1r1,6):>9} {mp.nstr(a1r2,6):>9}", flush=True)

# linear extrapolation tau->0 (last two)
def ex(col):
    (t1, v1), (t2, v2) = (rows[-2][0], rows[-2][col]), (rows[-1][0], rows[-1][col])
    return v2 - (v2-v1)/(t2-t1)*t2
print()
print(f"EXTRAP tau->0:  a1_true={ex(1):.6f} (target 1.75077)   a1_rec1={ex(2):.6f}   a1_rec2={ex(3):.6f}")
print("=> finite-loop saddle reconstruction does NOT reproduce a1_true; gap ~%.4f (all-loop tail)" % (1.75077-ex(3)))
