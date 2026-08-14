"""
BREAK test (2)+(3): Is the finite-loop saddle reconstruction of Y3 a CONVERGENT/asymptotic
series that reaches a1=1.75077, or does it run in sqrt(tau) (orders mix) / diverge (Gevrey tail)?

We build the saddle-point Laplace expansion of
   INT e^{W(xi)} dxi,  W = -xi^2/(4tau) - logD(xi),
at the true complex saddle xi*, to L loops (L=0..4), reconstruct Y3 as 2 Re[norm * pref * (1 + c1 + c2 + ...)],
and at each travel pole compute the reconstruction's relative error e_L = |Y3 - recon_L|/|Y3|.

DECISIVE diagnostics:
  (A) does e_L decrease with L at fixed pole?  (asymptotic series should improve then diverge)
  (B) the implied a1 from recon: a1_recL = (recon_L/target - 1)/tau.  Does a1_recL -> 1.75077 as L grows?
  (C) per-loop coefficient magnitudes |c1|,|c2|,|c3|,|c4| at the pole: ratio test.
      If |c_{L+1}/c_L| ~ const*L (factorial growth) => Gevrey/divergent => NEVER reaches a1 by truncation.
      If they decay geometrically => convergent => a1 reachable.

If a1_recL stalls at ~1.73-1.79 and loop coeffs grow factorially, the 'state-integral closes a1'
claim is REFUTED: a1 is genuinely all-loop / Gevrey, not a finite Bernoulli coefficient.

Scalar mpmath + sympy for the h_k recursion. dps<=50.
"""
import mpmath as mp
import sympy as sp

gg = sp.symbols('g')
hpoly = [gg]
for k in range(2, 13):
    hpoly.append(sp.expand(gg*(1-gg)*sp.diff(hpoly[-1], gg)))
hfun = [sp.lambdify(gg, hp, 'mpmath') for hp in hpoly]

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+12)); s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1-ai); ai *= p
    return s

def Wderivs(xi, tau, kmax):
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

def Y3_series(x, q, K=20000):
    def qk(a, p, k):
        r = mp.mpf(1); aj = a
        for _ in range(k): r *= (1-aj); aj *= p
        return r
    s = mp.mpf(0)
    for k in range(K):
        dk = (mp.mpf(-2))**k*(1-q)**k*q**(k*k+3*k)/(qk(q**2, q**2, k)*qk(q**5, q**2, k))
        t = dk*x**(2*k+3); s += t
        if k > 12 and abs(t) < mp.mpf(10)**(-(mp.mp.dps+6))*max(abs(s),1): break
    return s

# Laplace loop coefficients c_L from W-derivatives at saddle.
# Standard: INT e^{W} = e^{W0} sqrt(2pi/(-W2)) * sum_L c_L,  with s2=-1/W2 the variance.
# c_0=1; c_1 = s2^2 W4/8 + s2^3 (5/24) W3^2; c_2 as in CONF; we compute c_1..c_4 via the
# Wojdylo / moment formula. Use the explicit formulas through L=2 and Monte? No: use exact
# moment recursion. We'll implement the general formula via Bell-poly moments of the fluctuation.
# Fluctuation phi(t)=sum_{j>=3} W_j/j! t^j (t=xi-xi*). With Gaussian weight var s2.
# c_L = sum over partitions; implement via series multiplication of exp(phi) and Wick contraction.

def loop_coeffs(Wd, s2, Lmax):
    # Wd is [W0, W2, W3, ...]; Wj for j>=2 is Wd[j-1].  Loop grade L = p/2 - n (n = #phi-factors).
    # VALIDATED against explicit c1,c2 formulas to ~1e-43.
    from collections import defaultdict
    def dfact(n):
        r=mp.mpf(1)
        while n>1: r*=n; n-=2
        return r
    def gm(p):
        if p%2: return mp.mpf(0)
        m=p//2; return s2**m*dfact(2*m-1) if m>0 else mp.mpf(1)
    maxj = 2*Lmax+2
    phi = [(j, (Wd[j-1] if (j-1)<len(Wd) else mp.mpf(0))/mp.factorial(j)) for j in range(3, maxj+1)]
    phi = [(j,c) for (j,c) in phi if abs(c)>0]
    acc = defaultdict(mp.mpf); acc[(0,0)] += mp.mpf(1)
    cur = {(0,0): mp.mpf(1)}; fact = mp.mpf(1)
    for n in range(1, 2*Lmax+3):
        fact *= n; nxt = defaultdict(mp.mpf)
        for (pa,na),ca in cur.items():
            for (j,cj) in phi: nxt[(pa+j, na+1)] += ca*cj
        cur = nxt
        for (p,nn),c in cur.items(): acc[(p,nn)] += c/fact
    cL = [mp.mpf(0)]*(Lmax+1)
    for (p,nn),c in acc.items():
        g = gm(p)
        if g == 0: continue
        L = p//2 - nn
        if 0 <= L <= Lmax: cL[L] += c*g
    return cL

with open("poles.txt") as f:
    polesq = [mp.mpf(l.strip()) for l in f if l.strip()]

print("Loop-series reconstruction at travel poles: a1_recL and loop-coeff ratio test")
print(f"{'m':>3} {'tau':>8} {'a1_true':>9} | {'a1_rec0':>8} {'a1_rec1':>8} {'a1_rec2':>8} {'a1_rec3':>8} {'a1_rec4':>8} | {'|c2/c1|':>8} {'|c3/c2|':>8} {'|c4/c3|':>8}")
for m, qp in enumerate(polesq):
    if m < 3 or m > 6: continue
    tau = -mp.log(qp); mp.mp.dps = max(45, int(45 + 1.2/float(tau)))
    q = mp.e**(-tau); w = mp.sqrt(2/tau); sinw = mp.sin(w)
    target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
    Y3 = Y3_series(1/q, q)
    a1t = (Y3/target - 1)/tau
    xs = saddle(tau)
    Lmax=4
    Wd, _ = Wderivs(xs, tau, 2*Lmax+2)
    s2 = -1/Wd[1]
    cL = loop_coeffs(Wd, s2, Lmax)
    pref = mp.e**Wd[0]*mp.sqrt(2*mp.pi*s2)
    p52 = mp.e**poch_logsum(q**5, q**2)
    norm = q**(-3)/(p52*mp.sqrt(4*mp.pi*tau))
    a1rec=[]
    run = mp.mpf(0)
    for L in range(Lmax+1):
        run += cL[L]
        recon = norm*2*mp.re(pref*run)
        a1rec.append(float(((recon/target - 1)/tau).real))
    # ratios
    def rat(i):
        return float(abs(cL[i]/cL[i-1])) if abs(cL[i-1])>0 else float('nan')
    print(f"{m:>3} {float(tau):>8.5f} {float(a1t.real):>9.5f} | "
          f"{a1rec[0]:>8.4f} {a1rec[1]:>8.4f} {a1rec[2]:>8.4f} {a1rec[3]:>8.4f} {a1rec[4]:>8.4f} | "
          f"{rat(2):>8.3f} {rat(3):>8.3f} {rat(4):>8.3f}", flush=True)
print()
print("READ: if a1_recL stalls (not -> 1.75077) and |c_{L+1}/c_L| GROWS with L (factorial/Gevrey),")
print("the finite-loop state-integral does NOT close a1 -> claim REFUTED, gap = lem:cos standing.")
print("If a1_recL -> 1.75077 and ratios bounded/decaying, the loop series DOES reach a1 (claim supported).")
