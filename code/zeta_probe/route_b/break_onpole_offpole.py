"""
DECISIVE: off-pole vs on-pole reconstruction-error ORDER.
CONF_stateintegral_ohtsuki claims +1-loop gives relative O(tau) error ~0.04*tau OFF pole.
But the TARGET bound |Y3 - E| <= C tau^{5/2} is AT the travel poles, where sin(w)->0 so the
leading (3/sqrt2)tau^{3/2}sin w is itself SMALL -- the relative error structure is different.

We compute, for the SAME tau, both:
  - generic xi-integral relerr of +1-loop recon (off-pole-style, large generic value), and
  - the on-pole quantity: at a pole sin(w_m)=0-ish? No: poles q_m are where the GATE 1-Sigma=0,
    not where sin w=0. But the target uses sin w which at the pole is O(1) (w_m~(m+.5)pi+dev).
Actually the cleaner decisive test: reconstruct Y3 with +1 loop and +2 loop AT the poles and
look at the ABSOLUTE error vs C*tau^{5/2}. The control-function sanity: the +1-loop recon error
must be SMALLER than the 1.751*tau*|leading| = 1.751*tau*(3/sqrt2)tau^{3/2}|sin w| it claims to
explain. If recon1 error ~ a1_rec1 - a1_true ~ 0.02 in a1-units = 0.02*tau*leading, that's
SMALLER than the term... but a1_rec1=1.7698 != a1_true=1.75077, so the recon SYSTEMATICALLY
MIS-STATES the coefficient. The remaining 0.02*tau*leading IS an O(tau^{5/2}) absolute error,
but it is NOT captured/bounded by the finite-loop formula -- it's the residual we must bound,
and its size 0.02*tau*leading is what a HIGHER (all-)loop computation must supply.

Conclusion test: does (a1_recL) converge to a1_true as L grows, or stall/diverge?
We push to L=1,2,3 and see if |a1_recL - 1.75077| shrinks. If it does NOT shrink monotonically
to 0, the loop series does not resolve a1 (all-loop / divergent => Q2 yes).
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
        s += mp.log(1 - ai); ai *= p
    return s

def Wderivs(xi, tau, kmax=10):
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
                       mp.pi/2 - 0.5j*mp.log(1/tau), tol=mp.mpf(10)**-28)

def Y3_series(x, q, K=14000):
    def qk(a, p, k):
        r = mp.mpf(1); aj = a
        for _ in range(k): r *= (1-aj); aj *= p
        return r
    s = mp.mpf(0)
    for k in range(K):
        dk = (mp.mpf(-2))**k*(1-q)**k*q**(k*k+3*k)/(qk(q**2, q**2, k)*qk(q**5, q**2, k))
        t = dk*x**(2*k+3); s += t
        if k > 12 and abs(t) < mp.mpf(10)**(-(mp.mp.dps+6))*max(abs(s), mp.mpf(1)): break
    return s

# standard Laplace coeffs c1..c4 (Wojciechowski / DLMF) in s2,W3..W10
def cs_list(d):
    W2,W3,W4,W5,W6,W7,W8,W9,W10 = d[1],d[2],d[3],d[4],d[5],d[6],d[7],d[8],d[9]
    s2=-1/W2
    c1 = s2**2*(W4/8) + s2**3*(mp.mpf(5)/24*W3**2)
    c2 = (s2**3*(W6/48) + s2**4*(mp.mpf(35)/384*W4**2 + mp.mpf(7)/48*W3*W5)
          + s2**5*(mp.mpf(35)/64*W3**2*W4) + s2**6*(mp.mpf(385)/1152*W3**4))
    c3 = (s2**4*(W8/384) + s2**5*(mp.mpf(7)/192*W4*W6 + mp.mpf(7)/240*W3*W7 + mp.mpf(7)/640*W5**2)
          + s2**6*(mp.mpf(35)/128*W4**3 + mp.mpf(21)/64*W3*W4*W5 + mp.mpf(7)/96*W3**2*W6 + mp.mpf(7)/64*W3*W4*W5)
          + s2**7*(mp.mpf(1155)/1024*W3**2*W4**2 + mp.mpf(77)/192*W3**3*W5)
          + s2**8*(mp.mpf(25025)/9216*W3**4*W4)
          + s2**9*(mp.mpf(85085)/82944*W3**6))
    return s2,[c1,c2,c3]

with open("/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe/route_b/poles.txt") as f:
    polesq = [mp.mpf(l.strip()) for l in f if l.strip()]

print("a1_recL convergence test: does finite-loop a1 -> a1_true=1.75077 as L grows?")
print(f"{'m':>3} {'tau':>9} {'a1_true':>11} {'a1_rec1':>11} {'a1_rec2':>11} {'a1_rec3':>11}")
for m, qp in enumerate(polesq):
    if m not in (4,5,6): continue
    tau = -mp.log(qp); mp.mp.dps = max(55, int(55+1.3/float(tau)))
    q = mp.e**(-tau); w = mp.sqrt(2/tau); sinw = mp.sin(w)
    Y3 = Y3_series(1/q, q)
    target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
    a1t = ((Y3/target-1)/tau).real
    xs = saddle(tau); d,_ = Wderivs(xs, tau, 10)
    s2, cs = cs_list(d)
    pref = mp.e**d[0]*mp.sqrt(2*mp.pi*s2)
    p52 = mp.e**poch_logsum(q**5, q**2)
    norm = q**(-3)/(p52*mp.sqrt(4*mp.pi*tau))
    a1recs=[]
    partial=mp.mpf(1)
    for c in cs:
        partial=partial+c
        a1recs.append((( norm*2*mp.re(pref*partial)/target -1)/tau).real)
    print(f"{m:>3} {float(tau):>9.6f} {mp.nstr(a1t,9):>11} "
          f"{mp.nstr(a1recs[0],9):>11} {mp.nstr(a1recs[1],9):>11} {mp.nstr(a1recs[2],9):>11}", flush=True)
print()
print("READ: if a1_rec1,rec2,rec3 do NOT march toward 1.75077 (instead oscillate/diverge),")
print("the loop series is NOT resolving a1 at the pole => finite-loop truncation CANNOT")
print("certify |Y3-E|<=C tau^{5/2}; the residual is the all-loop/Gevrey tail (Q2 = YES).")
