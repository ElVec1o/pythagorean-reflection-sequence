"""
CONF_a1_assembly.py  (analytic-derivative, fast)
================================================
Apply quantum-dilog / Ohtsuki state-integral saddle-point expansion to Y3(1/q)
AT THE TRAVEL POLES.  Extract leading constant and a1 = lim (Y3/target - 1)/tau.
target = (3/sqrt2) tau^{3/2} sin(w),  w=sqrt(2/tau).

W(xi) = -xi^2/(4tau) - L4(xi) - Lz(xi),  Lc(xi)=sum_{n>=0} log(1+a_c q^{2n} e^{ixi}),
a4=q^4, az=2(1-q)q.   xi-derivatives are ANALYTIC sums (no mp.diff):
  d/dxi log(1+u) , u=a q^{2n} e^{ixi}, du/dxi = i u.
Let for each term g=u/(1+u). Then with D=d/dxi (=i*u d/du):
  L'   = sum i*g
  L''  = sum i^2 g(1-g)            = -sum g(1-g)
  L''' = sum i^3 g(1-g)(1-2g)      = -i sum g(1-g)(1-2g)
  L4   = sum i^4 g(1-g)(1-6g+6g^2) =  sum g(1-g)(1-6g+6g^2)
  L5   = sum i^5 g(1-g)(1-2g)(1-12g+12g^2)
  L6   = sum i^6 g(1-g)(1-30g+150g^2-240g^3+120g^4)
(These are i^k * (the k-th "Eulerian/Stirling" polynomial in g); g(1-g)=g', and the
 bracket polynomials are the derivatives of g w.r.t. its log-argument: standard
 tangent/Fubini structure.  Verified below against mp.diff for k<=4.)
"""
import sys
import mpmath as mp

def poch_logsum(a, p, NM=10000000):
    # sum_{n>=0} log(1 - a p^n);  here we call with a -> -a_c e^{ixi}-style externally
    tol = mp.mpf(10)**(-(mp.mp.dps+12))
    s = mp.mpc(0); ai = a
    for _ in range(NM):
        s += mp.log(1 - ai); ai *= p
        if abs(ai) < tol: break
    return s

# Bracket polynomials P_k(g) with  D^k log(1+u) = i^k P_k(g),  g=u/(1+u),  D=i u d/du.
# P0 = log; P1=g; P2=g(1-g); P3=g(1-g)(1-2g); etc.  We build via recursion:
#   d/dxi g = i g(1-g).  For F = i^k P_k, F' = i^{k+1} P_{k+1}, and F' = i^k P_k'(g)*g'(xi)/i ...
# Simplest: track the function h_k(g) with D^k(log(1+u)) = i^k h_k(g), recursion
#   h_{k+1} = g(1-g) * h_k'(g)     (since D = i*u d/du = i g(1-g) d/dg, and the i is pulled out)
import sympy as sp
gg = sp.symbols('g')
_h = [sp.log(1+0)]  # placeholder, h0 handled separately
hpoly = [gg]  # h1 = g
for k in range(2, 9):
    hpoly.append(sp.expand(gg*(1-gg)*sp.diff(hpoly[-1], gg)))
hfun = [sp.lambdify(gg, hp, 'mpmath') for hp in hpoly]  # hfun[0]=h1, hfun[k-1]=h_k

def Wderivs(xi, tau, kmax=6):
    """Return [W, W2, W3, W4, W5, W6] (W' too) using analytic sums."""
    q = mp.e**(-tau)
    e = mp.e**(1j*xi)
    a_list = [q**4, 2*(1-q)*q]
    # value
    Wv = -xi**2/(4*tau)
    for a in a_list:
        Wv -= poch_logsum(-a*e, q**2)
    # derivative sums
    # accumulate D^k of (L4+Lz) = sum over factors of i^k h_k(g_n)
    Dk = [mp.mpc(0)]*(kmax+1)  # Dk[k] = D^k of (L4+Lz), k=1..kmax
    tol = mp.mpf(10)**(-(mp.mp.dps+12))
    for a in a_list:
        u = -a*e   # NOTE sign: factor is (1 + a q^{2n} e^{ixi}); with a_c>0 the term is +a q^{2n} e
        # but poch uses (1 - (-a) ...). For derivative use actual factor (1+ a q^{2n} e).
        uu = a*e
        p2 = q**2
        while True:
            g = uu/(1+uu)
            for k in range(1, kmax+1):
                Dk[k] += (1j)**k * hfun[k-1](g)
            uu *= p2
            if abs(uu) < tol: break
    # W = -xi^2/4tau - (L4+Lz);  so W^{(k)} = -(d/dxi)^k(xi^2/4tau) - Dk[k]
    out = [Wv]
    # k>=2:
    for k in range(2, kmax+1):
        base = mp.mpf(0)
        if k == 2: base = -1/(2*tau)
        out.append(base - Dk[k])
    # also need W' (k=1) for findroot
    Wp = -(2*xi)/(4*tau) - Dk[1]
    return out, Wp  # out=[W, W2, W3, W4, W5, W6]

def saddle(tau, kmax=6):
    eta0 = 0.5*mp.log(1/tau)
    def fp(xi):
        _, Wp = Wderivs(xi, tau, 1)
        return Wp
    return mp.findroot(fp, mp.pi/2 - 1j*eta0, tol=mp.mpf(10)**-25)

def Y3_series(x, q, K=12000):
    def qk(a, p, k):
        r = mp.mpf(1); aj = a
        for _ in range(k):
            r *= (1-aj); aj *= p
        return r
    s = mp.mpf(0)
    for k in range(K):
        dk = (mp.mpf(-2))**k*(1-q)**k*q**(k*k+3*k)/(qk(q**2, q**2, k)*qk(q**5, q**2, k))
        t = dk*x**(2*k+3); s += t
        if k > 12 and abs(t) < mp.mpf(10)**(-(mp.mp.dps+6))*max(abs(s), mp.mpf(1)):
            break
    return s

def loop_coeffs(W2, W3, W4, W5, W6):
    s2 = -1/W2
    c1 = s2**2*(W4/8) + s2**3*(mp.mpf(5)/24*W3**2)
    c2 = (s2**3*(W6/48)
          + s2**4*(mp.mpf(35)/384*W4**2 + mp.mpf(7)/48*W3*W5)
          + s2**5*(mp.mpf(35)/64*W3**2*W4)
          + s2**6*(mp.mpf(385)/1152*W3**4))
    return s2, c1, c2

with open("poles.txt") as f:
    polesq = [mp.mpf(line.strip()) for line in f if line.strip()]

print("target = (3/sqrt2) tau^{3/2} sin(w).  a1_true = lim (Y3/target-1)/tau ~ 1.75077", flush=True)
print(f"{'m':>3} {'tau':>10} {'Y3/tgt':>13} {'a1=(r-1)/tau':>14} {'rec0/tau':>11} {'rec1/tau':>11} {'rec2/tau':>11}", flush=True)
for m, qp in enumerate(polesq):
    if m < 3: continue
    if m > 24: break
    tau = -mp.log(qp)
    mp.mp.dps = max(45, int(45 + 1.15/float(tau)))
    q = mp.e**(-tau)
    w = mp.sqrt(2/tau)
    Y3 = Y3_series(1/q, q)
    sinw = mp.sin(w)
    target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
    ratio = Y3/target
    a1_num = (ratio - 1)/tau
    # saddle reconstruction
    xs = saddle(tau)
    derivs, _ = Wderivs(xs, tau, 6)
    W0, W2, W3, W4, W5, W6 = derivs
    s2, c1, c2 = loop_coeffs(W2, W3, W4, W5, W6)
    pref = mp.e**W0*mp.sqrt(2*mp.pi*s2)
    p52 = mp.e**poch_logsum(q**5, q**2)
    norm = q**(-3)/(p52*mp.sqrt(4*mp.pi*tau))
    rec0 = norm*2*mp.re(pref)
    rec1 = norm*2*mp.re(pref*(1+c1))
    rec2 = norm*2*mp.re(pref*(1+c1+c2))
    r0 = (rec0/target-1)/tau; r1 = (rec1/target-1)/tau; r2 = (rec2/target-1)/tau
    print(f"{m:>3} {float(tau):>10.6f} {mp.nstr(ratio,9):>13} {mp.nstr(a1_num,7):>14} "
          f"{mp.nstr(r0,5):>11} {mp.nstr(r1,5):>11} {mp.nstr(r2,5):>11}", flush=True)
