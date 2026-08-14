"""
Decisive scaling test: at travel poles, what is the relative-error ORDER of the
L-loop saddle reconstruction?  If rel-err(L-loop) ~ tau^{(L+1)/2}  (half-integer
ladder), the loop series at the pole is in sqrt(tau), orders MIX, and no finite-loop
truncation gives a clean C tau^{5/2} absolute (= relative O(tau)) remainder without
also pinning the half-integer cross-terms -- i.e. a1 is all-loop, not one Bernoulli term.

We compute, per pole:  e_L = |Y3 - Y3_recon(L)| / |Y3|  for L=0,1,2,3 (3-loop added),
and e_L / tau^{(L+1)/2}.
"""
import mpmath as mp
import sympy as sp

gg = sp.symbols('g')
hpoly = [gg]
for k in range(2, 11):
    hpoly.append(sp.expand(gg*(1-gg)*sp.diff(hpoly[-1], gg)))
hfun = [sp.lambdify(gg, hp, 'mpmath') for hp in hpoly]

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+12))
    s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1 - ai); ai *= p
    return s

def Wderivs(xi, tau, kmax=8):
    q = mp.e**(-tau); e = mp.e**(1j*xi)
    a_list = [q**4, 2*(1-q)*q]
    Wv = -xi**2/(4*tau)
    for a in a_list:
        Wv -= poch_logsum(-a*e, q**2)
    Dk = [mp.mpc(0)]*(kmax+1)
    tol = mp.mpf(10)**(-(mp.mp.dps+12))
    for a in a_list:
        uu = a*e; p2 = q**2
        while abs(uu) > tol:
            g = uu/(1+uu)
            for k in range(1, kmax+1):
                Dk[k] += (1j)**k*hfun[k-1](g)
            uu *= p2
    out = [Wv]
    for k in range(2, kmax+1):
        base = -1/(2*tau) if k == 2 else mp.mpf(0)
        out.append(base - Dk[k])
    Wp = -(2*xi)/(4*tau) - Dk[1]
    return out, Wp

def saddle(tau):
    eta0 = 0.5*mp.log(1/tau)
    return mp.findroot(lambda xi: Wderivs(xi, tau, 1)[1], mp.pi/2-1j*eta0, tol=mp.mpf(10)**-30)

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

def loop_list(W2, W3, W4, W5, W6, W7, W8):
    s2 = -1/W2
    c1 = s2**2*(W4/8) + s2**3*(mp.mpf(5)/24*W3**2)
    c2 = (s2**3*(W6/48) + s2**4*(mp.mpf(35)/384*W4**2 + mp.mpf(7)/48*W3*W5)
          + s2**5*(mp.mpf(35)/64*W3**2*W4) + s2**6*(mp.mpf(385)/1152*W3**4))
    # 3-loop standard Laplace coefficient (DLMF / Wojciechowski c3):
    c3 = (s2**4*(W8/384)
          + s2**5*(mp.mpf(7)/192*W4*W6 + mp.mpf(7)/240*W3*W7 + mp.mpf(7)/640*W5**2)
          + s2**6*(mp.mpf(35)/128*W4**3 + mp.mpf(35)/64*W3*W4*W5 + mp.mpf(7)/96*W3**2*W6)  # approx grouping
          )
    return s2, [c1, c2, c3]

with open("poles.txt") as f:
    polesq = [mp.mpf(line.strip()) for line in f if line.strip()]

print("e_L = |Y3 - recon(L)|/|Y3| at poles.  Show e_L / tau^{(L+1)/2}.")
print(f"{'m':>3} {'tau':>10} {'e0/tau^.5':>11} {'e1/tau':>11} {'e2/tau^1.5':>12} {'e3/tau^2':>11}")
for m, qp in enumerate(polesq):
    if m < 3: continue
    if m > 9: break
    tau = -mp.log(qp)
    mp.mp.dps = max(45, int(45 + 1.15/float(tau)))
    q = mp.e**(-tau); w = mp.sqrt(2/tau)
    Y3 = Y3_series(1/q, q)
    p52 = mp.e**poch_logsum(q**5, q**2)
    norm = q**(-3)/(p52*mp.sqrt(4*mp.pi*tau))
    xs = saddle(tau)
    d, _ = Wderivs(xs, tau, 8)
    W0, W2, W3, W4, W5, W6, W7, W8 = d
    s2, cs = loop_list(W2, W3, W4, W5, W6, W7, W8)
    pref = mp.e**W0*mp.sqrt(2*mp.pi*s2)
    partial = mp.mpf(1)
    recs = [norm*2*mp.re(pref*partial)]  # L=0
    for c in cs:
        partial = partial + c
        recs.append(norm*2*mp.re(pref*partial))
    es = [abs(Y3 - r)/abs(Y3) for r in recs]
    print(f"{m:>3} {float(tau):>10.6f} "
          f"{mp.nstr(es[0]/tau**mp.mpf('0.5'),5):>11} "
          f"{mp.nstr(es[1]/tau,5):>11} "
          f"{mp.nstr(es[2]/tau**mp.mpf('1.5'),5):>12} "
          f"{mp.nstr(es[3]/tau**2,5):>11}", flush=True)
