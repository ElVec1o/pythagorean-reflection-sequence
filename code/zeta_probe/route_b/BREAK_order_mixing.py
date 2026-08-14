"""
BREAK: the SMOKING-GUN test for 'a1 is all-loop'. The adversary claims the bare leading
Gaussian relative error at the pole is O(1) (the 17/16 ~ 0.06 overshoot), i.e. orders MIX:
the loop series runs in sqrt(tau) not tau, because at a travel pole sin(w_m) is NOT extremal --
cos(w_m)=O(sqrt tau) admixes a half-order.

Test cheaply (small poles only, m=3,4,5, modest dps): for each pole compute
  bare leading Gaussian recon0, its rel error e0 = |Y3-recon0|/|Y3|.
  Is e0 ~ const (O(1) in tau)? or ~ tau? Track e0 and e0/tau, e0/sqrt(tau).
If e0 is ~0.06 roughly CONSTANT across poles (not shrinking like tau), the leading Gaussian
ALONE leaves an O(1)-relative defect => the a1 (relative O(tau)) target lives BELOW a layer
the bare saddle misranks => need loop terms AND they mix half-orders. That's the all-loop signature.

Also: control-function sanity. The claimed bound control must be >= the true ~1.751*tau error.
We print true_err = |Y3 - target|/target ( = |a1| tau + ...) and confirm it ~ 1.751 tau,
so any honest C tau^{5/2} bound on |Y3-E| means |Y3-E|/target <= C tau, C>=1.751.
"""
import mpmath as mp
import sympy as sp

gg = sp.symbols('g')
hpoly = [gg]
for k in range(2, 9):
    hpoly.append(sp.expand(gg*(1-gg)*sp.diff(hpoly[-1], gg)))
hfun = [sp.lambdify(gg, hp, 'mpmath') for hp in hpoly]

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+10)); s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1-ai); ai *= p
    return s

def Wderivs(xi, tau, kmax):
    q = mp.e**(-tau); e = mp.e**(1j*xi); a_list = [q**4, 2*(1-q)*q]
    Wv = -xi**2/(4*tau)
    for a in a_list: Wv -= poch_logsum(-a*e, q**2)
    Dk = [mp.mpc(0)]*(kmax+1); tol = mp.mpf(10)**(-(mp.mp.dps+10))
    for a in a_list:
        uu = a*e
        while abs(uu) > tol:
            g = uu/(1+uu)
            for k in range(1, kmax+1): Dk[k] += (1j)**k*hfun[k-1](g)
            uu *= q**2
    out = [Wv]
    for k in range(2, kmax+1):
        base = -1/(2*tau) if k == 2 else mp.mpf(0)
        out.append(base - Dk[k])
    return out, -(2*xi)/(4*tau) - Dk[1]

def saddle(tau):
    return mp.findroot(lambda xi: Wderivs(xi, tau, 1)[1],
                       mp.pi/2 - 0.5j*mp.log(1/tau), tol=mp.mpf(10)**-22)

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

with open("poles.txt") as f:
    polesq = [mp.mpf(l.strip()) for l in f if l.strip()]

print(f"{'m':>3} {'tau':>8} {'true_err/tau':>12} {'e0(bare)':>10} {'e0/tau':>8} {'e0/sqrtT':>9} {'e1':>9} {'e1/tau':>8}")
for m, qp in enumerate(polesq):
    if m < 3 or m > 5: continue
    tau = -mp.log(qp); mp.mp.dps = max(40, int(40 + 1.0/float(tau)))
    q = mp.e**(-tau); w = mp.sqrt(2/tau); sinw = mp.sin(w)
    target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
    Y3 = Y3_series(1/q, q)
    true_err = abs(Y3-target)/abs(target)   # ~ |a1| tau
    xs = saddle(tau); Wd,_ = Wderivs(xs, tau, 4)
    s2=-1/Wd[1]
    pref = mp.e**Wd[0]*mp.sqrt(2*mp.pi*s2)
    p52 = mp.e**poch_logsum(q**5, q**2)
    norm = q**(-3)/(p52*mp.sqrt(4*mp.pi*tau))
    rec0 = norm*2*mp.re(pref)
    c1 = s2**2*(Wd[3]/8) + s2**3*(mp.mpf(5)/24*Wd[2]**2)
    rec1 = norm*2*mp.re(pref*(1+c1))
    e0 = abs(Y3-rec0)/abs(Y3); e1 = abs(Y3-rec1)/abs(Y3)
    print(f"{m:>3} {float(tau):>8.5f} {float(true_err/tau):>12.5f} {float(e0):>10.5f} "
          f"{float(e0/tau):>8.3f} {float(e0/mp.sqrt(tau)):>9.4f} {float(e1):>9.6f} {float(e1/tau):>8.4f}", flush=True)
print()
print("true_err/tau should -> 1.751 (the a1 magnitude). CONTROL SANITY: any bound on |Y3-E|")
print("must exceed 1.751*tau*target; a C tau^{5/2} bound => C>=1.751 (a1).")
print("If e0/tau GROWS while e0/sqrtT ~ const => bare gaussian err is O(sqrt tau): orders mix (all-loop).")
print("If e1/tau ~ const small => 1-loop reaches relative O(tau) (loop helps); compare its const to a1 gap.")
