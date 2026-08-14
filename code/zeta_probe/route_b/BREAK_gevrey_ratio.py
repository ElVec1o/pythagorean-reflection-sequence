"""
BREAK (Gevrey settle): at ONE small pole (m=3), compute loop coeffs c_0..c_8 and the ratio
|c_{L+1}/c_L|.  If it grows ~ linearly in L (factorial / Gevrey-1), the saddle loop expansion
is a DIVERGENT asymptotic series -> truncation cannot reach a1 exactly -> 'state-integral closes
a1' is REFUTED.  Single pole, dps fixed modest, W-derivs to order 18.  Fast.
"""
import mpmath as mp
import sympy as sp
from collections import defaultdict

gg = sp.symbols('g')
hpoly = [gg]
for k in range(2, 21):
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

def loop_coeffs(Wd, s2, Lmax):
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

qp = polesq[3]   # m=3
tau = -mp.log(qp); mp.mp.dps = 90
xs = mp.findroot(lambda xi: Wderivs(xi, tau, 1)[1], mp.pi/2 - 0.5j*mp.log(1/tau), tol=mp.mpf(10)**-40)
Lmax = 8
Wd, _ = Wderivs(xs, tau, 2*Lmax+2)
s2 = -1/Wd[1]
cL = loop_coeffs(Wd, s2, Lmax)
print(f"m=3, tau={float(tau):.6f}, dps={mp.mp.dps}")
print(f"{'L':>3} {'|c_L|':>14} {'|c_L/c_{L-1}|':>14} {'ratio/L':>10}")
for L in range(Lmax+1):
    r = abs(cL[L]/cL[L-1]) if L>0 and abs(cL[L-1])>0 else mp.mpf(0)
    print(f"{L:>3} {mp.nstr(abs(cL[L]),8):>14} {mp.nstr(r,8):>14} {(mp.nstr(r/L,6) if L>0 else ''):>10}", flush=True)
print()
print("If |c_L/c_{L-1}| GROWS ~ linearly in L (ratio/L -> const), the loop series is Gevrey-1")
print("(factorially divergent) => finite truncation CANNOT equal a1 => Ohtsuki finite-loop")
print("does NOT close a1; need Borel/uniform-normal-form (=lem:cos standing). If ratio plateaus,")
print("series converges and a1 IS a finite resummation.")
