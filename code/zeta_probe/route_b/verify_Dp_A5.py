"""
Part 5: TRUE L_m decay  +  cross-check the Touchard/Poisson alternative majorant.

(a) TRUE sup|L_m| from the exact layer code: ratio L_m/L_{m-1} ~ c sqrt(tau)?
    sup|L_m| ~ tau^{(m+1)/2}?
(b) Does the Touchard bound sup|L_m| <= (2/m!) tau^{2m} E[C2t(N/2)^m] dominate TRUE?
(c) Is sum_{m>=2} 2 E[Psi(tau^2 C2t(N/2))] = O(tau) and CONVERGENT (not asymptotic)?
    This is the real test of whether the colleague's "divergent crude series" is the
    ONLY available crude bound, or whether the Touchard device already gives a convergent one.
"""
import mpmath as mp, sympy as sp
mp.mp.dps = 40
jj = sp.symbols('j')
C2t = (jj+1)*(2*jj+3)*(4*jj+5)/72

def alpha(k, t): return 2/(mp.e**((k+1)*t)-1)
def buildR(t, J):
    rho = []; prod = mp.mpf(1)
    for q in range(J):
        a1 = alpha(1+2*q, t); that = (2/t)**(q+1)/mp.factorial(2*q+2)
        rho.append(a1*prod/that); prod *= (a1-alpha(2+2*q, t))
    return [-mp.log(rho[q])-(q+1)*t for q in range(J)]

def E_poisson(Qpoly, w, trunc):
    Qf = sp.lambdify(jj, Qpoly, 'mpmath'); s = mp.mpf(0); logw = mp.log(w)
    for n in range(trunc):
        lp = -w + n*logw - mp.loggamma(n+1)
        if lp < -320 and n > float(w): break
        s += mp.e**lp * Qf(mp.mpf(n)/2)
    return s

print("="*70)
print("(a) TRUE sup|L_m| decay  +  (b) Touchard bound domination")
print("="*70)
for tval in ['0.02', '0.005', '0.001']:
    t = mp.mpf(tval); w = mp.sqrt(2/t); J = int(2.3*float(w))+50
    R = buildR(t, J); Rm1 = lambda q: mp.mpf(0) if q == 0 else R[q-1]
    base = [(-1)**(q+1)/mp.factorial(2*q) for q in range(J)]
    ej = [mp.e**(-q*t) for q in range(J)]; ejp1 = [mp.e**(-(q+1)*t) for q in range(J)]
    print(f"  tau={tval}, w={float(w):.1f}:")
    prev = None
    for m in range(1, 8):
        fm = mp.factorial(m)
        Lc = [(ej[q]*(-Rm1(q))**m - ejp1[q]*(-R[q])**m)/fm*base[q] for q in range(J)]
        Nn = 1200; sup = mp.mpf(0)
        for kk in range(Nn+1):
            u = w*mp.mpf(kk)/Nn; u2 = u*u; pw = mp.mpf(1); s = mp.mpf(0)
            for q in range(J): s += Lc[q]*pw; pw *= u2
            sup = max(sup, abs(s))
        bnd = 2/fm*t**(2*m)*E_poisson(sp.expand(C2t**m), w, int(float(w))*5+150)
        ratio = (sup/prev) if prev else mp.mpf(0)
        prev = sup
        dom = "OK" if bnd >= sup*(1-mp.mpf('1e-9')) else "VIOLATION"
        print(f"    m={m}: TRUE sup|L_m|/tau={float(sup/t):.4e}  L_m/L_(m-1)={float(ratio):.4f}"
              f"  Touchard_bnd/tau={float(bnd/t):.4e}  [{dom}]")

print()
print("="*70)
print("(c) MASTER: 2 E[Psi(tau^2 C2t(N/2))]  -- convergent and O(tau)?")
print("   plus the COLLEAGUE-style crude (w/2)^p-dressed sum for comparison")
print("="*70)
def master(t, w, trunc):
    C2f = sp.lambdify(jj, C2t, 'mpmath'); s = mp.mpf(0); logw = mp.log(w)
    for n in range(trunc):
        lp = -w + n*logw - mp.loggamma(n+1)
        if lp < -320 and n > float(w): break
        x = t**2 * C2f(mp.mpf(n)/2)
        s += mp.e**lp * (mp.e**x - 1 - x)
    return 2*s
for tval in ['0.02', '0.005', '0.001', '0.0001', '1e-5']:
    t = mp.mpf(tval); w = mp.sqrt(2/t)
    mb = master(t, w, int(float(w))*6+200)
    print(f"  tau={tval:>7}: MASTER/tau = {float(mb/t):.6f}")
