"""
Precise Euler-Maclaurin expansion of  S(c,xi,tau) = sum_{n>=0} log(1 + e^{-(c+2n) tau} z),  z=e^{i xi}.
Track winding by computing LHS as the SUM of principal-branch logs of each factor (NOT log of product),
which is what the q-Poch actually is (the integrand uses the product, but for the asymptotic comparison
we want the well-defined sum-of-logs, |Im(each)| < pi).

EM formula (Abel-Plana / Euler-Maclaurin), f(n)=log(1+ a e^{-2 tau n} z), a=e^{-c tau}:
  S = INT_0^inf f dn  +  (1/2) f(0)  -  sum_{j>=1} B_{2j}/(2j)! f^{(2j-1)}(0)
where INT_0^inf f dn = -(1/(2 tau)) Li2(-a z)   (EXACT, no approximation in a).
  B2/2! = 1/12,  B4/4! = -1/720.
f'(n) = -2 tau * g,  g = a e^{-2tau n} z/(1+a e^{-2tau n}z);  at 0: g0 = a z/(1+a z).
f'(0) = -2 tau g0.
f'''(0): f' = -2tau g(n).  g' = -2 tau g(1-g).  g'' = -2tau[ g'(1-g) - g g'] = -2tau g'(1-2g)= ( -2tau)^2 g(1-g)(1-2g)... 
Let me just compute derivatives numerically-exactly via the closed forms.
"""
import mpmath as mp
mp.mp.dps = 45

def qpoch_sumlog(a, p, tol=None, NM=4000000):
    # returns sum of principal-branch log(1 - a p^n)  -- well-defined, |Im each|<pi summed (can grow)
    if tol is None: tol = mp.mpf(10)**(-(mp.mp.dps+10))
    s = mp.mpc(0); ai = a
    for _ in range(NM):
        s += mp.log(1 - ai); ai *= p
        if abs(ai) < tol: break
    return s

def S_exact(c, xi, tau):
    q = mp.e**(-tau); z = mp.e**(1j*xi)
    return qpoch_sumlog(-q**c * z, q**2)

def S_EM(c, xi, tau, nterm=3):
    z = mp.e**(1j*xi); a = mp.e**(-c*tau)
    I = -mp.polylog(2, -a*z)/(2*tau)
    f0 = mp.log(1 + a*z)
    g0 = a*z/(1+a*z)
    # f'(0) = -2 tau g0
    fp1 = -2*tau*g0
    out = I + mp.mpf(1)/2*f0 - mp.mpf(1)/12*fp1
    if nterm >= 3:
        # f'''(0): with G(n)=g, g'=-2tau g(1-g); chain. f'=-2tau g => f'''=-2tau g''.
        # g'' = -2tau (g'(1-g) - g g') = -2tau g'(1-2g) = (-2tau)^2 g(1-g)(1-2g)
        gpp = (2*tau)**2 * g0*(1-g0)*(1-2*g0)   # note sign: g'=-2tau g(1-g); g''=(-2tau)^2 g(1-g)(1-2g)
        fp3 = -2*tau*gpp
        out += mp.mpf(1)/720*fp3   # -B4/4! = -(-1/30)/24=+1/720 ; EM term is -B4/4! f''' = +1/720 f'''
    return out, I, f0

print("Re/Im match of EM (sum-of-logs convention), extracting subleading orders:")
for c, xi in [(4, mp.mpf('1.2')), (1, mp.mpf('0.8'))]:
    print(f"=== c={c} xi={xi} ===")
    for tau in [mp.mpf('0.08'),mp.mpf('0.04'),mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005')]:
        ex = S_exact(c,xi,tau)
        em,I,f0 = S_EM(c,xi,tau,3)
        print(f" tau={float(tau):.4f} exact={mp.nstr(ex,14)}  EM={mp.nstr(em,14)}  diff={mp.nstr(ex-em,4)}")
