"""
Part 3: RIGOROUS FAMILY bound and J(W,rho) sub-Gaussian bound.

Cauchy: D_p(W) = 2^{-p} f^{(p)}(log W), f(t)=cos(e^t).
 |f^{(p)}(t)| <= p! rho^{-p} (1/2pi) int_{-pi}^{pi} |cos(W e^{rho e^{i psi}})| dpsi.
 |cos z| <= cosh(Im z) <= e^{|Im z|}; Im(W e^{rho e^{i psi}}) = W G(psi),
   G(psi)=Im(e^{rho e^{i psi}}) = sum_{n>=1} (rho^n/n!) sin(n psi).
 J(W,rho) := (1/2pi) int e^{W G(psi)} dpsi   [using psi->-psi symmetry to drop |.|]

Claims:
 (4a) |D_p(W)| <= 2^{-p} p! rho^{-p} J(W,rho)  -- the raw Cauchy bound (rigorous), any rho.
 (4b) J(W,rho) <= exp((W^2/2)(I0(2rho)-1))    SAFE  (claim worst ratio ~0.9975)
 (4c) J(W,rho) <= exp((W^2/4)(I0(2rho)-1))    TIGHT (holds but proof gap)
 (5)  inf_rho 2^{-p} p! rho^{-p} exp((W^2/2)(I0(2rho)-1)) >= true sup_[0,w]|D_p|   (dominates)
 (6)  E[G^{2k}] <= (2k)!/(2^k k!) (2 sigma^2)^k, sigma^2=(1/2)(I0(2rho)-1)  -- sub-Gaussian moment
 (7)  Bessel: I_m(c) <= (c/2)^m e^{c^2/4}/m! ; I0(c)<=e^{c^2/4}.
"""
import mpmath as mp
mp.mp.dps = 40

def G(psi, rho, NN=80):
    return sum((rho**n/mp.factorial(n))*mp.sin(n*psi) for n in range(1, NN+1))

def Jint(W, rho, M=4000):
    # (1/2pi) int_{-pi}^{pi} e^{W G(psi)} dpsi  by trapezoid (periodic -> spectral acc)
    s = mp.mpf(0)
    for k in range(M):
        psi = -mp.pi + 2*mp.pi*mp.mpf(k)/M
        s += mp.e**(W*G(psi, rho))
    return s/M

def Jint_abs(W, rho, M=4000):
    # the TRUE Cauchy integrand (1/2pi) int |cos(W e^{rho e^{i psi}})| dpsi
    s = mp.mpf(0)
    for k in range(M):
        psi = -mp.pi + 2*mp.pi*mp.mpf(k)/M
        z = W*mp.e**(rho*mp.e**(1j*psi))
        s += abs(mp.cos(z))
    return s/M

print("="*70)
print("(4b) J(W,rho) <= exp((W^2/2)(I0(2rho)-1))  [SAFE]")
print("="*70)
worst = mp.mpf(0); worst_at = None
for W in [mp.mpf(x) for x in ['0.5','2','5','10','20','40','80']]:
    for rho in [mp.mpf(x) for x in ['0.05','0.2','0.5','1','2','3','4']]:
        J = Jint(W, rho)
        rhs = mp.e**((W*W/2)*(mp.besseli(0, 2*rho)-1))
        r = J/rhs
        if r > worst: worst = r; worst_at = (float(W), float(rho), float(r))
print(f"  worst J/RHS_safe = {float(worst):.6f}  at (W,rho)={worst_at}")

print()
print("(4c) tighter  J(W,rho) <= exp((W^2/4)(I0(2rho)-1))  [TIGHT, proof-gap]")
worstt = mp.mpf(0); worstt_at = None
for W in [mp.mpf(x) for x in ['0.5','2','5','10','20','40','80']]:
    for rho in [mp.mpf(x) for x in ['0.05','0.2','0.5','1','2','3','4']]:
        J = Jint(W, rho)
        rhs = mp.e**((W*W/4)*(mp.besseli(0, 2*rho)-1))
        r = J/rhs
        if r > worstt: worstt = r; worstt_at = (float(W), float(rho), float(r))
print(f"  worst J/RHS_tight = {float(worstt):.6f}  at (W,rho)={worstt_at}")

print()
print("(4a) raw Cauchy: J_abs (true integrand) vs J (the e^{WG} majorant) -- J >= J_abs?")
ok = True
for W in [mp.mpf('5'), mp.mpf('20')]:
    for rho in [mp.mpf('0.5'), mp.mpf('2')]:
        Ja = Jint_abs(W, rho); J = Jint(W, rho)
        ok &= (J >= Ja*(1-mp.mpf('1e-9')))
        print(f"   W={float(W):.0f} rho={float(rho):.1f}: J_abs={float(Ja):.4g} <= J={float(J):.4g}  {'OK' if J>=Ja else 'VIOLATION'}")

print()
print("(7) Bessel inequalities  I_m(c) <= (c/2)^m e^{c^2/4}/m!  and I0(c)<=e^{c^2/4}")
okB = True
for ci in range(1, 81):
    c = mp.mpf(ci)/10
    okB &= mp.besseli(0, c) <= mp.e**(c*c/4)*(1+mp.mpf('1e-30'))
    for m in range(0, 8):
        lhs = mp.besseli(m, c); rhs = (c/2)**m * mp.e**(c*c/4)/mp.factorial(m)
        okB &= lhs <= rhs*(1+mp.mpf('1e-30'))
print(f"   I_m(c)<=(c/2)^m e^{{c^2/4}}/m! and I0(c)<=e^{{c^2/4}} for c<=8,m<=7: {'HOLDS' if okB else 'FAILS'}")
