"""
TASK D1 (2026-06-22, Vico): RIGOROUS Laplace/stationary-phase asymptotic of L(1/q).

Integral rep (fact 6) -- CORRECTED PREFACTOR (re-derived from Hubbard-Stratonovich; the prefactor
stated in fact 6, 2^{-7/4}tau^{3/4}, is WRONG by a factor sqrt(2 tau); correct is 2^{-9/4}tau^{1/4}):
    L(x) = 2^{-9/4} tau^{1/4} x^{-3/2} * INT,
    INT  = int_{-inf}^{inf} e^{-u^2/(4 tau)} J_{3/2}(x w e^{i u/2}) e^{-3 i u/4} du,   w=sqrt(2/tau).
Substitution u = sqrt(2 tau) t  (=> e^{-u^2/(4tau)} = e^{-t^2/2}, du = sqrt(2 tau) dt, u/2 = s t, s:=sqrt(tau/2)):
    INT = sqrt(2 tau) int e^{-t^2/2} J_{3/2}(M e^{i s t}) e^{-(3/2) i s t} dt,   M := x w = w e^{tau} (x=1/q=e^{tau}).

EXACT BRANCH DECOMPOSITION (no hand error): J_{3/2}(a)=sqrt(2/(pi a))(sin a/a - cos a), a=M e^{i s t},
write via e^{+-ia}.  Key identities (since M s = e^{tau} =: E):
    e^{-i a} = e^{-iM} e^{E t} e^{R(t)} e^{-i P(t)},   e^{+i a} = e^{+iM} e^{-E t} e^{-R(t)} e^{+i P(t)},
    R(t) = M sin(s t) - E t = -(E/6) s^2 t^3 + O(s^4)         [REAL, O(tau)]
    P(t) = M cos(s t) - M   = -(E/2) s   t^2 + O(s^3)         [O(sqrt tau) phase]
The two cores e^{-t^2/2 +- E t} are shifted Gaussians (saddles t = +-E). Averaging the remaining
slowly-varying factor over the Gaussian (Hermite moments <s^n>=(n-1)!!) gives the polar amplitude
    A_- := <Gm(E+u)>_u = (amp0)(-1/2) rho e^{-i delta},   A_+ = conj(A_-),  amp0=sqrt(2/(pi M)).
NUMERICALLY-PINNED rho, delta (rational coeffs identified by PSLQ-grade Richardson, s=sqrt(tau/2)):
    delta = 2 s - (11/4) s^3 + O(s^5)  =  sqrt(2 tau) - (11/4)(tau/2)^{3/2} + ...
    rho   = exp( -(23/12) s^2 + O(s^4) ) = exp( -(23/24) tau + ... )
Assembling  INT = sqrt(2tau)*e^{E^2/2} sqrt(2pi)*amp0*(-1)*rho*cos(M+delta), and pref*..., the amplitude
collapses to  -(1/2) tau e^{-2tau} e^{e^{2tau}/2} rho.  FINAL EXPLICIT ASYMPTOTIC:

    L(1/q) = -(1/2) tau e^{-2tau} exp(e^{2tau}/2) exp(-(23/24)tau) cos(Phi_eff) + O(tau^{5/2}),
    Phi_eff = w e^{tau} + sqrt(2 tau) - (11/4)(tau/2)^{3/2},   w = sqrt(2/tau).

LEADING (tau->0):  L(1/q) ~ -(1/2) e^{1/2} tau cos(w e^{tau}).   The constant is e^{1/2} (NOT 36/35;
36/35 is the FULL Y3=3x^3[L+tau G] pole-assembly value, fact 9 -- a DIFFERENT object).
"""
import mpmath as mp

def L_exact(q, x):
    tau = -mp.log(q); K = int(25/mp.sqrt(tau)) + 90; tot = mp.mpf(0)
    for k in range(K+1):
        d = mp.mpf(1)
        for j in range(2*k+3, 0, -2): d *= j
        tot += (-1)**k * q**(k*k) * (x*x/tau)**k / (mp.factorial(k)*d)
    return tot

def L_asymp(tau):
    w = mp.sqrt(2/tau); s = mp.sqrt(tau/2)
    Amp = -(mp.mpf(1)/2)*tau*mp.e**(-2*tau)*mp.e**(mp.e**(2*tau)/2)*mp.e**(-(mp.mpf(23)/24)*tau)
    Phi = w*mp.e**tau + mp.sqrt(2*tau) - (mp.mpf(11)/4)*s**3
    return Amp*mp.cos(Phi)

def L_asymp_leading(tau):   # bare leading, for the "amplitude e^{1/2}" statement
    w = mp.sqrt(2/tau)
    return -(mp.mpf(1)/2)*mp.e**(mp.mpf(1)/2)*tau*mp.cos(w*mp.e**tau)

if __name__ == "__main__":
    print("="*84)
    print("D1: L(1/q) asymptotic vs exact sum.  reldiff and absdiff/tau^{5/2} (-> bounded => O(tau^{5/2})).")
    print("="*84)
    print(f"{'tau':>10} {'L_exact':>17} {'L_asymp':>17} {'reldiff':>11} {'absdiff/tau^2.5':>15}")
    for tv in ['0.01','0.005','0.0025','0.02','0.001','0.0005']:
        tau = mp.mpf(tv); mp.mp.dps = 40 + int(2.5*mp.sqrt(2/tau))
        tau = mp.mpf(tv); q = mp.e**(-tau); x = 1/q
        Le = L_exact(q,x); La = L_asymp(tau)
        print(f"{tv:>10} {mp.nstr(Le,11):>17} {mp.nstr(La,11):>17} {mp.nstr((La-Le)/Le,5):>11} {mp.nstr((La-Le)/tau**mp.mpf('2.5'),5):>15}")
    mp.mp.dps=50
    print("\nLeading-order check  L ~ -(1/2)e^{1/2} tau cos(w e^{tau})  (e^{1/2}=%.6f):" % float(mp.e**mp.mpf('0.5')))
    for tv in ['0.005','0.0025','0.00125']:
        tau=mp.mpf(tv);q=mp.e**(-tau);x=1/q
        print(f"  tau={tv}: L_exact/[-(1/2)tau cos(w e^tau)] = {mp.nstr(L_exact(q,x)/(-(mp.mpf(1)/2)*tau*mp.cos(mp.sqrt(2/tau)*mp.e**tau)),8)}  (-> e^{{1/2}})")
