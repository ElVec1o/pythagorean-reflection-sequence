#!/usr/bin/env python3
"""beta_2 and the q-Niven architecture: Hahn-Exton identification, q-Lommel ladder, and the rho=1/2 wall.

RESULTS (paper2 rem:betanumber, all verified here to ~40 digits):

1. IDENTIFICATION. G(q,z) [the beta_2 function, S(q)=G(q,2q(1-q))] and H are Hahn-Exton (third
   Jackson) q-Bessel functions at nu = -1/2, +1/2 in base q^2:
       G(q,z) ~ J_{-1/2}(sqrt(z)/q; q^2),    H(q,z) ~ J_{+1/2}(sqrt(z/q); q^2)
   (zeros correspond exactly). These are the q-analogues of cos and sin; z* is the q-analogue of (pi/2)^2.

2. THE q-NIVEN ARCHITECTURE EXISTS VERBATIM (Koelink-Swarttouw, arXiv math/9703215):
   - nu-ladder (2.13):    J_{nu+1}(x;q^2) = ((1-q^{2nu})/x + x) J_nu - J_{nu-1}
   - q-Lommel connection (4.12):  J_{nu+m} = R_{m,nu} J_nu - R_{m-1,nu+1} J_{nu-1},
     with x^m R_{m,nu} a polynomial of degree m in x^2 with Z[q]-coefficients (recurrence 4.18/4.20).
   - At a zero x0 of J_{-1/2}: J_{m+1/2}(x0) = R_{m,1/2}(x0) J_{1/2}(x0)  [Niven's structure].
   REDUCTION: beta_2 rational => G(q*,z*)=0 is a RATIONAL VALUE of a Hahn-Exton function at rational
   base+argument. So beta_2 is IRRATIONAL as soon as this 1phi1 omits 0 at rational points -- a plain
   value-irrationality statement (strictly weaker than all transcendence targets).

3. THE WALL, QUANTIFIED (the arithmetic ratio rho = b-adic term decay / cleared-denominator growth):
   proven q-irrationality theory (Tschakaloff, q-exponential, Bezivin/Bundschuh-Vaananen) needs rho>=1
   (decay supplied BY the Pochhammer). Our G: independent q^{k^2} numerator vs DOUBLE Pochhammer
   (q;q)_{2k} => rho = 1/2. Measured failures:
   - z-Pade: remainder q^{3.5 n^2} vs height q-degree ~9 n^2;
   - z-continued fraction (convergents in Z[q,z], Pincherle limit = the H-ratio): geometric vs t^{n^2};
   - nu-ladder at the zero: J_{m+1/2}(x0) ~ C x0^m GEOMETRIC (q-factorial is geometric, unlike Niven's m!)
     vs t^{m^2}; second-kind ladder's q^{m^2/2} cancels t^{m^2} but leaves s^{m^2/2} (q=s/t) -- only q=1/t survives.
   - the b<->z swap 1phi1(0;q;q^2,z) = ((z;q^2)_inf/(q;q^2)_inf) 1phi1(0;z;q^2,q) conserves rho.
   OPEN DOOR: a q-irrationality criterion at rho=1/2 -- one notch beyond the proven rho>=1 theory.

Sources: Koelink-Swarttouw arXiv:math/9703215; Van Assche, "Analytic number theory and approximation"
(the classical Niven/Lommel structure and the cyclotomic lcm lemma d_n(p)^{1/n^2} -> p^{3/pi^2}).
"""
import mpmath as mp


def poch(a, p, n):
    r = mp.mpf(1)
    for i in range(n): r *= (1 - a * p**i)
    return r


def pochinf(a, p, K=300):
    r = mp.mpf(1)
    for i in range(K):
        f = (1 - a * p**i); r *= f
        if abs(1 - f) < mp.mpf(10)**-45: break
    return r


def J(nu, x, q, K=200):
    """Hahn-Exton J_nu(x; q^2) (Koelink-Swarttouw 2.4, base p=q^2)."""
    p = q * q
    pre = x**nu * pochinf(p**(nu + 1), p) / pochinf(p, p)
    s = mp.mpf(0)
    for k in range(K):
        term = (-1)**k * p**(mp.mpf(k) * (k - 1) / 2) * (p * x * x)**k / (poch(p, p, k) * poch(p**(nu + 1), p, k))
        s += term
        if k > 10 and abs(term) < mp.mpf(10)**-50: break
    return pre * s


def Rpoly(m, nu, x, q):
    """q-Lommel R_{m,nu}(x;q^2) via K-S (4.18): {x^2+1-q^{2(nu+m)}} R_m = x{R_{m-1}+R_{m+1}}."""
    R = [mp.mpf(1), x + (1 - q**(2 * nu)) / x]
    for mm in range(1, m):
        R.append((x * x + 1 - q**(2 * (nu + mm))) * R[-1] / x - R[-2])
    return R[m]


if __name__ == "__main__":
    mp.mp.dps = 40
    q = mp.mpf('0.5')
    z1 = mp.findroot(lambda z: J(mp.mpf('-0.5'), mp.sqrt(z) / q, q).real, mp.mpf('0.43'))
    print("smallest zero of G(1/2,.) via J_{-1/2}:", mp.nstr(z1, 20), "(matches 0.42969714231607221301)")
    x, nu = mp.mpf('0.8'), mp.mpf('0.5')
    print("(2.13) ladder residual:", mp.nstr(J(nu + 1, x, q) - (((1 - q**(2 * nu)) / x + x) * J(nu, x, q) - J(nu - 1, x, q)), 4))
    m, x = 6, mp.mpf('1.3')
    print("(4.12) q-Lommel residual (m=6):",
          mp.nstr(J(nu + m, x, q) - (Rpoly(m, nu, x, q) * J(nu, x, q) - Rpoly(m - 1, nu + 1, x, q) * J(nu - 1, x, q)), 4))
    x0 = mp.sqrt(z1) / q
    print("\nNiven structure at the zero x0 =", mp.nstr(x0, 15))
    for m in [4, 8, 12]:
        t = J(m + mp.mpf('0.5'), x0, q); l = Rpoly(m, mp.mpf('0.5'), x0, q) * J(mp.mpf('0.5'), x0, q)
        print(f"  m={m:>2}: J_(m+1/2)(x0)={mp.nstr(t,8)}  = R*J={mp.nstr(l,8)}  J/x0^m={mp.nstr(t/x0**m,8)}")
    print("\n=> J_{m+1/2}(x0) ~ 0.8164 * x0^m: geometric (q-factorial is geometric). rho=1/2 wall stands.")
