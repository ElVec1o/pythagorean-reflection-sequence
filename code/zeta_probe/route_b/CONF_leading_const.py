"""
Analytic structure of the LEADING saddle: confirm the saddle xi*, the exponent W0,
and that the 2-saddle leading Gaussian reproduces (3/sqrt2) tau^{3/2} sin(w) with
constant 1/(4 sqrt2) after the prefactor norm.  Also extract the leading-order
analytic form of xi*, W0, W2 to feed a closed-form a1 attempt.

This runs at MODERATE tau (no pole), where everything is cheap, to study scaling.
"""
import mpmath as mp
import sympy as sp

gg = sp.symbols('g')
hpoly = [gg]
for k in range(2, 9):
    hpoly.append(sp.expand(gg*(1-gg)*sp.diff(hpoly[-1], gg)))
hfun = [sp.lambdify(gg, hp, 'mpmath') for hp in hpoly]

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+12))
    s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1 - ai); ai *= p
    return s

def Wderivs(xi, tau, kmax=2):
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
        base = mp.mpf(0)
        if k == 2: base = -1/(2*tau)
        out.append(base - Dk[k])
    Wp = -(2*xi)/(4*tau) - Dk[1]
    return out, Wp

def saddle(tau):
    eta0 = 0.5*mp.log(1/tau)
    return mp.findroot(lambda xi: Wderivs(xi, tau, 1)[1],
                       mp.pi/2-1j*eta0, tol=mp.mpf(10)**-30)

mp.mp.dps = 60
print("Leading-saddle structure.  Check: -W0_real_lead, Im W0 (phase), and 1/(4sqrt2)=", mp.nstr(1/(4*mp.sqrt(2)),12))
print(f"{'tau':>10} {'Re xi*':>12} {'Im xi*':>12} {'Re W0':>14} {'Im W0':>14} {'(-W0*tau)':>16}")
for tau in [mp.mpf('0.05'), mp.mpf('0.02'), mp.mpf('0.01'), mp.mpf('0.005')]:
    xs = saddle(tau)
    d, _ = Wderivs(xs, tau, 2)
    W0, W2 = d
    # leading: Re(W0) ~ -c/tau^? ;  print -W0*tau to see the dilog "volume"
    print(f"{float(tau):>10.5f} {float(mp.re(xs)):>12.6f} {float(mp.im(xs)):>12.6f} "
          f"{float(mp.re(W0)):>14.5f} {float(mp.im(W0)):>14.5f} {mp.nstr(mp.re(W0)*tau,10):>16}")

# Now confirm: the leading 2-saddle Gaussian, after the norm prefactor, gives the
# constant 1/(4 sqrt2) in front of tau^{3/2} sin w  AT A POLE-LIKE phase.
# We test: define ratio_lead = [norm * 2Re(e^{W0} sqrt(2pi s2))] / ( (3/sqrt2) tau^{3/2} sin w )
# at general tau (not pole) the sin w is generic; ratio_lead -> 1 means leading captured.
print()
print("Leading-Gaussian / target ratio (should -> 1 as tau->0; deviation O(sqrt tau) off-pole, O(tau) at pole):")
print(f"{'tau':>10} {'lead/target':>16}")
for tau in [mp.mpf('0.05'), mp.mpf('0.02'), mp.mpf('0.01'), mp.mpf('0.005'), mp.mpf('0.0025')]:
    q = mp.e**(-tau); w = mp.sqrt(2/tau)
    xs = saddle(tau)
    d, _ = Wderivs(xs, tau, 2)
    W0, W2 = d; s2 = -1/W2
    pref = mp.e**W0*mp.sqrt(2*mp.pi*s2)
    p52 = mp.e**poch_logsum(q**5, q**2)
    norm = q**(-3)/(p52*mp.sqrt(4*mp.pi*tau))
    lead = norm*2*mp.re(pref)
    target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*mp.sin(w)
    print(f"{float(tau):>10.5f} {mp.nstr(lead/target,12):>16}")
