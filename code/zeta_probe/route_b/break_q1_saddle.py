"""
BREAK-IT Q1: Is the saddle GENUINELY O(1) (bounded) from the dilog branch point, with a
non-degenerate W''!=0, so Ohtsuki's plain Morse-with-remainder (case a) applies and gives a
FINITE remainder?  Or does the hypothesis FAIL (saddle ->singularity, OR W''->0)?

The 1/tau exponent (settled in Q4: ONE dilog from q^4->1, az is O(1)):
   V(xi) = -xi^2/4 + (1/2) Li2(-e^{i xi}).
Branch point of Li2(-e^{i xi}):  -e^{i xi} = 1  => e^{i xi} = -1 => xi = pi (and pi+2pi k).
So the dilog singularity is at xi = pi (real axis).  The leading saddle xi* solves
   V'(xi*) = -xi*/2 - (i/2) log(1+e^{i xi*}) = 0.

We track, as tau->0:
  - the FULL (tau-dependent) saddle xi*(tau) of the real W (incl. az, q^4!=1, EM corrections),
  - distance |xi*(tau) - pi| to the branch point,
  - W''(xi*) (must be !=0 and bounded away from 0 for Morse case a),
  - the rescaled distance  dist / (Gaussian width sqrt(tau)).
If dist stays O(1) AND dist/sqrt(tau)->inf, case (a) hypotheses hold pointwise.
BUT also track Im(xi*): if Im xi* ~ -(1/2)log(1/tau) -> -inf, the saddle RUNS OFF to
complex infinity (NOT toward pi). That is a DIFFERENT failure: the leading saddle is
DEGENERATE (V''=0 there) -- exactly what CONF_leading_symbolic found. Check V'' at leading saddle.
"""
import mpmath as mp
import sympy as sp

gg = sp.symbols('g')
hpoly = [gg]
for k in range(2, 9):
    hpoly.append(sp.expand(gg*(1-gg)*sp.diff(hpoly[-1], gg)))
hfun = [sp.lambdify(gg, hp, 'mpmath') for hp in hpoly]

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+12)); s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1 - ai); ai *= p
    return s

def Wderivs(xi, tau, kmax=4):
    q = mp.e**(-tau); e = mp.e**(1j*xi); a_list = [q**4, 2*(1-q)*q]
    Wv = -xi**2/(4*tau)
    for a in a_list: Wv -= poch_logsum(-a*e, q**2)
    Dk = [mp.mpc(0)]*(kmax+1); tol = mp.mpf(10)**(-(mp.mp.dps+12))
    for a in a_list:
        uu = a*e; p2 = q**2
        while abs(uu) > tol:
            g = uu/(1+uu)
            for k in range(1, kmax+1): Dk[k] += (1j)**k*hfun[k-1](g)
            uu *= p2
    out = [Wv]
    for k in range(2, kmax+1):
        base = -1/(2*tau) if k == 2 else mp.mpf(0)
        out.append(base - Dk[k])
    return out, -(2*xi)/(4*tau) - Dk[1]

def saddle(tau):
    return mp.findroot(lambda xi: Wderivs(xi, tau, 1)[1],
                       mp.pi/2 - 0.5j*mp.log(1/tau), tol=mp.mpf(10)**-25)

print("FULL saddle of W (with 1/tau prefactor): xi*, dist to branch point pi, W''(xi*) [rescaled].")
print("NOTE: W'' here is the FULL second deriv = O(1/tau) (it has the -1/2tau). The shape coeff is tau*W''.")
print(f"{'tau':>9} {'Re xi*':>9} {'Im xi*':>9} {'|xi*-pi|':>9} {'Im/(.5ln1/t)':>12} {'tau*W2':>14} {'dist/sqrt(t)':>12}")
for tau in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.0025'),mp.mpf('0.00125')]:
    mp.mp.dps = max(45, int(45+1.0/float(tau)))
    xs = saddle(tau)
    d,_ = Wderivs(xs, tau, 4); W0,W2,W3,W4 = d
    dist = abs(xs-mp.pi)
    imratio = mp.im(xs)/(0.5*mp.log(1/tau))
    tauW2 = tau*W2
    print(f"{float(tau):>9.5f} {float(mp.re(xs)):>9.5f} {float(mp.im(xs)):>9.5f} "
          f"{float(dist):>9.5f} {float(imratio):>12.5f} {mp.nstr(tauW2,7):>14} "
          f"{float(dist/mp.sqrt(tau)):>12.3f}", flush=True)
print()
print("INTERPRET:")
print(" - If Im xi* ~ -(1/2)log(1/tau) -> -inf (imratio->1): saddle RUNS OFF to -i*inf,")
print("   it does NOT approach pi. dist|xi*-pi| then GROWS (~|Im xi*|).")
print(" - 'tau*W2' is the leading-order shape coefficient. If tau*W2 -> 0, the LEADING")
print("   saddle is DEGENERATE (Morse fails at leading order; need higher-order normal form).")
print(" - dist/sqrt(tau): rescaled distance to singularity. ->inf means Gaussian core is")
print("   clear of the cut (necessary, NOT sufficient, for case a).")
