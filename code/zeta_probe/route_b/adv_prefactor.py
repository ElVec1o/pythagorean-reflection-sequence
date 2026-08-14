import mpmath as mp
mp.mp.dps = 40
# prefactor 2q*tau/(1-q) with q=e^{-tau}: expand
tau=mp.mpf('0.001')
q=mp.e**(-tau)
pref=2*q*tau/(1-q)
print("prefactor 2q tau/(1-q) at tau=1e-3:",mp.nstr(pref,12),"  vs 2-tau=",mp.nstr(2-tau,12))
# (2q tau/(1-q)) series: tau/(1-e^{-tau}) = 1 + tau/2 + tau^2/12... times 2 e^{-tau}=2(1-tau+tau^2/2)
# = 2(1-tau+..)(1+tau/2+tau^2/12) = 2(1 -tau/2 -tau^2(...)) = 2 - tau - tau^2/6 ...
import mpmath
# symbolic-ish check via taylor
f=lambda t: 2*mp.e**(-t)*t/(1-mp.e**(-t))
for t in [mp.mpf('0.01'),mp.mpf('0.001')]:
    print(f" tau={float(t)}: pref={mp.nstr(f(t),12)}  (2-tau)={mp.nstr(2-t,12)} diff/tau^2={mp.nstr((f(t)-(2-t))/t**2,6)}")
# So pref = 2 - tau + c*tau^2. colleague said "2-tau+O(tau^2)" OK leading 2-tau correct.
# product pref * (So/Se) where So/Se = 1+tau/2+O(tau^2):
# (2-tau+a tau^2)(1+tau/2+b tau^2) = 2 +tau -tau +... = 2 + (a + 2*b - 1/2... )tau^2
# leading: 2 + 0*tau + O(tau^2).  GOOD: tau term cancels.
print("Conclusion: pref=2-tau+O(tau^2), So/Se=1+tau/2+O(tau^2) => product=2+O(tau^2). tau-term cancels exactly.")
