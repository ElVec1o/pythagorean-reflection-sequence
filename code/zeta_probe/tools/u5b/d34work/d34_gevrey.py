import sympy as sp
# The c_k are KNOWN exact rationals; the dev asymptotic series is sum c_k / w^{2k-1}, w=sqrt(2/tau).
# In tau: 1/w^{2k-1} = (tau/2)^{k-1/2}*sqrt(2)... so dev(tau) ~ sum c_k (tau/2)^{k-1/2} * sqrt2  (half-integer powers!)
# Check Gevrey growth / divergence rate of c_k (given in problem):
ck = [sp.Rational(1,18), sp.Rational(-41,600), sp.Rational(-1915,7056),
      sp.Rational(-18617,51840), sp.Rational(-942829,29272320)]
print("c_k exact:", [str(c) for c in ck])
import mpmath as mp
mp.mp.dps=30
vals=[abs(mp.mpf(c.p)/c.q) for c in ck]
print("|c_k|:", [mp.nstr(v,6) for v in vals])
# ratio |c_{k+1}|/|c_k|  and  |c_k|^{1/k}, and |c_k|/k! ,  k!*? growth -> Gevrey-1?
print("\n k   |c_k|        ratio       |c_k|/k!      |c_k|/(k!)^s test")
import math
for k in range(len(vals)):
    r = vals[k]/vals[k-1] if k>0 else mp.mpf('nan')
    kf = mp.factorial(k+1)  # index offset: c_k multiplies tau^{k-1/2}
    print(f"  {k+1}  {mp.nstr(vals[k],6):>10}  {mp.nstr(r,6):>9}   {mp.nstr(vals[k]/kf,5):>10}")
# l1-norm cs(m) given in problem grows -> the SERIES dev(tau)=sum c_k(tau/2)^{k-1/2} is DIVERGENT (Gevrey>=1).
# That's FINE for asymptotics (Poincare) but means dev is NOT analytic; only C^infty asymptotic.
print("\nProblem states cs(m)*m! blows up (0.097..46.5) => the dev SERIES is divergent (factorially): Gevrey-1-ish.")
print("=> Even the SMOOTH carrier's Taylor series diverges; C^infty (not analytic) is the most one can hope for.")
