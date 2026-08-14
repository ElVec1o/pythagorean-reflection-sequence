import mpmath as mp
mp.mp.dps=40
# Series g(tau) is Gevrey-1 in tau. Borel B(t)=sum a_n/n! t^n, singularity at A (the 'action').
# The series arises from Y3 ~ (3/sqrt2) tau^{3/2} sin(w) (1 + g(tau)), w=sqrt(2/tau).
# So the NON-perturbative companion is the OTHER Bessel solution ~ cos(w) (or e^{+-iw}).
# The two solutions of the confluent eqn differ by phase exp(2 i w) = exp(2 i sqrt(2/tau)).
# In tau, exp(2 i sqrt2 / sqrt(tau)) is NOT exp(-A/tau) (wrong power: 1/sqrt tau not 1/tau).
# But g is Gevrey-1 in TAU (a_n ~ n! / A^n). The Borel sing A is where exp(-A/tau) ~ the leading
# non-pert correction to g. From memory: non-pert ~ exp(-2.3/tau) doubly-exp in w.
# Resurgence of the q-difference eqn (Braaksma): the formal exponents are the McMahon phases of
# the TWO Bessel-type solutions; their tau-Borel actions are differences of {analytic continuations}.
#
# DIRECT: a_n ~ C n! / A^n (1+...) for Gevrey-1. So A = lim n a_n/a_{n+1}? No: a_n/n! ~ C/A^n =>
# A = lim (a_n/n!)/(a_{n+1}/(n+1)!) = lim (n+1) a_n/a_{n+1}.  But complex A => a_n oscillate (they do).
# The conj-pair fit already gave A ~ 2.58+5.03i (|A|~5.65, arg~62.8).
#
# Candidate exact actions and their match:
print("Pinning A (nearest Borel sing), data: A ~ 2.58 + 5.03 i, |A|~5.65, arg~62.8 deg")
cands={
 '4 sqrt2 e^{i 63.43}':4*mp.sqrt(2)*mp.e**(1j*mp.atan(2)),
 '(5/2)(1+2i)':mp.mpf(5)/2*(1+2j),
 '2pi e^{i pi/3}':2*mp.pi*mp.e**(1j*mp.pi/3),
 'sqrt2 pi (1+? )':0,
 'pi^2/2 * e^{i 62.8}':mp.pi**2/2*mp.e**(1j*mp.radians(62.8)),
 '2sqrt2 + 4sqrt(1.6) i':0,
 'i pi^2/2 + something':0,
 '(pi^2/4)(... )':0,
 'pi^2/2 (cos? )':0,
}
for k,v in cands.items():
    if v==0: continue
    v=mp.mpc(v)
    print(f"  {k:24s}: {float(v.real):+.4f}{float(v.imag):+.4f}i  |.|={float(abs(v)):.4f} arg={float(mp.arg(v)*180/mp.pi):+.2f}")
# Most natural: the action of the turning point connecting to centrifugal sing. 
# For u''+(2-2/s^2)u=0 (s var), the action between turning pt s=1 and the regular sing s=0:
# A_action = 2 int_0^1 p ds with p=sqrt(2-2/s^2). For s<1, p imaginary: p=i sqrt(2/s^2-2).
# A = 2i int_0^1 sqrt(2/s^2-2)ds. But that diverges at s=0 (nu=3/2 centrifugal).
# The CORRECT resurgence action for a regular singular point x=0 with indicial exponents
# +/- nu (nu=3/2) is 2 pi i nu? or i pi (difference of exponents)*... Let me compute the
# monodromy/period. Actually the relevant thing: the Borel sing for Bessel J_nu asymptotic series
# is well known: the asymptotic series of J_nu(z) has Borel singularities at t = +/- 2 i z-scale.
# For our problem in tau, w=sqrt(2/tau), the Bessel argument is w => the 'instanton' exp(2iw).
# but we need tau-Borel. The map w=sqrt(2/tau) sends the w-plane exp(2iw) to a tau-singularity
# via Watson/Borel: NOT a simple action. => the tau-Borel plane sing is genuinely the image of
# the w-oscillation under sqrt, giving a BRANCH POINT (consistent with our finding) not a pole.
print("\nNOTE: w=sqrt(2/tau) maps the Bessel oscillation exp(2iw) (entire in 1/sqrt tau) to a")
print("tau-Borel BRANCH structure; the nearest branch point is the value we fit ~2.58+5.03i.")
