# P1d_delta.py -- RIGOROUS (Arb) bound for the deep-rational hypothesis of Theorem 5 along x_N = j/n0 + theta/(n0 N), |theta|=1,
# at the seed j/n0 (used in Proposition 6(i)).  For n in T:  n0 not| n, n < N/2  =>  ||n x_N|| >= 1/(2 n0), so 1/|1-zeta^{-n}| <= 2n0/4;
# multiples of n0 up to n0*floor(N/2) lie in M;  every other n in T has n >= N/2 and 1/|1-zeta^{-n}| <= N/4.  Hence
#   Delta_N(x_N; rho) <= (2 n0/4) g^{n2+1}/((n2+1)(1-g)) + (N/4) g^{h}/(h (1-g)),   g = |u0| rho,  h = ceil(N/2).
# |u0| is bounded on a ball of radius RAD around j/n0 (with the lambda-factor of Lemma W).
# Usage: python3 P1d_delta.py j n0 n2 eta RAD N1 N2 ...
import sys
from flint import arb, acb, ctx
ctx.prec = 200
PI = arb.pi()
j, n0, n2, eta, rad = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), arb(sys.argv[4]), float(sys.argv[5])
x = arb(j)/n0 + arb(0, rad)
c = -2*(1 - (2*PI*acb(0, 1)*x).exp())
l = arb(c.abs_lower()).log()
u = (1/arb(c.abs_lower()))*(1 + 0.1*(-151*l).exp())
for tag, rho in (('rho_eta', (2*PI*eta).exp()),):
    g = u*rho; assert bool(g < 1)
    for Ns in sys.argv[6:]:
        N = int(float(Ns)); h = (N + 1)//2
        D = arb(2*n0)/4*g**(n2 + 1)/((n2 + 1)*(1 - g)) + arb(N)/4*g**h/(h*(1 - g))
        print('%d/%d n2=%d %s: |u0|rho <= %s, N=%s: Delta_N(x_N; rho) <= %s  (hypotheses need <= 1e-3 at rho_core <= rho_eta)' % (
            j, n0, n2, tag, g.str(5, radius=False), Ns, D.str(3, radius=False)))
