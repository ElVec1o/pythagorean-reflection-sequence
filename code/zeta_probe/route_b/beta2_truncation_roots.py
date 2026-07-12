#!/usr/bin/env python3
"""Truncation-root scheme (paper2 rem:truncroot): the wall in s-independent form.

P_N = (q;q)_{2N} sum_{k<=N} (-2)^k q^{k^2}(1-q)^k/(q;q)_{2k} in Z[q]: degree 2N^2+N,
heights e^{O(N)} (pentagonal sparsity), nearest root |q_N - q*| ~ q*^{(N+1)^2} (verified N<=7).
Liouville: q* = s/t => |P_N(q*)| >= t^{-(2N^2+N)}; analytic: e^{O(N)} q*^{(N+1)^2}.
Contradiction iff q* < t^{-2}: impossible. Deficit = the double-Pochhammer factor 2 exactly.
COROLLARY: a single-Pochhammer equivalent form (clearing deg ~N^2/2) would prove q* != s/t for
all s < sqrt(t) -- and Rogers-Ramanujan/Bailey transformations to such a form require a q-power
argument, which the catalytic point z = 2q(1-q) is not. The wall = the catalytic argument.
"""
import sympy as sp
import mpmath as mp
mp.mp.dps=80
q=sp.symbols('q')
qstar=mp.mpf('0.44945363055894804612554582539569638931955531619656834986311073606681761091')
def PN(N):
    S=sp.Integer(0)
    for k in range(N+1):
        cof=sp.Integer(1)
        for i in range(2*k+1,2*N+1): cof*=(1-q**i)
        S+=sp.expand((-2)**k*q**(k*k)*(1-q)**k*sp.expand(cof))
    return sp.Poly(sp.expand(S),q)
print("N | deg (2N^2+N) | log2 H(P_N) | |q_N - q*|   | q*^{(N+1)^2}  | deg*log2(t)/N^2 needed<1? (t=2 case)")
for N in [2,3,4,5,6,7]:
    P=PN(N)
    H=max(abs(c) for c in P.all_coeffs())
    f=sp.lambdify(q,P.as_expr(),'mpmath')
    qN=mp.findroot(f,qstar,tol=mp.mpf(10)**-70)
    err=abs(qN-qstar)
    print(f"{N} | {P.degree():>3} ({2*N*N+N:>3}) | {mp.nstr(mp.log(H,2),4):>6} | {mp.nstr(err,3)} | {mp.nstr(qstar**((N+1)**2),3)}")
print("\nheights e^{O(N)} (log2 H grows ~linearly), error ~ q*^{N^2}: both confirmed if columns track.")
