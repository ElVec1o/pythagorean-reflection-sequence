"""
ADVERSARIAL: verify the j^3 -> vartheta^3 resummation bridge EXACTLY.

We must show:
   - sum_{j>=0} (-1)^j hat_j * j^3  ==  vartheta^3 (1-cos w)|... with the RIGHT index bookkeeping,
where hat_j = (2/tau)^{j+1}/(2j+2)! = w^{2j+2}/(2j+2)!  (since 2/tau = w^2),
so (-1)^j hat_j = (-1)^j w^{2(j+1)}/(2(j+1))!.

Put n = j+1 (n>=1):  (-1)^j hat_j = (-1)^{n-1} w^{2n}/(2n)!,  and  1-cos w = sum_{n>=1} (-1)^{n-1} w^{2n}/(2n)!.
So  sum_j (-1)^j hat_j * f(j) = sum_{n>=1} (-1)^{n-1} w^{2n}/(2n)! * f(n-1).

The operator vartheta=(1/2) w d/dw acting on w^{2n}/(2n)! gives n * w^{2n}/(2n)!.  So
   vartheta^p (1-cos w) = sum_{n>=1} (-1)^{n-1} n^p w^{2n}/(2n)!.
Thus with f(j)=j^3=(n-1)^3 we get a combination of vartheta^3,vartheta^2,vartheta,1 applied to (1-cos w).

E^T_lead = - (1/9)tau^2 sum_j (-1)^j hat_j j^3
         = - (1/9)tau^2 sum_{n>=1} (-1)^{n-1} (n-1)^3 w^{2n}/(2n)!
         = - (1/9)tau^2 [ (vartheta^3 - 3 vartheta^2 + 3 vartheta - 1)(1-cos w) ].
LEADING large-w: vartheta^3(1-cos w) ~ -(w^3/8) sin w dominates (each vartheta ~ multiply by ~ (w/2)*(slope)).
Lower vartheta powers are lower order in w => subleading.  So E^T_lead ~ -(1/9)tau^2 * (-(w^3/8) sin w)
= (1/72)tau^2 w^3 sin w = (sqrt2/36) sqrt(tau) sin w.

CHECK NUMERICALLY (no asymptotics): compute  -(1/9)tau^2 (vartheta^3-3vartheta^2+3vartheta-1)(1-cos w)
in closed form and compare to E_lead = -sum_j (-1)^j hat_j (1/9)tau^2 j^3 directly, AND to c_T sqrt tau sin w.
"""
import sympy as sp
import mpmath as mp

# symbolic vartheta powers of (1-cos w)
wv = sp.symbols('w', positive=True)
def vth(e): return sp.Rational(1,2)*wv*sp.diff(e, wv)
f = 1 - sp.cos(wv)
v1 = sp.simplify(vth(f))
v2 = sp.simplify(vth(v1))
v3 = sp.simplify(vth(v2))
comb = sp.expand(v3 - 3*v2 + 3*v1 - f)    # (vartheta^3-3vartheta^2+3vartheta-1)(1-cos w)
print("(vartheta^3-3vartheta^2+3vartheta-1)(1-cos w) =")
print("   ", sp.simplify(comb))
print("   leading large-w term should be -(w^3/8) sin w; full expr:")
print("   ", sp.collect(sp.expand_trig(comb), [sp.sin(wv), sp.cos(wv)]))

# numeric check: the (n-1)^3 sum equals comb
def hatf(jj, tau): return (2/tau)**(jj+1)/mp.factorial(2*jj+2)
print("\nNumeric: sum_j (-1)^j hat_j (n-1)^3 (j^3) vs symbolic comb, and vs leading -(w^3/8)sin w")
for tau in [mp.mpf('0.01'), mp.mpf('0.001')]:
    mp.mp.dps = 60+int(2.5*mp.sqrt(2/tau))
    w = mp.sqrt(2/tau)
    J = int(3*w)+60
    S = mp.fsum([(-1)**jj*hatf(jj,tau)*jj**3 for jj in range(J)])
    combf = sp.lambdify(wv, comb, 'mpmath')
    Cf = combf(w)
    lead = -(w**3/8)*mp.sin(w)
    print(f"  tau={mp.nstr(tau,4)} w={mp.nstr(w,8)}: sum_j(-1)^j hat j^3 = {mp.nstr(S,12)}")
    print(f"      symbolic comb(w)          = {mp.nstr(Cf,12)}  (match? {mp.nstr(S-Cf,4)})")
    print(f"      leading -(w^3/8) sin w     = {mp.nstr(lead,12)}  (rel diff {mp.nstr((S-lead)/S,4)})")
    # assemble c_T
    E_lead = -(mp.mpf(1)/9)*tau**2 * S
    print(f"      E_lead/(sqrt tau sin w)   = {mp.nstr(E_lead/(mp.sqrt(tau)*mp.sin(w)),12)}  (cT=sqrt2/36={mp.nstr(mp.sqrt(2)/36,12)})")
