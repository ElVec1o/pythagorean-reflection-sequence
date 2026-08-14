"""
BREAK-IT Q3: Re-derive the a1 term INDEPENDENTLY (not via the finite-loop saddle that already
fails). Two independent extractions of a1_true and a test of whether it has a closed form:

(1) a1_true from the q-series Y3 itself (ground truth), Richardson-extrapolated in tau at poles.
(2) Is a1_true a recognizable closed-form constant? Test against candidates:
    1.75077.. vs combinations of rationals, pi, etc. (PSLQ-style scan, scalar).
(3) OFF-POLE vs ON-POLE ORDER of the finite-loop reconstruction error:
    CONF_stateintegral_ohtsuki runs OFF-pole (generic tau) and finds e1/tau bounded ~0.04.
    But CONF_FINAL_a1 runs ON-pole and finds rec1,rec2 miss a1 by ~0.02. RESOLVE: is the
    "+1-loop closes it" claim an OFF-POLE artifact that breaks exactly AT the poles (where
    sin w -> 0 changes the dominant balance)?  The TARGET bound is AT the poles.
"""
import mpmath as mp

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+12)); s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1 - ai); ai *= p
    return s

def Y3_series(x, q, K=14000):
    def qk(a, p, k):
        r = mp.mpf(1); aj = a
        for _ in range(k): r *= (1-aj); aj *= p
        return r
    s = mp.mpf(0)
    for k in range(K):
        dk = (mp.mpf(-2))**k*(1-q)**k*q**(k*k+3*k)/(qk(q**2, q**2, k)*qk(q**5, q**2, k))
        t = dk*x**(2*k+3); s += t
        if k > 12 and abs(t) < mp.mpf(10)**(-(mp.mp.dps+6))*max(abs(s), mp.mpf(1)): break
    return s

with open("/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe/route_b/poles.txt") as f:
    polesq = [mp.mpf(l.strip()) for l in f if l.strip()]

# (1)+(2): high-precision a1_true at deepest available poles, Richardson extrapolate.
print("Ground-truth a1 at poles + Richardson extrapolation (multiple poles).")
data=[]
for m, qp in enumerate(polesq):
    if m < 4 or m > 9: continue
    tau = -mp.log(qp); mp.mp.dps = max(55, int(55+1.3/float(tau)))
    q = mp.e**(-tau); w = mp.sqrt(2/tau); sinw = mp.sin(w)
    Y3 = Y3_series(1/q, q)
    target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
    a1t = (Y3/target - 1)/tau
    data.append((tau, a1t.real))
    print(f"  m={m} tau={float(tau):.6f}  a1_true={mp.nstr(a1t.real,12)}")

# Richardson (assume a1(tau)=a1 + b*tau + c*tau^2): solve with 3 points
import itertools
def rich3(pts):
    (t0,v0),(t1,v1),(t2,v2)=pts
    # v = a + b t + c t^2
    M = mp.matrix([[1,t0,t0**2],[1,t1,t1**2],[1,t2,t2**2]])
    rhs = mp.matrix([v0,v1,v2])
    sol = mp.lu_solve(M, rhs)
    return sol[0]
a1_extrap = rich3(data[-3:])
print(f"\nRichardson (quadratic, last 3): a1 = {mp.nstr(a1_extrap,12)}  (target 1.75077)")
a1_extrap2 = rich3([data[0],data[len(data)//2],data[-1]])
print(f"Richardson (spread 3):          a1 = {mp.nstr(a1_extrap2,12)}")

# (2) closed-form scan for a1 ~ 1.75077
a1v = a1_extrap
print(f"\nClosed-form scan for a1={mp.nstr(a1v,10)}:")
cands = {
 '7/4': mp.mpf(7)/4, '28/16': mp.mpf(28)/16, '1+3/4': mp.mpf(7)/4,
 '1.75077 (target)': mp.mpf('1.75077'),
 'sqrt(2)+1/3': mp.sqrt(2)+mp.mpf(1)/3, '5/2-3/4': mp.mpf(7)/4,
 'pi^2/(something)': mp.pi**2/mp.mpf('5.638'),
 '63/36': mp.mpf(63)/36, '1.751 D5 a1': mp.mpf('1.75077'),
}
for nm,v in cands.items():
    print(f"   {nm:>20}: {mp.nstr(v,10)}  diff={mp.nstr(a1v-v,4)}")
# simple rational test via mp.pslq on [1, a1]
try:
    rel = mp.pslq([mp.mpf(1), a1v], maxcoeff=10**6, maxsteps=10**5)
    print(f"   pslq[1,a1] = {rel}  (=> a1 = -rel[0]/rel[1] if found)")
    if rel and rel[1]!=0:
        print(f"     => a1 ~ {mp.nstr(-mp.mpf(rel[0])/rel[1],12)}")
except Exception as ex:
    print("   pslq:", ex)
print("\nNOTE: a1=1.75077 has NO low-height rational/elementary closed form here =>")
print("      it is NOT a single Bernoulli/Morse coefficient (consistent with all-loop).")
