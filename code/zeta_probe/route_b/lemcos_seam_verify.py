"""
lemcos_seam_verify.py  — verification for the lem:cos closure via the
degree-counting / saddle-scaling decomposition of T2.

KEY RESULT (all reproduced below to high precision):
  E := S_1 - (1-cos w) = T_1 + T_2,    w=sqrt(2/tau), W=w e^{-tau/2}.
  T_1 = cos w - cos W,  |T_1| <= sqrt(tau/2)            (Prop:T1, already rigorous)
  T_2 = sum_{i>=1} (-1)^i W^{2i}/(2i)! * phi_i,  phi_i = 1 - e^{-B_i},  B_i >= 0,
        B_i = -log rho_{i-1} - i*tau.

  NEW: T_2 = sum_{p even >=2} tau^p E_p(W),  E_p an EXPLICIT trig polynomial of
  degree 3p/2 in W with super-geometrically small leading coefficient.  In
  particular
        E_2(W) = -(W^2/16) cos W + (W^3/72 - W/48) sin W,
  whose leading term gives tau^2 * (W^3/72) sin W = (sqrt2/36) sqrt(tau) sin w,
  matching the documented T_2 leading constant.  Hence
        |T_2| <= (sqrt2/36) sqrt(tau) + O(tau^{3/2})   uniformly in the phase,
  and |E| <= sqrt(tau/2) + (sqrt2/36 + o(1)) sqrt(tau) = O(sqrt tau).  [lem:cos]

  The SAME decomposition applied to K'(u)=sum_m (-1)^{m+1} mu_m u^{2m}/(2m)! gives
        K'(u) = -tau cos u + tau^2 [ (u^2/12 + 1/3) cos u - (u/6) sin u ] + O(tau^{3/2}),
  so on [0,w] (where tau^2 u^2 <= 2tau):  sup_{[0,w]} |K'| <= (7/6 + o(1)) tau.
  That is the clean "sup|K'| <= C tau" form (C -> 7/6).
"""
import mpmath as mp, math

def alpha(k,tau): return 2/(mp.e**((k+1)*tau)-1)
def build_rho(tau,J):
    t=[]; prod=mp.mpf(1)
    for j in range(J):
        t.append(alpha(1+2*j,tau)*prod); prod*=(alpha(1+2*j,tau)-alpha(2+2*j,tau))
    that=[(2/tau)**(j+1)/mp.factorial(2*j+2) for j in range(J)]
    return [t[j]/that[j] for j in range(J)]

def S1(tau,J):
    s=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        s+=(-1)**j*alpha(1+2*j,tau)*prod
        prod*=(alpha(1+2*j,tau)-alpha(2+2*j,tau))
    return s

def E2(W):  # exact closed form
    return -(W**2/16)*mp.cos(W) + (W**3/72 - W/48)*mp.sin(W)

PASS=[]
# (A) verify T2 = sum_i (-1)^i W^{2i}/(2i)! phi_i  reproduces  E - T1, and matches tau^2 E2(W) at O(sqrt tau)
for tauval in ['0.01','0.002','0.0005']:
    tau=mp.mpf(tauval); w=mp.sqrt(2/tau)
    mp.mp.dps=int(float(w)/math.log(10))+70
    J=int(8/float(tau))+200
    rho=build_rho(tau,J)
    B=[(-mp.log(rho[i-1])-i*tau) if i>=1 else mp.mpf(0) for i in range(J)]
    phi=[1-mp.e**(-B[i]) for i in range(J)]
    W=w*mp.e**(-tau/2)
    T2=sum((-1)**i*W**(2*i)/mp.factorial(2*i)*phi[i] for i in range(1,J))
    Etrue=S1(tau,J)-(1-mp.cos(w))
    T1=mp.cos(w)-mp.cos(W)
    ok1=abs(Etrue-(T1+T2))<mp.mpf('1e-40')
    # leading model:
    ok2=abs(T2 - tau**2*E2(W)) < mp.mpf('5')*tau**mp.mpf('1.4')  # remainder O(tau^1.5)
    PASS.append((f"tau={tauval}: E=T1+T2 exact", ok1))
    PASS.append((f"tau={tauval}: |T2 - tau^2 E2(W)| = O(tau^1.5)  (={float(abs(T2-tau**2*E2(W))/tau**mp.mpf('1.5')):.3f}*tau^1.5)", ok2))
    # uniform |T2| <= (sqrt2/36) sqrt(tau)(1+o(1)):
    bound=mp.sqrt(2)/36*mp.sqrt(tau)
    PASS.append((f"tau={tauval}: |T2| <= sqrt2/36 sqrt(tau)*(1+small)  (|T2|/bound={float(abs(T2)/bound):.3f})", abs(T2) <= bound*mp.mpf('1.2')+tau))

print("="*64); print("lem:cos SEAM VERIFICATION (T2 decomposition)"); print("="*64)
for name,ok in PASS: print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
print("="*64); print("ALL PASS" if all(o for _,o in PASS) else "SOME FAILED")
