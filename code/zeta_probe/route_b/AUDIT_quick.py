"""Quick independent re-checks: A1 reduction identity, A6 gate ratio, c1 constant."""
import mpmath as mp
mp.mp.dps = 50

# ---- A6 gate: cocycle, P12 = 1/P11 - Se exactly, |P12|/tau^{3/2} -> 1/(4 sqrt2) ----
def cocycle(q, N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y,X,x   # P12, Se=P22, P11, P21

# travel poles: find q_m where 1 - Sigma_1^T = 0, i.e. P11 + P21 = 0 (pole cond)
def find_pole(m, N=200000):
    # w_m ~ (m-1/2)pi => tau ~ 2/w^2, q ~ e^{-tau}. refine by P11+P21=0
    w0 = (m-0.5)*mp.pi; tau0 = 2/w0**2; q0 = mp.e**(-tau0)
    def f(q):
        P12,Se,P11,P21 = cocycle(q, N)
        return P11+P21
    try:
        q = mp.findroot(f, q0)
        return q
    except Exception as e:
        return None

print("A6 gate: P12 = 1/P11 - Se exact?  and |P12|/tau^{3/2}:")
print(f"{'m':>3} {'tau':>12} {'|P12-(1/P11-Se)|':>18} {'|P12|/tau^1.5':>14} {'det-1':>10}")
for m in [1,2,3,6,10]:
    N = 4000 if m<8 else 30000
    q = find_pole(m, N)
    if q is None:
        print(f"{m:>3}  pole not found"); continue
    tau = -mp.log(q)
    P12,Se,P11,P21 = cocycle(q, N)
    ident = abs(P12 - (1/P11 - Se))
    det = P11*Se - P12*P21
    print(f"{m:>3} {mp.nstr(tau,7):>12} {mp.nstr(ident,4):>18} {mp.nstr(abs(P12)/tau**mp.mpf(1.5),7):>14} {mp.nstr(det-1,3):>10}")
print(f"target 1/(4 sqrt2) = {mp.nstr(1/(4*mp.sqrt(2)),8)},  1/sqrt2 = {mp.nstr(1/mp.sqrt(2),6)}")

# ---- c1 leading constant of E = S1-(1-cos w): should be -17 sqrt2/36 at sin w = +-1 ----
print()
print("Leading sqrt(tau) coeff of E at sin w = +1 (w=(n+1/2)pi):  target -17 sqrt2/36 =",
      mp.nstr(-17*mp.sqrt(2)/36, 10))
import sys
try:
    from abelplana_verify import S1_bulk
    vals=[]
    for n in [20,40,80,160]:
        w = (n+mp.mpf('0.5'))*mp.pi; tau = 2/w**2; q=mp.e**(-tau)
        E = S1_bulk(q) - (1-mp.cos(w))
        vals.append(E/mp.sqrt(tau))   # sin w = +1
    # richardson
    print("   E/sqrt(tau) at sin w=1:", [mp.nstr(v,8) for v in vals])
except Exception as e:
    print("   (S1_bulk slow/failed:", e, ")")
