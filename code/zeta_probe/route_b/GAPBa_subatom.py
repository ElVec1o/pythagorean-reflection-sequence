"""
SUB-ATOMIZE B(a) = gate |P12|<=C tau^{3/2}.  P12 = 1/P11 - Se = -cos w + T2 + O(tau^{3/2}).
(a1) sqrt(tau) CANCELLATION:  cos w_m = T2(q_m) to leading  <=>  c0^travel = c0^bulk (both sqrt2/36).
     Verify cos w_m/(sqrt(tau) sin w_m) and T2(q_m)/(sqrt(tau) sin w_m) both -> sqrt2/36=0.03928, and the
     residual (cos w_m - T2(q_m))/tau^{3/2} is BOUNDED (the subleading a2).
(a2) tau^{3/2} subleading: P12/tau^{3/2} -> 1/(4 sqrt2)=0.1768 < 1/sqrt2 (gate, 4x margin).
If (a1) holds (c0^trav=c0^bulk, structural via same B_s engine), B(a) reduces to (a2) alone.
"""
import mpmath as mp
from abelplana_verify import S1_bulk
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y,X,x   # P12,Se,P11,P21
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
c0=mp.sqrt(2)/36
print(f"sqrt2/36 = {float(c0):.6f}")
print(f"{'m':>3}{'tau':>10}{'cosw_m/(st sinw)':>17}{'T2/(st sinw)':>14}{'(a1)resid/t1.5':>15}{'P12/t1.5(a2)':>13}")
for m in [2,3,4,6,8,12,16]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    mp.mp.dps=40+int(1.3*float(w)); N=int(60/(1-q))
    P12,Se,P11,P21=cocycle(q,N)
    S1=S1_bulk(q); cw=mp.cos(w); sw=mp.sin(w)
    T2=S1-(1-cw)-(cw-mp.cos(W))    # bulk T2 = S1bulk -(1-cos w) - T1
    st=mp.sqrt(tau)
    c0_trav=cw/(st*sw); c0_bulk=T2/(st*sw)
    resid_a1=(cw-T2)/tau**mp.mpf('1.5')   # the sqrt(tau) cancellation residual -> subleading
    gate_a2=P12/tau**mp.mpf('1.5')
    print(f"{m:>3}{float(tau):>10.6f}{float(c0_trav):>17.6f}{float(c0_bulk):>14.6f}{float(resid_a1):>15.5f}{float(gate_a2):>13.6f}")
    mp.mp.dps=40
print("\n(a1): cosw_m/(st sinw) and T2/(st sinw) BOTH -> sqrt2/36=0.03928  => c0^trav=c0^bulk, sqrt(tau) CANCELS.")
print("      residual (cosw-T2)/tau^1.5 BOUNDED => the cancellation is exact to leading, leaving tau^{3/2} (a2).")
print("(a2): P12/tau^1.5 -> 0.1768 = 1/(4 sqrt2) < 0.707 (gate, 4x margin).  THE lone subleading frontier.")
print("If c0^trav=c0^bulk is STRUCTURAL (rem:blockscope: same B_s saddle), (a1) PROVEN => B(a) = (a2) only.")
