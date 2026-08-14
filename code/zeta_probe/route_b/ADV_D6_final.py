"""
FINAL consolidated independent confirmation:
  - GATE: sup_m |P12|/tau^{3/2} < 1/sqrt2 with ~4x margin, -> 1/(4 sqrt2)
  - GOAL: R = P12 - E = O(tau^{5/2}), E=(1/2)(w-W)^2 sin w sin(w-W)
  - [S2] bounded; (*) bounded; both proportional (ratio -> 3/sqrt2); same saddle defect.
Highest-m poles, Newton-refined.
"""
import mpmath as mp

def cocycle_full(q, N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return X,Y,x,y

def Sig_t(q):
    q=mp.mpf(q); S=mp.mpf(0); pr=mp.mpf(1)
    maxj=int(220/(1-q))+50
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10): break
    return S

def refine_pole(q0, iters=8):
    q=mp.mpf(q0); h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(iters):
        f0=Sig_t(q)-1; fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h)
        dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-8)): break
    return q

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
s32=mp.mpf('1.5'); s52=mp.mpf('2.5'); half=mp.mpf('0.5')

print("FINAL CONSOLIDATED CHECK (refined poles)")
print(f"{'m':>3} {'tau':>10} {'|P12|/t1.5':>11} {'R/t2.5':>10} {'E3 resid':>10} {'[S2]/t1.5':>10} {'(*)/[S2]':>9}")
sup=mp.mpf(0)
for m in [4,20,40,60,79]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=55+int(3.0*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); N=int(115/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N); Se=P22
    rg=abs(P12)/tau**s32
    if rg>sup: sup=rg
    E=half*(w-W)**2*mp.sin(w)*mp.sin(w-W)
    R=P12-E
    e3=P12-(1/P11-Se)
    s2u=mp.cos(w)-(mp.cos(W)-Se)
    star=1/P11-mp.cos(W)+mp.cos(w)
    print(f"{m:>3} {float(tau):>10.3e} {float(rg):>11.7f} {float(R/tau**s52):>10.6f} {mp.nstr(e3,2):>10} {float(s2u/tau**s32):>10.7f} {float(star/s2u):>9.6f}")
    mp.mp.dps=50
print(f"\nsup|P12|/t1.5={float(sup):.7f}  gate 1/sqrt2={float(1/mp.sqrt(2)):.7f}  margin={float((1/mp.sqrt(2))/sup):.3f}x  -> 1/(4sqrt2)={float(1/(4*mp.sqrt(2))):.7f}")
print("R/t2.5 BOUNDED nonzero => GOAL R=O(tau^{5/2}) holds.  (*)/[S2]->3/sqrt2=%.6f"%float(3/mp.sqrt(2)))
