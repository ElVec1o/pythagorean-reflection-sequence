"""
ATOM B via POLE-ZERO factorization (concrete route).
Gate |P12|<=C tau^{3/2}  <=>  |Y3(1)|=|sum d_k| <= C1 tau^{5/2},  P12=(2q^3/(1-q^3)) Y3(1).
Travel pole q_m: Sig1^T(q_m)=1.  Zero qz_m: Y3(1)(qz_m)=0.  CLAIM:
   |Y3(1)(q_m)| <= |Y3(1)'(qz_m)| * |q_m - qz_m|,   with
   (a) |q_m - qz_m| ~ C tau^3   (pole-zero coincidence),
   (b) |Y3(1)'(qz_m)| ~ C' tau^{-1/2}  (derivative scale),
   => |Y3(1)(q_m)| ~ tau^{5/2}, gate holds.  If (a),(b) are clean, Atom B reduces to them.
Check the rates of (a),(b) and that the product reproduces |Y3(1)(q_m)|~tau^{5/2}.
"""
import mpmath as mp
def dk(k,q):
    num=(-2)**k*(1-q)**k*q**(k*k+3*k)
    den=mp.mpf(1)
    for i in range(k):
        den*=(1-q**(2*i+2))*(1-q**(2*i+5))
    return num/den
def Y3at1(q,K=None):
    if K is None: K=int(8/float(1-q)**0.5)+30
    return mp.fsum(dk(k,q) for k in range(K))
def Sig1T(q):
    S=mp.mpf(0); pr=mp.mpf(1); maxj=int(220/(1-q))+50
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2))-2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10): break
    return S
def find_root(f,q0,iters=40):
    q=mp.mpf(q0); h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(iters):
        f0=f(q); fp=(f(q+h)-f(q-h))/(2*h)
        if fp==0: break
        dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-10)): break
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print(f"{'m':>3}{'tau':>11}{'|q_m-qz|':>13}{'/tau^3':>9}{'|Y3p(qz)|':>12}{'*tau^.5':>9}{'|Y3(q_m)|':>13}{'/tau^2.5':>10}")
for m in [2,3,4,6,8,12,16]:
    q0=poles[m-1]; tau0=-mp.log(q0); w=mp.sqrt(2/tau0)
    mp.mp.dps=50+int(1.5*float(w))
    qm=find_root(lambda q:Sig1T(q)-1, q0)           # travel pole
    qz=find_root(Y3at1, q0)                          # nearest Y3(1) zero
    tau=-mp.log(qm)
    hh=mp.mpf(10)**(-(mp.mp.dps//2))
    Y3p=(Y3at1(qz+hh)-Y3at1(qz-hh))/(2*hh)          # derivative at the zero
    Y3m=Y3at1(qm)                                    # Y3(1) at the travel pole
    t3=tau**3; tm=tau**mp.mpf('-0.5'); t25=tau**mp.mpf('2.5')
    print(f"{m:>3}{float(tau):>11.6f}{float(abs(qm-qz)):>13.3e}{float(abs(qm-qz)/t3):>9.4f}"
          f"{float(abs(Y3p)):>12.3e}{float(abs(Y3p)*mp.sqrt(tau)):>9.4f}{float(abs(Y3m)):>13.3e}{float(abs(Y3m)/t25):>10.4f}")
    mp.mp.dps=30
print("\nIf |q_m-qz|/tau^3 -> const (a) and |Y3'(qz)|*sqrt(tau) -> const (b), then |Y3(q_m)|~tau^{5/2} (gate).")
print("=> Atom B reduces to: (a) pole-zero coincidence O(tau^3), (b) derivative |Y3'(qz)|=O(tau^{-1/2}).")
