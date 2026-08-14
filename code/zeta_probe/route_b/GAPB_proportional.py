"""
DECISIVE test for Atom B route: is (Sig1^T(q) - 1) PROPORTIONAL to Y3(1)(q) up to O(tau^3)-relative?
If (Sig1^T - 1) = kappa(q) * Y3(1) * (1 + O(tau^3-rel)) with kappa smooth, then the zeros of Sig1^T-1
(travel poles) and Y3(1) (q-Bessel) coincide to O(tau^3) STRUCTURALLY -- closing (a) without the
subleading confluence.  Check: ratio r(q)=(Sig1^T-1)/Y3(1) near a pole, and how r varies (smooth? const?).
Also fit the proportionality const and the deviation rate.
"""
import mpmath as mp
def dk(k,q):
    num=(-2)**k*(1-q)**k*q**(k*k+3*k); den=mp.mpf(1)
    for i in range(k): den*=(1-q**(2*i+2))*(1-q**(2*i+5))
    return num/den
def Y3at1(q):
    K=int(8/float(1-q)**0.5)+30; return mp.fsum(dk(k,q) for k in range(K))
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
print("ratio r(q)=(Sig1^T-1)/Y3(1) sampled around the pole; is it ~const (proportional)?")
print(f"{'m':>3}{'tau':>10}{'r at q_m-d':>14}{'r at q_m':>14}{'r at q_m+d':>14}{'rel spread':>12}")
for m in [3,4,6,8,12]:
    q0=poles[m-1]; tau0=-mp.log(q0); w=mp.sqrt(2/tau0)
    mp.mp.dps=50+int(1.5*float(w))
    qm=find_root(lambda q:Sig1T(q)-1,q0)
    tau=-mp.log(qm); d=tau**2  # sample spacing ~ tau^2 (< pole spacing)
    rs=[]
    for qq in [qm-d, qm, qm+d]:
        num=Sig1T(qq)-1; den=Y3at1(qq)
        rs.append(num/den if den!=0 else mp.mpf('nan'))
    spread=abs(rs[2]-rs[0])/(abs(rs[1])+mp.mpf('1e-99'))
    print(f"{m:>3}{float(tau):>10.6f}{mp.nstr(rs[0],7):>14}{mp.nstr(rs[1],7):>14}{mp.nstr(rs[2],7):>14}{float(spread):>12.3e}")
    mp.mp.dps=30
print("\nIf r(q) is ~const (small spread) across the pole, Sig1^T-1 ∝ Y3(1): zeros coincide STRUCTURALLY")
print("=> (a) |q_m-qz|=O(tau^3) follows from the SMOOTHNESS of kappa, NOT the subleading confluence.")
print("Then Atom B = (a)[structural] + (b)[leading-confluence derivative O(tau^-.5)] + MVT.")
