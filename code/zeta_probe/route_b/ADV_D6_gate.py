"""
INDEPENDENT check of the GATE and the residual bound [S2], plus the GOAL statement
R = P12 - E = O(tau^{5/2}), E = (1/2)(w-W)^2 sin(w) sin(w-W).

All at NEWTON-REFINED poles. High precision.
"""
import mpmath as mp

def cocycle_full(q, N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return X,Y,x,y   # P11,P12,P21,P22=Se

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
        f0=Sig_t(q)-1
        fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h)
        dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-8)): break
    return q

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*100)
print("GATE + [S2] + GOAL (R=P12-E) at NEWTON-REFINED poles")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'|P12|/t^1.5':>13} {'(cosw-T2Se)/t^1.5':>18} {'P12/t^1.5':>12} {'E/t^1.5':>11} {'R/t^2.5':>12}")

sup=mp.mpf(0)
half=mp.mpf('0.5')
rows=[]
for m in [4,6,8,12,16,24,32,40,50,60,70,79]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps = 45 + int(2.5*float(w0))
    q0=poles[m-1]
    q=refine_pole(q0)
    tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2)
    N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N)
    Se=P22
    # gate
    r_gate = abs(P12)/tau**mp.mpf('1.5')
    if r_gate>sup: sup=r_gate
    # [S2]: cos w - T2_Se, T2_Se = cos W - Se
    T2Se = mp.cos(W) - Se
    s2 = (mp.cos(w) - T2Se)/tau**mp.mpf('1.5')
    # elementary leading part E
    E = half*(w-W)**2 * mp.sin(w) * mp.sin(w-W)
    Er = E/tau**mp.mpf('1.5')
    P12r = P12/tau**mp.mpf('1.5')
    R = P12 - E
    Rr = R/tau**mp.mpf('2.5')
    rows.append((m,float(tau),float(r_gate),float(s2),float(P12r),float(Er),float(Rr),P12,E,R,tau,w,W,Se,P11))
    print(f"{m:>3} {float(tau):>11.4e} {float(r_gate):>13.7f} {float(s2):>18.8f} {float(P12r):>12.7f} {float(Er):>11.7f} {float(Rr):>12.7f}")
    mp.mp.dps=50

print(f"\nsup_m |P12|/tau^1.5 = {float(sup):.7f}   gate 1/sqrt2 = {float(1/mp.sqrt(2)):.7f}   1/(4 sqrt2) = {float(1/(4*mp.sqrt(2))):.7f}")
