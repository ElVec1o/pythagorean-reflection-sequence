"""
G3 end-to-end turning-point check: compute y_n PAST the turning point n*, verify
   P12 = (WKB amplitude at n*) x (Airy connection) x (phase factor sin/cos(Theta(n*)+pi/4)).
If the suppression of P12 is a clean PHASE factor (controlled by the pole condition), G3 decomposes:
   3a amplitude (bounded WKB, done) x 3c Airy connection (Olver, explicit error) x 3d phase (pole condition).
"""
import mpmath as mp
mp.mp.dps=40

def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(220/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=16):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def run(m):
    q=refine(poles[m-1]); tau=-mp.log(q); w=mp.sqrt(2/tau)
    Nconv=int((mp.mp.dps+15)*2.3026/tau)+200    # past turning point, P12 converged
    # full cocycle for true P12
    a,b=mp.mpf(1),mp.mpf(0); qn=mp.mpf(1)
    # also accumulate WKB phase Theta and amplitude up to the turning point
    z_prev=None; z_curr=None
    Theta=mp.mpf(0); nstar=None; R_star=None; Theta_star=None; sin_at_x=None
    seq_tail=[]
    for n in range(1,Nconv+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        a,b=a*(1+2*q2n)-2*b*qn, 2*a*q3n+b*(1-2*q2n)
        bn=(1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
        if abs(bn)<2:
            kn=mp.acos(bn/2); Theta+=kn
            z=q**(-mp.mpf(3)*n/2)*b
            if z_prev is not None and z_curr is not None:
                pass
            z_prev=z_curr; z_curr=z
        elif nstar is None:
            nstar=n; Theta_star=Theta
            # amplitude just before turning point
            kprev=mp.acos((1+q**3-2*(1-q)*q**(2*(n-1)+2))/q**mp.mpf('1.5')/2)
            if z_prev is not None:
                R_star=mp.sqrt((z_curr**2+z_prev**2-2*mp.cos(kprev)*z_curr*z_prev)/mp.sin(kprev)**2)
        if n>=Nconv-3: seq_tail.append(b)
    P12=b
    return tau,w,P12,nstar,Theta_star,R_star,seq_tail

print(f"{'m':>2}{'tau':>9}{'P12/tau^1.5':>12}{'n*':>7}{'Theta(n*)':>12}{'Theta(n*)/pi':>12}{'R*':>9}{'R* q^{3n*/2}':>14}")
for m in [6,8,10,12]:
    tau,w,P12,nstar,Th,Rs,tail=run(m)
    settled = abs(tail[-1]-tail[-2])<mp.mpf('1e-20')
    Rq = Rs*mp.exp(-mp.mpf('1.5')*nstar*tau) if (Rs and nstar) else mp.mpf('nan')
    print(f"{m:>2}{float(tau):>9.5f}{float(P12/tau**mp.mpf('1.5')):>12.5f}{nstar:>7}{float(Th):>12.5f}{float(Th/mp.pi):>12.6f}"
          f"{float(Rs) if Rs else float('nan'):>9.3f}{float(Rq) if Rq==Rq else float('nan'):>14.6g}")
print("\nKEY: if Theta(n*)/pi = (integer + delta) with delta the SAME small offset across poles, the Airy")
print("connection sin(Theta(n*)+pi/4) carries a UNIFORM phase => P12 suppression is the pole-condition phase (3d).")
print("R* q^{3n*/2} = physical amplitude at turning point; P12 ~ that x Airy x phase. Compare P12/tau^1.5->0.177.")
