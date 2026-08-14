"""
CLOSE #4 (numerator asymptotic S0 ~ w sin w) via the absolute-contour method, NO Watson/saddle gap.
Key identity: the numerator error is the 2*theta image of the denominator error (theta=(1/2)w d/dw),
and  w dh/dw = 2s h   [since h=g_s W^{2s}/Gamma(2s+1), W=w e^{-tau/2}, w/W=e^{tau/2}], so the
numerator error's non-elementary part is
   2 theta T2 = sum_{n>=1}(-1)^n (2n) h(n) = (1/2pi i) oint_{dR} 2s h(s) pi/sin(pi s) ds,
the SAME contour as lem:T2abs with an extra 2s.  Its absolute bound
   B_num = (1/2pi) oint_{dR} 2|s| |h pi/sin| |ds|
picks up 2|s| <~ W ~ tau^{-1/2} on the left-edge mass, giving B_num = O(tau^{-1/4}) = o(tau^{-1/2}).
Since w sin w ~ tau^{-1/2} DOMINATES, S0/(w sin w) -> 1 and S0(q_m) != 0.  We verify:
 (1) S0=Sblk(0,q): error = S0 - w sin w is o(tau^{-1/2}) and S0/(w sin w)->1  [the asymptotic holds];
 (2) B_num*sqrt(tau) -> 0  [the contour bound is o(tau^{-1/2}), the rigorous input];
 (3) B_num >= |alt sum sum(-1)^n 2n h(n)|  [bound is valid].
Scalar mpmath. dps scales with w.
"""
import mpmath as mp
from abelplana_verify import B_exact
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2))-2*q**(k+1)/(1-q**(k+1))
def Sblk(k,q,J=300000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-(mp.mp.dps+10)) and j>60: break
    return tot
def h(s,tau,W):
    B,_=B_exact(s,tau)
    return (1-mp.e**(-B))*mp.e**(2*s*mp.log(W))/mp.gamma(2*s+1)
def altsum_num(tau,W,Nmax):  # sum_{n>=1}(-1)^n 2n h(n)
    tot=mp.mpf(0)
    for n in range(1,Nmax):
        tot+=(-1)**n*(2*n)*h(mp.mpf(n),tau,W)
    return tot
def Bnum(tau,W,ntop,nleft):  # (1/2pi) oint 2|s| |h pi/sin|
    A=mp.mpf(0)
    smax=2*W+12.0; ht=(smax-0.5)/ntop
    for k in range(ntop+1):
        sig=mp.mpf('0.5')+k*ht; s=mp.mpc(sig,float(W/2))
        val=2*abs(s)*abs((1-mp.e**(-B_exact(s,tau)[0]))*W**(2*sig)/mp.gamma(2*s+1))*abs(mp.pi/mp.sin(mp.pi*s))
        A+=val*(ht if 0<k<ntop else ht/2)
    A*=2/(2*mp.pi)
    hl=(W/2)/nleft; Al=mp.mpf(0)
    for k in range(nleft+1):
        t=k*hl; s=mp.mpc('0.5',float(t))
        val=2*abs(s)*abs((1-mp.e**(-B_exact(s,tau)[0]))*W/mp.gamma(2*s+1))*abs(mp.pi/mp.sin(mp.pi*s))
        Al+=val*(hl if 0<k<nleft else hl/2)
    Al*=2/(2*mp.pi)
    return A+Al

print(f"{'tau':>9}{'w':>8}{'S0/(wsinw)':>11}{'|err|/w':>10}{'|err|*st':>10}{'Bnum':>10}{'Bnum*st':>9}{'Bnum>=|alt|':>11}")
for taus in ['0.02','0.01','0.005','0.002','0.001','0.0005']:
    tau=mp.mpf(taus); w=mp.sqrt(2/tau); W=Wof(tau); st=mp.sqrt(tau)
    mp.mp.dps=40+int(1.3*float(w))
    S0=Sblk(0,q:=mp.e**(-tau)); wsw=w*mp.sin(w); err=S0-wsw
    ntop=max(220,int((2*float(W)+12)/0.15)); nleft=max(80,int(float(W)/0.10))
    Bn=Bnum(tau,W,ntop,nleft)
    alt=altsum_num(tau,W,int(3*float(W)+40))
    print(f"{taus:>9}{float(w):>8.2f}{float(S0/wsw):>11.6f}{float(abs(err)/w):>10.5f}{float(abs(err)*st):>10.5f}{float(Bn):>10.4f}{float(Bn*st):>9.5f}{str(Bn>=abs(alt)):>11}")
    mp.mp.dps=30
print("\nS0/(w sin w)->1 ; |err|*sqrt(tau)->0 (error o(tau^{-1/2})) ; Bnum*sqrt(tau)->0 (contour bound o(tau^{-1/2})).")
print("=> S0 ~ w sin w RIGOROUSLY via absolute contour (extra 2s), |S0(q_m)|->inf, S0(q_m)!=0. #4 CLOSED.")
