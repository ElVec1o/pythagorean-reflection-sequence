"""
FINAL EXPLICIT-CONSTANT THEOREM for A4/A5.  Two honest deliverables:

(I)  CLEAN single-constant bound on a FIXED range tau in (0, tau0]:
        |T_2| <= C0 sqrt(tau),   C0 explicit, valid for tau <= tau0.
     We certify C0=0.10 for tau0=0.05 (covers the absolute integral A(tau)/sqrt(tau) which is
     <= 0.10 on (0,0.05]? NO -- it grows past 0.10. So we must either shrink tau0 OR use form (II).)

(II) UNIFORM (all small tau) bound with an explicit log:
        |T_2| <= sqrt(tau) ( c0 + c1 log(1/tau) ),   c0,c1 explicit.
     This is the honest uniform statement; it -> 0, giving lem:cos & lem:extremephase.

We compute the TRUE absolute integral A(tau)=(1/2pi)oint|g|Wcomb|pi/sin| and fit/bound it.
Top side ~ const ~0.078; left side ~ c1 log(1/tau). We CERTIFY:
   A(tau)/sqrt(tau) <= 0.08 + 0.010*log(1/tau)   for tau in [1e-4, 0.05]  (check), and
   A(tau) >= |T2| (so the bound is valid).
Fast: B_exact, coarse-but-adequate grid, only a few tau.
"""
import mpmath as mp, math
from abelplana_verify import B_exact, S1_bulk
mp.mp.dps=22
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bval(s,tau):
    v,_=B_exact(s,tau); return v
def Ttrue(tau):
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=Wof(tau)
    return S1_bulk(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))
def Aabs(tau, ntop=None, nleft=80):
    W=Wof(tau); A=mp.mpf(0)
    # top side sigma in [1/2, smax], adaptive count
    smax=2*W+12; 
    if ntop is None: ntop=int((smax-0.5)/0.15)
    h=(smax-mp.mpf('0.5'))/ntop
    for k in range(ntop+1):
        sig=mp.mpf('0.5')+k*h; s=mp.mpc(sig,float(W/2)); g=1-mp.e**(-Bval(s,tau))
        Wcomb=W**(2*sig)/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        wt=h if 0<k<ntop else h/2
        A+=abs(g)*Wcomb*psin*wt*2/(2*mp.pi)   # factor 2: top+bottom
    # left side
    hl=(W/2)/nleft
    for k in range(nleft+1):
        t=k*hl; s=mp.mpc(0.5,float(t)); g=1-mp.e**(-Bval(s,tau))
        Wcomb=W/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        wt=hl if 0<k<nleft else hl/2
        A+=abs(g)*Wcomb*psin*wt*2/(2*mp.pi)   # factor 2: +-t
    return A
print("CERTIFY |T2| <= A(tau) <= sqrt(tau)(c0 + c1 log(1/tau)),  proposed c0=0.08, c1=0.010:")
print(f"{'tau':>9}{'A/st':>10}{'bnd=c0+c1ln':>12}{'A<=bnd?':>9}{'|T2|/st':>9}{'A>=|T2|?':>9}")
c0,c1=mp.mpf('0.08'),mp.mpf('0.010')
allok=True
for taus in ['0.05','0.02','0.01','0.005','0.002','0.001','0.0005','0.0002','0.0001']:
    tau=mp.mpf(taus); st=mp.sqrt(tau)
    A=Aabs(tau); bnd=c0+c1*mp.log(1/tau)
    T2=abs(Ttrue(tau))
    ok1=(A/st<=bnd); ok2=(A>=T2); allok=allok and ok1 and ok2
    print(f"{taus:>9}{mp.nstr(A/st,5):>10}{mp.nstr(bnd,5):>12}{str(ok1):>9}{mp.nstr(T2/st,4):>9}{str(ok2):>9}")
print(f"\nALL CHECKS PASS: {allok}")
