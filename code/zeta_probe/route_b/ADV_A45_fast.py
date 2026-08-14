"""Fast version: use B_exact (abelplana, q-Bessel/loggamma closed form) instead of K-truncated sum."""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk
mp.mp.dps=22
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bs(s,tau): return mp.re(B_exact(s,tau)[0]) + 1j*mp.im(B_exact(s,tau)[0])
def Bval(s,tau):
    v,_=B_exact(s,tau); return v
def T2_true(tau):
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=Wof(tau)
    return S1_bulk(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))

# (1) tail/multiplicative const
print("ratio |B_s|/[(1/36)tau^2|4s^3+3s^2-s|] in mass region:")
for taus in ['0.02','0.01','0.005']:
    tau=mp.mpf(taus); W=Wof(tau); worst=mp.mpf(0); wat=None
    for sig in [0.5,1,2,3,4,6,8]:
        s=mp.mpc(sig,float(W/2)); B=Bval(s,tau)
        d=(mp.mpf(1)/36)*tau**2*abs(4*s**3+3*s**2-s)
        r=abs(B)/d
        if r>worst: worst=r;wat=('top',sig)
    for t in [0.5,2,float(W/4),float(W/2)]:
        s=mp.mpc(0.5,float(t)); B=Bval(s,tau)
        d=(mp.mpf(1)/36)*tau**2*abs(4*s**3+3*s**2-s)
        if d>0:
            r=abs(B)/d
            if r>worst: worst=r;wat=('left',t)
    print(f"  tau={taus}: worst={mp.nstr(worst,5)} at {wat}")

# (2) master bound
print("\nMASTER:")
print(f"{'tau':>7}{'W':>7}{'R1/2pi/st':>11}{'R1UB/2pi/st':>12}{'|T2|/st':>9}{'UB>=|T2|':>9}")
def contour(tau,h):
    W=Wof(tau); h=mp.mpf(h); pts=[]
    sig=mp.mpf('0.5')
    while sig<=2*W+12: pts.append((mp.mpc(sig,float(W/2)),2*h)); sig+=h
    t=mp.mpf(0)
    while t<=W/2: pts.append((mp.mpc(0.5,float(t)),2*h)); t+=h
    return pts
for taus in ['0.02','0.01','0.005','0.002']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau); fac=mp.e**((mp.sqrt(2)/18)*st)
    R1=mp.mpf(0); R1UB=mp.mpf(0)
    for s,wds in contour(tau,'0.12'):
        Wcomb=W**(2*mp.re(s))/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        B=Bval(s,tau); g=1-mp.e**(-B); a=abs(s)
        R1+=abs(g)*Wcomb*psin*wds
        Bub=fac*(mp.mpf(1)/36)*tau**2*(4*a**3+3*a**2+a)*1.05
        R1UB+=Bub*Wcomb*psin*wds
    T2=abs(T2_true(tau))
    print(f"{taus:>7}{float(W):>7.2f}{mp.nstr(R1/(2*mp.pi)/st,5):>11}{mp.nstr(R1UB/(2*mp.pi)/st,5):>12}{mp.nstr(T2/st,4):>9}{str(R1UB/(2*mp.pi)>=T2):>9}")
