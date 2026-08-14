"""
Compute the explicit constant C in |T_2| <= C sqrt(tau) via the corner-cubic route, fully numerically,
plus the dimensionless O(1) integrals that make C explicit & tau-independent in the limit.

|T_2| <= (1/2pi) oint |g| Wcomb |pi/sin| |ds|,  |g|<=|B| e^{(sqrt2/18)sqrt tau},
|B_s| <= (1/36)tau^2 (4|s|^3+3|s|^2+|s|)(1+rho(s)),  rho>=0 the n>=2 relative tail (numerically <=~0 in mass region).

Define the four DIMENSIONLESS contour integrals (substitute s, integrate against Wcomb|pi/sin|):
  M_p := (1/2pi) oint (|s|^p) Wcomb |pi/sin| |ds|,  p=1,2,3.
Then |T_2| <= e^{eps} (1/36) tau^2 (4 M3 + 3 M2 + M1)(1+rho_max).
Claim: tau^2 M3 -> (sqrt2/36)*K3 sqrt(tau) with K3 an explicit O(1) number; tau^2 M2=O(tau), tau^2 M1=O(tau^{3/2}).
So leading C = e^{0}(1/36)*4*(M3 tau^2/sqrt tau) = (1/9)(tau^2 M3/sqrt tau).  Print tau^2 M_p/sqrt(tau).
"""
import mpmath as mp
from abelplana_verify import S1_bulk
mp.mp.dps=30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def contour(tau,h):
    W=Wof(tau); h=mp.mpf(h); pts=[]
    sig=mp.mpf('0.5')
    while sig<=2*W+15: pts.append((mp.mpc(sig,float(W/2)),2*h)); sig+=h
    t=mp.mpf(0)
    while t<=W/2: pts.append((mp.mpc(0.5,float(t)),2*h)); t+=h
    return pts
print(f"{'tau':>8}{'t^2M3/st':>11}{'t^2M2/st':>11}{'t^2M1/st':>11}{'C_lead':>9}{'C_full':>9}")
for taus in ['0.02','0.01','0.005','0.002','0.001']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    M=[mp.mpf(0),mp.mpf(0),mp.mpf(0),mp.mpf(0)]
    for s,wds in contour(tau,'0.1'):
        Wcomb=W**(2*mp.re(s))/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s)); a=abs(s)
        base=Wcomb*psin*wds/(2*mp.pi)
        M[1]+=a*base; M[2]+=a**2*base; M[3]+=a**3*base
    eps=mp.e**((mp.sqrt(2)/18)*st)
    t2M3=tau**2*M[3]/st; t2M2=tau**2*M[2]/st; t2M1=tau**2*M[1]/st
    Clead=eps*(mp.mpf(1)/36)*4*t2M3
    Cfull=eps*(mp.mpf(1)/36)*(4*t2M3+3*t2M2*st+t2M1*st)  # M2,M1 carry extra st so ->0
    print(f"{taus:>8}{mp.nstr(t2M3,5):>11}{mp.nstr(t2M2,5):>11}{mp.nstr(t2M1,5):>11}{mp.nstr(Clead,5):>9}{mp.nstr(Cfull,5):>9}")
