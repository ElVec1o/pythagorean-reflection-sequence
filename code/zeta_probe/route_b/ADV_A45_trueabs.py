"""
The REAL question for A4/A5: is the TRUE absolute-contour integral
  A(tau) := (1/2pi) oint_{dR} |g_s| Wcomb |pi/sin| |ds|
bounded by C sqrt(tau) with a SINGLE constant C for all small tau?  (This is lem:T2abs as written.)
Use fast B_exact. Scan to small tau. Also split top/left to locate any growth.
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk
mp.mp.dps=30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bval(s,tau):
    v,_=B_exact(s,tau); return v
def Tt(tau):
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=Wof(tau)
    return S1_bulk(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))
print(f"{'tau':>9}{'A_top/st':>11}{'A_left/st':>11}{'A_tot/st':>11}{'|T2|/st':>10}")
for taus in ['0.02','0.005','0.001','0.0003','0.0001']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau); h=mp.mpf('0.12')
    At=mp.mpf(0); Al=mp.mpf(0)
    sig=mp.mpf('0.5')
    while sig<=2*W+12:
        s=mp.mpc(sig,float(W/2)); g=1-mp.e**(-Bval(s,tau))
        Wcomb=W**(2*sig)/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        At+=abs(g)*Wcomb*psin*2*h/(2*mp.pi); sig+=h
    t=mp.mpf(0)
    while t<=W/2:
        s=mp.mpc(0.5,float(t)); g=1-mp.e**(-Bval(s,tau))
        Wcomb=W/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        Al+=abs(g)*Wcomb*psin*2*h/(2*mp.pi); t+=h
    print(f"{taus:>9}{mp.nstr(At/st,5):>11}{mp.nstr(Al/st,5):>11}{mp.nstr((At+Al)/st,5):>11}{mp.nstr(abs(Tt(tau))/st,4):>10}")
