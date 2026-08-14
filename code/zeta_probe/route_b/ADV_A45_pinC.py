"""
Pin the explicit constant. Two honest options:
 (O1) Use the SHARP cubic |B_s|<=(1/36)tau^2|4s^3+3s^2-s|*(1+rho), rho<=2e-4 in mass region (verified).
      Then |T2| <= e^{eps} (1+rho_max) (1/2pi) oint (1/36)tau^2|4s^3+3s^2-s| Wcomb |pi/sin| |ds|.
      Call this UB_sharp. Check UB_sharp/sqrt(tau) over a wide tau range -> single bounding C.
 (O2) crude 4|s|^3+3|s|^2+|s| (looser on left side).
We want the smallest clean C with UB/sqrt(tau) <= C for ALL tau in (0, tau0]. Scan to tiny tau.
"""
import mpmath as mp
mp.mp.dps=30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def contour(tau,h):
    W=Wof(tau); h=mp.mpf(h); pts=[]
    sig=mp.mpf('0.5')
    while sig<=2*W+15: pts.append((mp.mpc(sig,float(W/2)),2*h)); sig+=h
    t=mp.mpf(0)
    while t<=W/2: pts.append((mp.mpc(0.5,float(t)),2*h)); t+=h
    return pts
print(f"{'tau':>9}{'UBsharp/st':>12}{'UBcrude/st':>12}")
mx_s=mp.mpf(0); mx_c=mp.mpf(0)
for taus in ['0.05','0.02','0.01','0.005','0.002','0.001','0.0005','0.0002','0.0001','0.00005']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau); eps=mp.e**((mp.sqrt(2)/18)*st)
    Us=mp.mpf(0); Uc=mp.mpf(0)
    for s,wds in contour(tau,'0.1'):
        Wcomb=W**(2*mp.re(s))/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s)); a=abs(s)
        base=Wcomb*psin*wds/(2*mp.pi)
        Us+=abs(4*s**3+3*s**2-s)*base
        Uc+=(4*a**3+3*a**2+a)*base
    rho=mp.mpf('0.0002')
    UBs=eps*(1+rho)*(mp.mpf(1)/36)*tau**2*Us
    UBc=eps*(1+rho)*(mp.mpf(1)/36)*tau**2*Uc
    mx_s=max(mx_s,UBs/st); mx_c=max(mx_c,UBc/st)
    print(f"{taus:>9}{mp.nstr(UBs/st,5):>12}{mp.nstr(UBc/st,5):>12}")
print(f"max over scan: UBsharp/st={mp.nstr(mx_s,5)}  UBcrude/st={mp.nstr(mx_c,5)}")
