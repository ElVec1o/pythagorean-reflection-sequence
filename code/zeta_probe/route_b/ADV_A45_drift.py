"""Does t^2 M3/sqrt(tau) stay bounded as tau->0? If it grows ~log, then C grows and the explicit
constant must be stated as C(tau0) for tau<=tau0 with explicit tau0. Investigate the source: split M3
into top-side and left-side contributions; check whether the growth is the sigma-tail on top side."""
import mpmath as mp
mp.mp.dps=30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def M3parts(tau,h):
    W=Wof(tau); h=mp.mpf(h); Mtop=mp.mpf(0); Mleft=mp.mpf(0)
    sig=mp.mpf('0.5')
    while sig<=2*W+15:
        s=mp.mpc(sig,float(W/2)); Wcomb=W**(2*sig)/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        Mtop+=abs(s)**3*Wcomb*psin*2*h/(2*mp.pi); sig+=h
    t=mp.mpf(0)
    while t<=W/2:
        s=mp.mpc(0.5,float(t)); Wcomb=W**(1)/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        Mleft+=abs(s)**3*Wcomb*psin*2*h/(2*mp.pi); t+=h
    return Mtop,Mleft
print(f"{'tau':>9}{'t^2 Mtop/st':>13}{'t^2 Mleft/st':>13}{'total':>10}")
for taus in ['0.02','0.005','0.001','0.0003','0.0001']:
    tau=mp.mpf(taus); st=mp.sqrt(tau)
    Mt,Ml=M3parts(tau,'0.1')
    print(f"{taus:>9}{mp.nstr(tau**2*Mt/st,5):>13}{mp.nstr(tau**2*Ml/st,5):>13}{mp.nstr(tau**2*(Mt+Ml)/st,5):>10}")
