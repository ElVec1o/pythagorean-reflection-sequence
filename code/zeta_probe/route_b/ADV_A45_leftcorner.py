"""Analytic check: left-side integrand near corner. Use exact gamma & exact B (B_exact) at a FEW points only
so it's fast. Show integrand_left(t=W/2)*W-scale ~ O(1)*sqrt(tau)? and the integral of the left side
equals sqrt(tau) * h(tau) with h slowly growing. Tabulate h_left(tau)=A_left/sqrt(tau) at a few tau ONLY,
coarse grid, fast."""
import mpmath as mp
from abelplana_verify import B_exact
mp.mp.dps=25
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bval(s,tau):
    v,_=B_exact(s,tau); return v
print("Left side Re s=1/2 integrand profile and integral (coarse, fast):")
print(f"{'tau':>8}{'W':>7}{'A_left/st':>11}{'integ@t=0':>11}{'integ@W/2':>11}")
for taus in ['0.02','0.005','0.001','0.0002']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    n=40; h=(W/2)/n; Al=mp.mpf(0); first=None;last=None
    for k in range(n+1):
        t=k*h; s=mp.mpc(0.5,float(t)); g=1-mp.e**(-Bval(s,tau))
        Wcomb=W/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        val=abs(g)*Wcomb*psin
        if k==0:first=val
        if k==n:last=val
        wt=h if 0<k<n else h/2
        Al+=val*wt*2/(2*mp.pi)  # double for +-t, /2pi
    print(f"{taus:>8}{float(W):>7.2f}{mp.nstr(Al/st,5):>11}{mp.nstr(first,5):>11}{mp.nstr(last,5):>11}")
