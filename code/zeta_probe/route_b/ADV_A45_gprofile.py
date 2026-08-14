import mpmath as mp
from lemcos_Bstrip import B_gamma
mp.mp.dps=30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
# |g_s| on top side s=sigma+iW/2.  g=1-e^{-B}. Show |g_s| ~ |B_s| (small) near corner, and where it sits.
print("Profile of |g_s| and the full integrand on top side:")
for taus in ['0.01']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    print(f"tau={taus} W={float(W):.3f} W/2={float(W/2):.3f} sqrt(tau)={float(st):.5f}")
    print(f"{'sigma':>7}{'|B_s|':>12}{'|g_s|':>12}{'Wcomb':>12}{'|pi/sin|':>12}{'integrand':>12}")
    for sig in [0.5,1,2,3,5,float(W/4),float(W/2),float(W)]:
        s=mp.mpc(sig,float(W/2))
        B=B_gamma(s,tau,4000); g=1-mp.e**(-B)
        Wcomb=W**(2*sig)/abs(mp.gamma(mp.mpc(2*sig+1,float(W))))
        psin=abs(mp.pi/mp.sin(mp.pi*s))
        integ=abs(g)*Wcomb*psin
        print(f"{sig:>7.2f}{mp.nstr(abs(B),5):>12}{mp.nstr(abs(g),5):>12}{mp.nstr(Wcomb,5):>12}{mp.nstr(psin,5):>12}{mp.nstr(integ,5):>12}")
