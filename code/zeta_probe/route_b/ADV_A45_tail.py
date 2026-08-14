"""
Verify the explicit |B_s| <= (1/36)tau^2|4s^3+3s^2-s|*(1+tail) bound, tail explicit.
B_s = sum_{n>=1} phi_n tau^{2n}(P_n(2s)-s),  phi_n = (-1)^{n+1} zeta(2n)/(n (2pi)^{2n}).
P_n(M)=sum_{m=1}^M m^{2n} is a poly of degree 2n+1 with leading M^{2n+1}/(2n+1).
On the strip/contour |s|<= O(W)=O(tau^{-1/2}), so |2s|<= O(tau^{-1/2}), and
|phi_n tau^{2n} P_n(2s)| ~ |phi_n| tau^{2n} |2s|^{2n+1}/(2n+1) ~ |phi_n|/(2n+1) (tau |2s|^2)^n |2s|.
With tau|2s|^2 <= tau*4*(W/sqrt2... )^2.  Max |s| on contour mass ~ a few W. tau*(2W)^2 = tau*4*2/tau=8.
Hmm tau|2s|^2 can be O(1)! So the tail is NOT obviously small at large |s|. BUT large |s| is killed by Wcomb.
So the RIGHT statement is term-ratio of B-SERIES, weighted. Let's just numerically bound
   sup over contour-mass of  |B_s - B_s^{(1)}| / |B_s^{(1)}|     where B^{(1)} = n=1 term,
restricted to the region where Wcomb*|pi/sin| is within 1e-6 of its max (the mass region).
"""
import mpmath as mp
from lemcos_Bstrip import B_gamma
mp.mp.dps=25
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def B1(s,tau):  # n=1 term
    return (mp.mpf(1)/36)*tau**2*(4*s**3+3*s**2-s)

# Also: ratio |B_s|/( (1/36)tau^2|4s^3+3s^2-s| ) in mass region -> bound the multiplicative const.
print("In the Wcomb-weighted mass region, ratio |B_s| / [(1/36)tau^2|4s^3+3s^2-s|]:")
for taus in ['0.02','0.01','0.005']:
    tau=mp.mpf(taus); W=Wof(tau)
    # mass region: sigma in [1/2, 4] on top (where integrand peaks), plus left side small t
    worst=mp.mpf(0); worst_at=None
    for sig in [0.5,1,1.5,2,3,4,6,8]:
        s=mp.mpc(sig,float(W/2)); B=B_gamma(s,tau,3000)
        denom=(mp.mpf(1)/36)*tau**2*abs(4*s**3+3*s**2-s)
        r=abs(B)/denom
        if r>worst: worst=r; worst_at=('top',sig)
    for t in [0.5,2,4,float(W/4),float(W/2)]:
        s=mp.mpc(0.5,float(t)); B=B_gamma(s,tau,3000)
        denom=(mp.mpf(1)/36)*tau**2*abs(4*s**3+3*s**2-s)
        if denom>0:
            r=abs(B)/denom
            if r>worst: worst=r; worst_at=('left',t)
    print(f"tau={taus} W={float(W):.2f}: worst ratio={mp.nstr(worst,5)} at {worst_at}")
