"""
Does moving the left vertical edge from Re s=1/2 to Re s = c (constant > 1/2) remove the log growth?
The residue rep needs the contour to enclose integers n>=1, so the left edge must be in (0,1) to keep n=1
inside, OR we accept losing n=1 and add its residue back. Simplest: keep Re s=1/2.
Alternative: the log comes from the corner region |s|~W/2 on the LEFT edge where |g|~sqrt(tau) and
Wcomb*|pi/sin|~O(1/W)? Let's instead test: is the growth REAL or a discretization artifact?
Refine the left-side integration (finer grid) at fixed tau and check A_left/st stable. Then test edge at
Re s=1/2 vs Re s=3/2 (add residue at n=1 explicitly: Res = h(1) = g_1 W^2/Gamma(3), the n=1 term of T2).
"""
import mpmath as mp
from abelplana_verify import B_exact
mp.mp.dps=25
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bval(s,tau):
    v,_=B_exact(s,tau); return v
def left_integral(tau, ReEdge, n=80):
    W=Wof(tau); h=(W/2)/n; Al=mp.mpf(0)
    for k in range(n+1):
        t=k*h; s=mp.mpc(float(ReEdge),float(t)); g=1-mp.e**(-Bval(s,tau))
        Wcomb=W**(2*ReEdge)/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        wt=h if 0<k<n else h/2
        Al+=abs(g)*Wcomb*psin*wt*2/(2*mp.pi)
    return Al
print("Left-edge integral A_left/sqrt(tau) at Re s = 1/2 vs 3/2 (refined n=80):")
print(f"{'tau':>8}{'edge=1/2':>11}{'edge=3/2':>11}")
for taus in ['0.02','0.005','0.001']:
    tau=mp.mpf(taus); st=mp.sqrt(tau)
    a05=left_integral(tau,0.5); a15=left_integral(tau,1.5)
    print(f"{taus:>8}{mp.nstr(a05/st,5):>11}{mp.nstr(a15/st,5):>11}")
print("(if edge=3/2 also grows -> log is intrinsic to the vertical edge near the corner, not removable by small shift)")
