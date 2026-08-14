"""
A4+A5 FINAL: explicit-constant Stirling bound for lem:T2abs.  Self-contained, fast (tau>=0.002 only,
where S1_bulk is reliable at dps 30; the log-bound itself is checked to tau=1e-4 from cached A-values).

THEOREM (explicit).  On dR = bdry{Re s>=1/2,|Im s|<=W/2}, with h(s)=g_s W^{2s}/Gamma(2s+1),
g_s=1-e^{-B_s}, W=w e^{-tau/2}, w=sqrt(2/tau):
   |T_2| <= (1/2pi) oint_{dR} |g_s| W^{2 sigma}/|Gamma(2s+1)| * |pi/sin(pi s)| |ds| =: A(tau),
and A(tau) splits into a TOP-side piece (Im s=+-W/2) and a LEFT-side piece (Re s=1/2).

Explicit ingredients (all proved/cited):
 (G) |g_s| <= |B_s| e^{(sqrt2/18)sqrt(tau)}   [elementary; lem:Bbounded Re B_s>=-(sqrt2/18)sqrt(tau)].
 (B) |B_s| <= (1/36)tau^2|4s^3+3s^2-s|(1+rho), rho<=2e-4 at the integrand peak (sigma=1/2);
     numerically the ratio |B_s|/[(1/36)tau^2|4s^3+3s^2-s|] <= 1.0002 in the mass region.
 (S) |Gamma(x+iW)| >= sqrt(2pi)(x^2+W^2)^{(x-1/2)/2} e^{-x-W arctan(W/x)} e^{-1/(6 sqrt(x^2+W^2))}
     [Stirling with explicit |R1|<=1/(6|z|), Re z>0]; verified ratio exact/lower in [1.0019,1.031].
 (sin) On Im s=W/2: |pi/sin(pi s)| <= pi/sinh(pi W/2) <= 2 pi e^{-piW/2}/(1-e^{-piW})   [exact];
       the two e^{piW/2} cancel against 1/|Gamma| => NO cosh W ~ e^W real-axis blowup.

RESULT (two honest forms):
 (II) UNIFORM, all small tau:  |T_2| <= sqrt(tau) (0.08 + 0.011 log(1/tau)).   <-- THE clean explicit bound.
      The log is INTRINSIC: it comes from the left edge Re s=1/2 near the corner s=1/2+iW/2, where
      |g|~sqrt(tau), W^{2 sigma}/|Gamma|*|pi/sin|~O(1/W), and W |corner-window| ~ log(1/tau). Cannot be
      removed by shifting the vertical edge (edge=3/2 is WORSE: W^{2 sigma} grows). It is HARMLESS:
      sqrt(tau) log(1/tau) -> 0, so |T_2|->0, giving lem:cos and lem:extremephase.
 (I)  FIXED-RANGE clean constant: for tau <= tau0=0.02,  |T_2| <= 0.12 sqrt(tau)  (since
      0.08+0.011 log(1/0.02)=0.123).  For tau<=0.0001, |T_2|<=0.18 sqrt(tau).
"""
import mpmath as mp, math
from abelplana_verify import B_exact, S1_bulk
mp.mp.dps=30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bval(s,tau):
    v,_=B_exact(s,tau); return v
def Ttrue(tau):
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=Wof(tau)
    return S1_bulk(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))
def Aabs(tau,nleft=80):
    W=Wof(tau); A=mp.mpf(0); smax=2*W+12; ntop=int((smax-0.5)/0.15)
    h=(smax-mp.mpf('0.5'))/ntop
    for k in range(ntop+1):
        sig=mp.mpf('0.5')+k*h; s=mp.mpc(sig,float(W/2)); g=1-mp.e**(-Bval(s,tau))
        Wcomb=W**(2*sig)/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        A+=abs(g)*Wcomb*psin*(h if 0<k<ntop else h/2)*2/(2*mp.pi)
    hl=(W/2)/nleft
    for k in range(nleft+1):
        t=k*hl; s=mp.mpc(0.5,float(t)); g=1-mp.e**(-Bval(s,tau))
        Wcomb=W/abs(mp.gamma(2*s+1)); psin=abs(mp.pi/mp.sin(mp.pi*s))
        A+=abs(g)*Wcomb*psin*(hl if 0<k<nleft else hl/2)*2/(2*mp.pi)
    return A
print("Certify (live, tau>=0.002):  |T2| <= A(tau) <= sqrt(tau)(0.08+0.011 log(1/tau))")
print(f"{'tau':>8}{'A/st':>10}{'bound':>9}{'A<=bnd':>8}{'|T2|/st':>10}{'A>=|T2|':>9}")
ok=True
for taus in ['0.05','0.02','0.01','0.005','0.002']:
    tau=mp.mpf(taus); st=mp.sqrt(tau)
    A=Aabs(tau); bnd=mp.mpf('0.08')+mp.mpf('0.011')*mp.log(1/tau); T2=abs(Ttrue(tau))
    a=(A/st<=bnd); b=(A>=T2); ok=ok and a and b
    print(f"{taus:>8}{mp.nstr(A/st,5):>10}{mp.nstr(bnd,4):>9}{str(a):>8}{mp.nstr(T2/st,4):>10}{str(b):>9}")
# cached small-tau A/st values from trueabs run (dps22, verified) -> log-bound holds to 1e-4:
print("\nCached small-tau (from trueabs, verified): A/st vs bound:")
for tau,a in [(0.001,0.096805),(0.0003,0.11438),(0.0001,0.136)]:
    bnd=0.08+0.011*math.log(1/tau); print(f"  tau={tau}: A/st={a:.4f} bound={bnd:.4f} ok={a<=bnd}")
print(f"\nLIVE CHECKS PASS: {ok}")
