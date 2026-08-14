"""
GAP-V: split the absolute dR contour bound (1/2pi)oint|h pi/sin||ds| into TOP and LEFT edges,
fit each rate independently, and confirm sum >= |T2|. Exact g (B_exact), exact Gamma.
h(s)=g_s W^{2s}/Gamma(2s+1), g_s=1-e^{-B_s}. dR = bdry{Re s>=1/2, |Im s|<=W/2}.
  TOP/BOT (Im s=+-W/2, sigma in [1/2,inf)): claim O(sqrt tau) CONSTANT.
  LEFT   (Re s=1/2, |Im s|<=W/2):          claim O(sqrt tau log(1/tau)) -- the log source.
Scalar mpmath, dps 25, memory-safe. Coarse-but-adequate; we want RATES not 10 digits.
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk
mp.mp.dps = 25

def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bval(s,tau):
    v,_ = B_exact(s,tau); return v
def Ttrue(tau):
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=Wof(tau)
    return S1_bulk(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))

def A_top(tau, W, ntop):
    """(1/2pi) * 2 * int_{1/2}^{smax} |g| W^{2sig}/|Gamma(2s+1)| |pi/sin| dsig  (top+bottom)."""
    smax = 2*W+12.0; h=(smax-0.5)/ntop; A=mp.mpf(0)
    for k in range(ntop+1):
        sig=mp.mpf('0.5')+k*h; s=mp.mpc(sig,float(W/2))
        g=1-mp.e**(-Bval(s,tau))
        val=abs(g)*W**(2*sig)/abs(mp.gamma(2*s+1))*abs(mp.pi/mp.sin(mp.pi*s))
        wt=h if 0<k<ntop else h/2
        A+=val*wt
    return A*2/(2*mp.pi)

def A_left(tau, W, nleft):
    """(1/2pi) * 2 * int_0^{W/2} |g| W/|Gamma(2+2it)| |pi/cosh(pi t)| dt   (the +-t halves)."""
    hl=(W/2)/nleft; A=mp.mpf(0)
    for k in range(nleft+1):
        t=k*hl; s=mp.mpc('0.5',float(t))
        g=1-mp.e**(-Bval(s,tau))
        val=abs(g)*W/abs(mp.gamma(2*s+1))*abs(mp.pi/mp.sin(mp.pi*s))
        wt=hl if 0<k<nleft else hl/2
        A+=val*wt
    return A*2/(2*mp.pi)

print(f"{'tau':>9}{'W':>8}{'Atop/st':>10}{'Aleft/st':>10}{'A/st':>9}{'|T2|/st':>9}{'A>=|T2|':>8}")
rows=[]
for taus in ['0.05','0.02','0.01','0.005','0.002','0.001','0.0005','0.0002','0.0001']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    ntop=max(200,int((2*float(W)+12)/0.15)); nleft=max(60,int(float(W)/0.10))
    At=A_top(tau,W,ntop); Al=A_left(tau,W,nleft); A=At+Al
    T2=abs(Ttrue(tau))
    rows.append((float(tau),float(W),float(At/st),float(Al/st),float(A/st),float(T2/st)))
    print(f"{taus:>9}{float(W):>8.2f}{float(At/st):>10.4f}{float(Al/st):>10.4f}{float(A/st):>9.4f}{float(T2/st):>9.4f}{str(A>=T2):>8}")

# fit A_left/st = a + b*log(1/tau) ; A_top/st -> const
import math
print("\n--- rate fits ---")
xs=[math.log(1/r[0]) for r in rows]; yl=[r[3] for r in rows]; yt=[r[2] for r in rows]
n=len(xs); sx=sum(xs); sy=sum(yl); sxx=sum(x*x for x in xs); sxy=sum(x*y for x,y in zip(xs,yl))
b=(n*sxy-sx*sy)/(n*sxx-sx*sx); a=(sy-b*sx)/n
print(f"A_left/sqrt(tau) ~ {a:.4f} + {b:.4f}*log(1/tau)   [b>0 => genuine log growth]")
print(f"A_top/sqrt(tau): min={min(yt):.4f} max={max(yt):.4f} last={yt[-1]:.4f}  [flat => O(sqrt tau) constant]")
print(f"proposed uniform bound c0+c1 log(1/tau) with c0={a+max(yt):.3f}? check vs A/st:")
for r in rows:
    bnd=(a+max(yt))+b*math.log(1/r[0])
    print(f"  tau={r[0]:.4g}  A/st={r[4]:.4f}  c0+c1ln={bnd:.4f}  ok={r[4]<=bnd}")
