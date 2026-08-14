"""
Push left-edge scaling to small tau (down to 1e-4) to confirm the log law and
nail the slope b. S1_bulk reference is unreliable at tiny tau, but the contour
absolute integral A(tau) does NOT need S1_bulk -- it only needs B_exact, which
is a closed form valid at all tau. So we compute A and its edges only.
Use moderate dps and adaptive #points (left edge has width W/2 ~ 1/sqrt(tau), large).
"""
import mpmath as mp, math
from abelplana_verify import B_exact
mp.mp.dps = 25

def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bval(s,tau):
    v,_=B_exact(s,tau); return v
def integrand_abs(s,tau,logW):
    g=1-mp.e**(-Bval(s,tau))
    h=g*mp.e**(2*s*logW)/mp.gamma(2*s+1)
    return abs(h*mp.pi/mp.sin(mp.pi*s))

def edges(tau):
    W=Wof(tau); logW=mp.log(W); half=float(W/2)
    # top: sigma 1/2..2W+12, step ~0.1
    smax=2*float(W)+12.0; ntop=max(300,int((smax-0.5)/0.08)); h0=(smax-0.5)/ntop
    top=mp.mpf(0)
    for k in range(ntop+1):
        sig=mp.mpf('0.5')+k*h0
        v=integrand_abs(mp.mpc(sig,half),tau,logW)
        top+=v*(h0 if 0<k<ntop else h0/2)
    top/= (2*mp.pi)
    # left: t -half..half, need fine grid since width ~ W. step ~0.08
    nleft=max(300,int((2*half)/0.08)); hl=(2*half)/nleft
    left=mp.mpf(0)
    for k in range(nleft+1):
        t=-half+k*hl
        v=integrand_abs(mp.mpc('0.5',t),tau,logW)
        left+=v*(hl if 0<k<nleft else hl/2)
    left/=(2*mp.pi)
    return top,left

print(f"{'tau':>9}{'W':>8}{'top/st':>10}{'left/st':>10}{'A/st':>10}{'attackA/st':>11}")
attack={0.02:0.078,0.005:0.082,0.001:0.097,0.0003:0.114,0.0001:0.136}
rows=[]
for taus in ['0.02','0.005','0.001','0.0003','0.0001']:
    tau=mp.mpf(taus); st=mp.sqrt(tau)
    top,left=edges(tau); A=2*top+left
    rows.append((float(taus),float(left/st),float(A/st)))
    av=attack.get(float(taus),float('nan'))
    print(f"{taus:>9}{float(Wof(tau)):>8.1f}{mp.nstr(top/st,5):>10}{mp.nstr(left/st,5):>10}"
          f"{mp.nstr(A/st,5):>10}{av:>11}")

xs=[math.log(1/t) for t,_,_ in rows]; ysL=[l for _,l,_ in rows]; ysA=[a for _,_,a in rows]
def linfit(xs,ys):
    n=len(xs);sx=sum(xs);sy=sum(ys);sxx=sum(x*x for x in xs);sxy=sum(x*y for x,y in zip(xs,ys))
    b=(n*sxy-sx*sy)/(n*sxx-sx*sx);a=(sy-b*sx)/n
    ssr=sum((y-(a+b*x))**2 for x,y in zip(xs,ys));return a,b,ssr
aL,bL,sL=linfit(xs,ysL); aA,bA,sA=linfit(xs,ysA)
print(f"\nleft/st = {aL:.5f} + {bL:.5f} log(1/tau)  SSR={sL:.2e}")
print(f"A/st    = {aA:.5f} + {bA:.5f} log(1/tau)  SSR={sA:.2e}")
print(f"attack claims A/st bound = 0.08 + 0.011 log(1/tau); my A/st slope b={bA:.5f}")
# power-law alternative for A/st: ln(A/st) = c + alpha ln(log(1/tau))? check residuals.
print("\nIs A/st const? spread:", f"{min(ysA):.4f}..{max(ysA):.4f} ({max(ysA)/min(ysA):.2f}x) -> NOT const")
