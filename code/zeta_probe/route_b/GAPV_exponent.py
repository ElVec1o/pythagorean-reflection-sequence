"""
DEFINITIVE: the absolute dR bound's LEFT edge (Re s=1/2) is A_left ~ c tau^{1/4}, a POWER law.
Confirm exponent 1/4 and constant c over an extended range, and show A_left eventually EXCEEDS
the (false) claimed bound sqrt(tau)(0.08+0.011 log 1/tau). Left edge only (the tau^{1/4} carrier).
A_left = (1/2pi)*2*int_0^{W/2} |g_{1/2+it}| W/|Gamma(2+2it)| (pi/cosh(pi t)) dt.
Scalar mpmath dps=30. Uniform t-grid (integrand smooth, ~t^{3/2} growth, mass near t=W/2).
"""
import mpmath as mp, math
from abelplana_verify import B_exact
mp.mp.dps = 30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def A_left(tau, n=240):
    W=Wof(tau); hl=(W/2)/n; A=mp.mpf(0)
    for k in range(n+1):
        t=k*hl; s=mp.mpc('0.5',float(t))
        B,_=B_exact(s,tau); g=1-mp.e**(-B)
        val=abs(g)*W/abs(mp.gamma(2*s+1))*abs(mp.pi/mp.sin(mp.pi*s))
        wt=hl if 0<k<n else hl/2
        A+=val*wt
    return A*2/(2*mp.pi)
print(f"{'tau':>9}{'A_left':>12}{'A_left/t^.25':>13}{'A_left/st':>11}{'falsebnd√t(.08+.011L)':>21}{'exceeds?':>9}")
rows=[]
for taus in ['0.01','0.003','0.001','0.0003','0.0001','0.00003','0.00001']:
    tau=mp.mpf(taus); Al=A_left(tau); st=mp.sqrt(tau)
    q=float(Al/tau**mp.mpf('0.25')); fb=float(st*(mp.mpf('0.08')+mp.mpf('0.011')*mp.log(1/tau)))
    exc = float(Al) > fb
    rows.append((float(tau),float(Al),q,float(Al/st)))
    print(f"{taus:>9}{float(Al):>12.6f}{q:>13.6f}{float(Al/st):>11.4f}{fb:>21.6f}{str(exc):>9}")
# fit exponent: log A_left = a + p log tau
import math
xs=[math.log(r[0]) for r in rows]; ys=[math.log(r[1]) for r in rows]
n=len(xs); sx=sum(xs);sy=sum(ys);sxx=sum(x*x for x in xs);sxy=sum(x*y for x,y in zip(xs,ys))
p=(n*sxy-sx*sy)/(n*sxx-sx*sx); a=(sy-p*sx)/n
print(f"\nfit: A_left ~ {math.exp(a):.5f} * tau^{p:.5f}   (expect exponent ~ 0.25)")
print(f"=> absolute bound A = O(tau^1/4), NOT O(sqrt(tau) log 1/tau). Still ->0 (suffices for prop:signchanges).")
