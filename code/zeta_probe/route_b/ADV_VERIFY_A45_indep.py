"""
INDEPENDENT adversarial verification of the A4+A5 attack.
Claim under test: |T_2| <= A(tau) = (1/2pi) oint_{dR} |h pi/sin| |ds|, and
A(tau)/sqrt(tau) is NOT bounded by a constant but grows like 0.08 + 0.011 log(1/tau),
the growth coming from the LEFT vertical edge Re s = 1/2.

I rebuild the closed-contour absolute integral from scratch, splitting the THREE
relevant edges (top Im s=+W/2, bottom Im s=-W/2, left Re s=1/2) and tracking each
separately. By symmetry top==bottom; I compute top once and double it.

dR = boundary of R = {Re s >= 1/2, |Im s| <= W/2}, traversed so it encircles the
integers n>=1. The right edge (Re s -> +inf) vanishes by factorial decay.

h(s) = g_s W^{2s}/Gamma(2s+1), g_s = 1 - e^{-B_s}, B_s via B_exact (abel-plana closed form).
Reference |T_2| via S1_bulk.
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk
mp.mp.dps = 30
I = mp.mpc(0,1)

def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bval(s,tau):
    v,_ = B_exact(s,tau); return v
def Ttrue(tau):
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=Wof(tau)
    # T_2 = S1_bulk - (1-cos w) - (cos w - cos W)
    return S1_bulk(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))

def integrand_abs(s,tau):
    g = 1 - mp.e**(-Bval(s,tau))
    h = g * mp.e**(2*s*mp.log(Wof(tau))) / mp.gamma(2*s+1)
    return abs(h * mp.pi/mp.sin(mp.pi*s))

def edge_top(tau, npts=400):
    """Im s = +W/2, sigma from 1/2 to smax. Returns integral of |.| d sigma /(2pi)."""
    W = Wof(tau); smax = 2*float(W)+12.0
    h0 = (smax-0.5)/npts
    acc = mp.mpf(0)
    for k in range(npts+1):
        sig = mp.mpf('0.5') + k*h0
        v = integrand_abs(mp.mpc(sig, float(W/2)), tau)
        w8 = h0 if 0<k<npts else h0/2
        acc += v*w8
    return acc/(2*mp.pi)

def edge_left(tau, npts=400):
    """Re s = 1/2, t from -W/2 to +W/2. Returns integral of |.| dt /(2pi)."""
    W = Wof(tau); half = float(W/2)
    h0 = (2*half)/npts
    acc = mp.mpf(0)
    for k in range(npts+1):
        t = -half + k*h0
        v = integrand_abs(mp.mpc('0.5', t), tau)
        w8 = h0 if 0<k<npts else h0/2
        acc += v*w8
    return acc/(2*mp.pi)

print("Edges separated. A = 2*top + left (top==bottom by symmetry).")
print(f"{'tau':>9}{'top/st':>10}{'left/st':>10}{'A/st':>10}{'|T2|/st':>10}{'A>=|T2|':>9}{'bound':>9}")
rows=[]
for taus in ['0.05','0.02','0.01','0.005','0.002','0.001']:
    tau=mp.mpf(taus); st=mp.sqrt(tau)
    top=edge_top(tau); left=edge_left(tau)
    A=2*top+left
    T2=abs(Ttrue(tau))
    bnd=mp.mpf('0.08')+mp.mpf('0.011')*mp.log(1/tau)
    rows.append((float(taus),float(left/st),float(A/st)))
    print(f"{taus:>9}{mp.nstr(top/st,5):>10}{mp.nstr(left/st,5):>10}{mp.nstr(A/st,5):>10}"
          f"{mp.nstr(T2/st,5):>10}{str(A>=T2):>9}{mp.nstr(bnd,4):>9}")

# Scaling analysis of left/st: fit  y = a + b*log(1/tau)  vs power law.
print("\nLeft-edge scaling: is left/st ~ a + b log(1/tau) (log) or ~ const?")
import math
xs=[math.log(1/t) for t,_,_ in rows]; ys=[l for _,l,_ in rows]
n=len(xs); sx=sum(xs); sy=sum(ys); sxx=sum(x*x for x in xs); sxy=sum(x*y for x,y in zip(xs,ys))
b=(n*sxy-sx*sy)/(n*sxx-sx*sx); a=(sy-b*sx)/n
resid=sum((y-(a+b*x))**2 for x,y in zip(xs,ys))
print(f"  log-fit left/st = {a:.5f} + {b:.5f}*log(1/tau),  SSR={resid:.2e}")
print(f"  spread of left/st over tau in [0.001,0.05]: {min(ys):.4f} .. {max(ys):.4f}  (ratio {max(ys)/min(ys):.2f}x)")
print("  => if left/st rises substantially & log-fit is tight, attack's log claim is corroborated.")
