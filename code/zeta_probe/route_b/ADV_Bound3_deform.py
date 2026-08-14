"""
BOUND 3 clean route -- finish: (i) vertical segment at sigma=1/2 is also O(sqrt tau);
(ii) the deformation is VALID: signed contour integral over the rectangle boundary
{Re s>=1/2, |Im s|<=W/2} reproduces T_2 (so |T_2| <= (1/2)*perimeter |h pi/sin| = O(sqrt tau)).
Contour encloses integers 1,2,...; h analytic for Re s>0 (poles of g_s in Re s<0); integrand->0 at
sigma=+inf (factorial). T_2=(1/2i) oint = sum_n (-1)^n h(n).
Scalar mpmath, dps 30, K=2000, memory-safe.
"""
import mpmath as mp
from lemcos_Bstrip import B_gamma
from abelplana_verify import S1_bulk
mp.mp.dps = 30
I = mp.mpc(0,1)

def setup(tau):
    tau=mp.mpf(tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); return tau,w,W
def T2_true(tau):
    tau,w,W=setup(tau); return S1_bulk(mp.e**(-tau)) - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))
def hps(s, tau, W, K=2000):   # h(s)*pi/sin(pi s)
    B=B_gamma(s,tau,K); h=(1-mp.e**(-B))*mp.e**(2*s*mp.log(W))/mp.gamma(2*s+1)
    return h*mp.pi/mp.sin(mp.pi*s)

print(f"{'tau':>7} {'W':>8} {'A_top(>=1/2)':>13} {'A_vert':>11} {'A_vert/sqrtt':>12} {'(1/2)(2A_top+A_vert)':>20} {'|T2|':>11} {'signed=T2?':>12}")
for taus in ['0.05','0.02','0.01']:
    tau,w,W=setup(taus); st=mp.sqrt(tau); smax=float(2*W+10); h0=mp.mpf('0.1')
    # top ray Im=+W/2, sigma in [1/2, smax]
    sig=[mp.mpf('0.5')+k*h0 for k in range(int((smax-0.5)/float(h0))+1)]
    top_vals=[hps(mp.mpc(x,float(W/2)),tau,W) for x in sig]
    A_top=(mp.fsum(abs(v) for v in top_vals)-(abs(top_vals[0])+abs(top_vals[-1]))/2)*h0
    I_top=(mp.fsum(top_vals)-(top_vals[0]+top_vals[-1])/2)*h0
    # bottom ray Im=-W/2
    bot_vals=[hps(mp.mpc(x,float(-W/2)),tau,W) for x in sig]
    I_bot=(mp.fsum(bot_vals)-(bot_vals[0]+bot_vals[-1])/2)*h0
    # vertical sigma=1/2, t in [-W/2, W/2]
    tt=[mp.mpf(-1)*W/2+k*h0 for k in range(int(float(W)/float(h0))+1)]
    vert_vals=[hps(mp.mpc('0.5',float(t)),tau,W) for t in tt]
    A_vert=(mp.fsum(abs(v) for v in vert_vals)-(abs(vert_vals[0])+abs(vert_vals[-1]))/2)*h0
    I_vert=(mp.fsum(vert_vals)-(vert_vals[0]+vert_vals[-1])/2)*h0*I   # ds=i dt
    # signed contour: up vertical (t:-W/2->W/2) + top (sigma:1/2->inf) - bottom(sigma:1/2->inf, i.e. inf->1/2)
    signed=(1/(2*I))*(I_vert + I_top - I_bot)
    T2=T2_true(taus); bound=(A_top*2+A_vert)/2
    ok = abs(signed-T2)/max(abs(T2),st) < mp.mpf('0.05')
    print(f"{taus:>7} {float(W):>8.3f} {mp.nstr(A_top,6):>13} {mp.nstr(A_vert,6):>11} {mp.nstr(A_vert/st,5):>12} {mp.nstr(bound,6):>20} {mp.nstr(abs(T2),5):>11} {str(ok)+' '+mp.nstr(mp.re(signed),4):>12}")
print()
print("Need: A_vert/sqrtt BOUNDED (vertical also O(sqrt tau)); bound=(1/2)perimeter >= |T2|; signed≈T2 (valid).")
print("Then |T2| <= (1/2)*perimeter integral |h pi/sin| = O(sqrt tau), CLEAN absolute bound. V closes.")
