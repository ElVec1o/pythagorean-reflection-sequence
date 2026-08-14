"""
FINAL AUDIT of lem:T2abs (A4/A5).  The tex claims:
    |T_2| <= (1/2pi) oint_{dR} |h(s) pi/sin(pi s)| |ds| = O(sqrt tau),  <= 0.078 sqrt tau,
with dR = boundary of R = {Re s >= 1/2, |Im s| <= W/2}.
That boundary has THREE pieces (R extends to Re s = +inf, integrand factorially small there):
  - top horizontal   Im s = +W/2, sigma in [1/2, inf)
  - bottom horizontal Im s = -W/2, sigma in [1/2, inf)
  - left vertical     Re s = 1/2,  t in [-W/2, W/2]
The published script ADV_Bound3_abscontour.py integrates ONLY the top horizontal from sigma=0.
This audit integrates the FULL boundary as written, separating the three contributions,
to determine the TRUE rate: O(sqrt tau) or O(sqrt tau * log(1/tau))?
Also recomputes the SIGNED integral on dR to confirm it equals T_2 (deformation legality).
"""
import mpmath as mp
from lemcos_Bstrip import B_gamma
from abelplana_verify import S1_bulk
mp.mp.dps = 22
I = mp.mpc(0, 1)

def T2_true(tau):
    q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return S1_bulk(q) - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

def h(s, tau):
    B = B_gamma(s, tau, 300)
    W = mp.sqrt(2/tau)*mp.e**(-tau/2)
    return (1-mp.e**(-B)) * mp.e**(2*s*mp.log(W)) / mp.gamma(2*s+1)

def kern(s, tau):
    return h(s, tau) * mp.pi/mp.sin(mp.pi*s)

print(f"{'tau':>8} {'W':>8} {'top':>11} {'bottom':>11} {'left':>11} {'sum_abs':>11} "
      f"{'/sqrt(tau)':>10} {'/sqrt log':>10} {'|T2|/st':>9} {'sign chk':>10}")
for taus in ['0.05','0.02','0.01','0.005','0.002']:
    tau = mp.mpf(taus); W = mp.sqrt(2/tau)*mp.e**(-tau/2)
    st = mp.sqrt(tau)
    # --- top & bottom horizontals: sigma in [1/2, smax], integrand decays factorially ---
    smax = float(1.5*W + 8); h0 = mp.mpf('0.2'); n = int((smax-0.5)/float(h0))
    def horiz_abs(sign):
        pts = [abs(kern(mp.mpc(0.5+k*float(h0), sign*float(W/2)), tau)) for k in range(n+1)]
        return (mp.fsum(pts) - (pts[0]+pts[-1])/2)*h0
    top = horiz_abs(+1); bot = horiz_abs(-1)
    # --- left vertical Re s = 1/2, t in [-W/2, W/2] ---
    m = 120; dt = W/m
    ptsL = [abs(kern(mp.mpc(0.5, float(-W/2 + k*dt)), tau)) for k in range(m+1)]
    left = (mp.fsum(ptsL) - (ptsL[0]+ptsL[-1])/2)*dt
    sum_abs = (top+bot+left)/(2*mp.pi)   # the (1/2pi) prefactor
    # --- signed integral around dR (legality of deformation) : (1/2pi i) oint ---
    # orientation: counterclockwise around R (R is to the right). Top L->R? Use closed: top(R->L)+left(down)+bot(L->R)...
    # Simpler legality check: does |T2| <= sum_abs hold AND is sum_abs the right order.
    chk = sum_abs >= abs(T2_true(tau))
    log_t = mp.log(1/tau)
    print(f"{taus:>8} {float(W):>8.3f} {mp.nstr(top/(2*mp.pi),5):>11} {mp.nstr(bot/(2*mp.pi),5):>11} "
          f"{mp.nstr(left/(2*mp.pi),5):>11} {mp.nstr(sum_abs,5):>11} "
          f"{mp.nstr(sum_abs/st,5):>10} {mp.nstr(sum_abs/(st*log_t),5):>10} "
          f"{mp.nstr(abs(T2_true(tau))/st,4):>9} {str(chk):>10}")
print()
print("READ: if sum_abs/sqrt(tau) GROWS while sum_abs/(sqrt(tau) log(1/tau)) is FLAT,")
print("then the FULL-boundary bound is O(sqrt(tau) log(1/tau)), NOT a clean O(sqrt(tau)).")
print("The 'left' column isolates the vertical-edge leak the synthesis flagged.")
