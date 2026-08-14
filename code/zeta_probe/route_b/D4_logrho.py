"""
D4 step 2: Derive c_T for the TRAVEL block by the SAME mechanism as transcendence.tex
for S_1, but with the travel-block end factors A_k, C_k.

Travel block:  Sigma_1 = sum_{j>=0} (-1)^j t^T_j,   t^T_j = A_{1+2j} prod_{i<j} |C_{1+2i}|.
Leading model:  hat t_j = (2/tau)^{j+1}/(2j+2)!   [SAME as S_1 -> sum = 1-cos w].
Form factor:    rho^T_j = t^T_j / hat t_j.

We compute log rho^T_j numerically in the saddle window j ~ w = sqrt(2/tau) and fit
   log rho^T_j = a1*(j+1)*tau + a3*tau^2*j^3 + ...
to extract the linear coefficient a1 and cubic coefficient a3.

For S_1 (bulk):   a1 = -1,  a3 = -1/9   =>  c_1 = -1/sqrt2 + sqrt2/36 = -17 sqrt2/36.
Claim for travel: a1 = 0 (or different), a3 such that c_T = +sqrt2/36.

The map from (a1,a3) to c via the vartheta resummation (tex lines 191-196):
   linear term  a1*(j+1)*tau  -> contributes  a1 * (1/sqrt2) * sqrt(tau) * sin w   (note sign in tex: -1 -> -1/sqrt2)
   cubic  term  a3*tau^2*j^3  -> contributes  a3 * (-2 sqrt2) * sqrt(tau) * sin w   ... let's pin coefficients numerically.
"""
import mpmath as mp

KSTART = 1

def Aq(k, q):  return 2 * q / (1 - q ** (k + 1))
def Cq(k, q):  return 2 * q ** (k + 3) / (1 - q ** (k + 2)) - 2 * q ** (k + 2) / (1 - q ** (k + 1))

def travel_terms(q, J):
    """return list t^T_j for j=0..J-1 (positive magnitudes)."""
    ts = []
    prod = mp.mpf(1)
    for j in range(J):
        kk = KSTART + 2 * j
        ts.append(Aq(kk, q) * prod)            # A_{1+2j} prod_{i<j} |C|  (prod already has the |C| product)
        prod *= -Cq(kk, q)                      # C<0 so -C>0 = |C|
    return ts

def hat_t(j, tau):
    return (2 / tau) ** (j + 1) / mp.factorial(2 * j + 2)

if __name__ == "__main__":
    mp.mp.dps = 80
    for tau in [mp.mpf('0.02'), mp.mpf('0.005'), mp.mpf('0.001'), mp.mpf('0.0003')]:
        q = mp.e ** (-tau)
        w = mp.sqrt(2 / tau)
        J = int(3 * w) + 20
        ts = travel_terms(q, J)
        print(f"\n=== tau={mp.nstr(tau,4)}  w={mp.nstr(w,6)}  J={J} ===")
        print(f"{'j':>4} {'log rho_j':>16} {'/(  (j+1)tau )':>16} {'/( tau^2 j^3 )':>18}")
        for j in [1, 2, 4, int(w/4), int(w/2), int(3*w/4), int(w)]:
            if j >= J: continue
            rho = ts[j] / hat_t(j, tau)
            lr = mp.log(rho)
            lin = lr / ((j + 1) * tau)
            cub = lr / (tau**2 * j**3) if j > 0 else mp.mpf('nan')
            print(f"{j:>4} {mp.nstr(lr,8):>16} {mp.nstr(lin,8):>16} {mp.nstr(cub,8):>18}")
