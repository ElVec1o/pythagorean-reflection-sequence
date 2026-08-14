"""
BOUND 1 (lem:Bbounded) airtight derivation check.
Exact tau-series:  B_s = sum_{n>=1} phi_n tau^{2n} (P_n(2s) - s),
  phi_n = (-1)^{n+1} zeta(2n)/(n (2pi)^{2n}),   P_n(M)=sum_{m=1}^M m^{2n} (Faulhaber).
Claims to verify vs reference B_gamma (Gamma-form, lemcos_Bstrip):
 (1) the tau-series == B_gamma at complex s (imaginary axis AND diagonal).
 (2) Re B_{iy} = -(1/2) log( y tau / sin(y tau) ) + O(tau * leading)   [closed form, sigma=0].
 (3) strip min at diagonal s=(W/2)(1+i):  Re B -> -(sqrt2/18) sqrt(tau).
 (4) tail sum_{n>=2} is O(tau^{3/2}) (geometric ratio ~ (2|s|tau/2pi)^2), << sqrt(tau) leading.
Scalar mpmath, dps 40, memory-safe.
"""
import mpmath as mp
from lemcos_Bstrip import B_gamma
mp.mp.dps = 40
I = mp.mpc(0,1)

def phi_n(n):
    return (-1)**(n+1) * mp.zeta(2*n) / (n * (2*mp.pi)**(2*n))

def Pn_2s(n, s):
    # P_n(M)=sum_{m=1}^M m^{2n} = (B_{2n+1}(M+1)-B_{2n+1}(1))/(2n+1), M=2s
    M = 2*s
    return (mp.bernpoly(2*n+1, M+1) - mp.bernpoly(2*n+1, 1))/(2*n+1)

def B_tauseries(s, tau, N=40):
    return mp.fsum(phi_n(n)*tau**(2*n)*(Pn_2s(n,s) - s) for n in range(1, N+1))

def tail_n_ge_2(s, tau, N=40):
    return mp.fsum(abs(phi_n(n)*tau**(2*n)*(Pn_2s(n,s) - s)) for n in range(2, N+1))

print("=== (1) tau-series == B_gamma (Gamma-form) at complex s ===")
print(f"{'tau':>8} {'s':>22} {'B_tauseries':>20} {'B_gamma':>20} {'rel.diff':>10}")
for taus in ['0.05','0.02','0.01']:
    tau = mp.mpf(taus); W = mp.sqrt(2/tau)
    for s in [I*(W/2), mp.mpc(W/2, W/2), mp.mpc('0.3', float(W/2))]:
        bt = B_tauseries(s, tau); bg = B_gamma(s, tau)
        rd = abs(bt-bg)/abs(bg) if abs(bg)>0 else abs(bt-bg)
        print(f"{taus:>8} {mp.nstr(s,5):>22} {mp.nstr(bt,9):>20} {mp.nstr(bg,9):>20} {mp.nstr(rd,3):>10}")

print("\n=== (2) Re B_{iy} closed form: -(1/2) log( y tau / sin(y tau) ) ===")
print(f"{'tau':>8} {'y=W/2':>10} {'Re B_iy':>16} {'-1/2 log(yt/sin yt)':>20} {'ratio':>10} {'(both)/(-tau/24)':>16}")
for taus in ['0.05','0.02','0.01','0.005']:
    tau = mp.mpf(taus); W = mp.sqrt(2/tau); y = W/2
    ReB = mp.re(B_tauseries(I*y, tau))
    yt = y*tau
    cf = -mp.mpf(1)/2 * mp.log(yt/mp.sin(yt))
    print(f"{taus:>8} {float(y):>10.4f} {mp.nstr(ReB,8):>16} {mp.nstr(cf,8):>20} {mp.nstr(ReB/cf,7):>10} {mp.nstr(ReB/(-tau/24),6):>16}")

print("\n=== (3) strip min at diagonal (W/2)(1+i): Re B / sqrt(tau) -> -sqrt2/18 ===")
tgt = -mp.sqrt(2)/18
for taus in ['0.05','0.02','0.01','0.005','0.002']:
    tau = mp.mpf(taus); W = mp.sqrt(2/tau); s = mp.mpc(W/2, W/2)
    ReB = mp.re(B_tauseries(s, tau))
    print(f"  tau={taus:>6}: ReB/sqrt(tau)={mp.nstr(ReB/mp.sqrt(tau),8)}  target -sqrt2/18={mp.nstr(tgt,8)}")

print("\n=== (4) tail n>=2 magnitude: O(tau^{3/2}) at the diagonal (vs sqrt(tau) leading) ===")
for taus in ['0.05','0.02','0.01','0.005']:
    tau = mp.mpf(taus); W = mp.sqrt(2/tau); s = mp.mpc(W/2, W/2)
    n1 = abs(phi_n(1)*tau**2*(Pn_2s(1,s)-s))
    tl = tail_n_ge_2(s, tau)
    print(f"  tau={taus:>6}: |n=1 term|={mp.nstr(n1,6)} (~sqrt tau), tail n>=2={mp.nstr(tl,6)}, tail/tau^1.5={mp.nstr(tl/tau**mp.mpf('1.5'),5)}, tail/leading={mp.nstr(tl/n1,4)}")
print("\nIf (1) rel.diff~1e-30, (2) ratio->1, (3) ->-0.0786, (4) tail/tau^1.5 bounded => Bound 1 closed form RIGOROUS.")
