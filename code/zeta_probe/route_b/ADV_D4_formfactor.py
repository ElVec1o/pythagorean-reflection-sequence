"""
ADVERSARIAL: verify the FORM-FACTOR transcriptions that the symbolic derivation ASSUMED.

(F0) Build the real travel terms  t^T_j = Aq(1+2j) prod_{i<j} Cq(1+2i).
     Sig_t = sum_j t^T_j.  Check sign pattern: are the t^T_j alternating like (-1)^j (2/tau)^{j+1}/(2j+2)!?

(F1) Define hat_t_j = (2/tau)^{j+1}/(2j+2)!.  Check that sum_j (-1)^j hat_t_j = 1 - cos w + (tiny).
     (cos w = sum_{n>=0} (-1)^n w^{2n}/(2n)!; 1-cos w = sum_{n>=1} (-1)^{n-1} w^{2n}/(2n)!.
      With n=j+1, w^2=2/tau:  (-1)^j (2/tau)^{j+1}/(2j+2)! = (-1)^j hat_t_j.  So sum (-1)^j hat_t_j = 1-cos w EXACTLY.)

(F2) rho^T_j := t^T_j / ((-1)^j hat_t_j)  (factor out the alternation+model).
     Check  log(rho_j/rho_{j-1}) = 2y + 2 log(2y/(e^{2y}-1)),  y=j tau   [THE key (D1) identity].

(F3) Check  log rho^T_j  vs the integrated  -(1/9)tau^2 j^3 + (1/450)tau^4 j^5 - ...
     and quantify the Euler-Maclaurin discrepancy (claim: O(sqrt tau) relative, i.e. j^2-correction).
"""
import mpmath as mp

def Aq(k, q): return 2*q/(1 - q**(k+1))
def Cq(k, q): return 2*q**(k+3)/(1 - q**(k+2)) - 2*q**(k+2)/(1 - q**(k+1))

if __name__=="__main__":
    mp.mp.dps = 200
    tau = mp.mpf('0.0008')
    q = mp.e**(-tau)
    w = mp.sqrt(2/tau)
    print(f"tau={mp.nstr(tau,5)} q={mp.nstr(q,8)} w={mp.nstr(w,8)}")

    # build terms
    J = 220
    t = []
    prod = mp.mpf(1)
    for jj in range(J):
        kk = 1 + 2*jj
        t.append(Aq(kk,q)*prod)
        prod *= Cq(kk,q)

    # (F0) sign pattern of t_j
    print("\n(F0) sign(t_j) for j=0..10:", [int(mp.sign(t[jj]).real) for jj in range(11)])
    print("     => is it (-1)^j?  expected +,-,+,-,...")

    # (F1) model sum = 1 - cos w
    def hat(jj): return (2/tau)**(jj+1)/mp.factorial(2*jj+2)
    model_sum = mp.nsum(lambda n: (-1)**int(n)*hat(int(n)), [0, mp.inf])
    print(f"\n(F1) sum_j (-1)^j hat_t_j = {mp.nstr(model_sum,16)}")
    print(f"     1 - cos w             = {mp.nstr(1-mp.cos(w),16)}")
    print(f"     diff = {mp.nstr(model_sum-(1-mp.cos(w)),5)}")

    # (F2) rho_j and the one-step identity
    rho = [ t[jj] / ((-1)**jj * hat(jj)) for jj in range(J) ]
    print("\n(F2) log(rho_j/rho_{j-1}) vs 2y+2log(2y/(e2y-1)), y=j tau:")
    print(f"  {'j':>4} {'y':>10} {'actual':>22} {'predicted':>22} {'diff':>12}")
    for jj in [5,10,20,40,80,120]:
        yv = jj*tau
        actual = mp.log(rho[jj]/rho[jj-1])
        pred = 2*yv + 2*mp.log(2*yv/(mp.e**(2*yv)-1))
        print(f"  {jj:>4} {mp.nstr(yv,5):>10} {mp.nstr(actual,16):>22} {mp.nstr(pred,16):>22} {mp.nstr(actual-pred,4):>12}")

    # (F3) log rho_j vs integrated series; Euler-Maclaurin discrepancy
    print("\n(F3) log rho_j: actual vs -(1/9)tau^2 j^3 + (1/450)tau^4 j^5 - (2/19845)tau^6 j^7")
    print(f"  {'j':>4} {'logrho actual':>20} {'series pred':>20} {'rel.err':>12}")
    for jj in [10,20,30,40,60,80]:
        lr = mp.log(rho[jj])
        ser = -mp.mpf(1)/9*tau**2*jj**3 + mp.mpf(1)/450*tau**4*jj**5 - mp.mpf(2)/19845*tau**6*jj**7
        rel = (lr-ser)/lr if lr!=0 else mp.mpf('nan')
        print(f"  {jj:>4} {mp.nstr(lr,12):>20} {mp.nstr(ser,12):>20} {mp.nstr(rel,5):>12}")

    # Where is the saddle?  j ~ w/sqrt2 (so y=j tau ~ tau w/sqrt2 = sqrt(tau/... )). compute:
    jstar = w/mp.sqrt(2)
    print(f"\n  saddle j* ~ w/sqrt2 = {mp.nstr(jstar,6)}  => y* = j* tau = {mp.nstr(jstar*tau,6)} (small, O(sqrt tau))")
    print(f"  delta_jstar = 1-rho_jstar ~ (1/9)tau^2 j*^3 = {mp.nstr(mp.mpf(1)/9*tau**2*jstar**3,6)}")
