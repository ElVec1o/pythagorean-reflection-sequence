"""
D4 step 5: At the pole q_m (Sigma_1=1), determine to O(tau):
   cos(w_m), sin(w_m), and the W/q-phase values cos(W_m/q_m), sin(W_m/q_m).
W = w e^{-tau/2}.  Pole condition => cos w_m = c_T sqrt(tau) sin w_m + O(tau^{3/2}),  c_T=sqrt2/36.

Since |cos w_m| = O(sqrt tau) -> 0, w_m -> (m - 1/2)pi (a zero of cos), and sin w_m -> +/-1.
We have, with eps_m := w_m - (m-1/2)pi (small):
   cos w_m = cos((m-1/2)pi + eps) = -sin((m-1/2)pi) sin eps ~ -(-1)^{m-1} eps_m  (since sin((m-1/2)pi)=(-1)^{m-1})
   wait sign: sin((m-1/2)pi) = sin(m pi - pi/2) = -cos(m pi) = -(-1)^m = (-1)^{m-1}.
   cos w_m = -(-1)^{m-1} eps + O(eps^3),  sin w_m = (-1)^{m-1}(1 - eps^2/2).
Pole condition cos w_m = c_T sqrt tau sin w_m =>  -(-1)^{m-1}eps = c_T sqrt tau (-1)^{m-1} =>
   eps_m = -c_T sqrt tau + O(tau).    (so w_m = (m-1/2)pi - c_T sqrt tau + O(tau))
Thus:
   sin w_m = (-1)^{m-1}(1 + O(tau)),
   cos w_m = c_T sqrt(tau) (-1)^{m-1} + O(tau^{3/2}) = c_T sqrt tau sin w_m + O(tau^{3/2}).

Now W = w e^{-tau/2} = w(1 - tau/2 + tau^2/8 - ...).  W - w = -w tau/2 + w tau^2/8 = -(1/sqrt2)sqrt tau + O(tau^{3/2})
   (since w tau/2 = (1/2)sqrt(2/tau)*tau = (1/2)sqrt(2 tau)=sqrt(tau/2)=(1/sqrt2)sqrt tau).
   cos W = cos(w + (W-w)) = cos w cos(W-w) - sin w sin(W-w)
         = [c_T sqrt tau sin w] [1+O(tau)] - sin w [-(1/sqrt2)sqrt tau + O(tau^{3/2})]
         = sin w * sqrt tau (c_T + 1/sqrt2) + O(tau^{3/2})
   So cos W_m = (c_T + 1/sqrt2) sqrt tau sin w_m + O(tau^{3/2}).   [matches fact 5: cos W ~ sqrt(tau/2) sin w, since
        c_T+1/sqrt2 = sqrt2/36 + 1/sqrt2 ~ 0.7464; but fact5 says sqrt(tau/2)=0.7071 sqrt tau... let me CHECK numerically]
   sin W_m = sin(w+(W-w)) = sin w cos(W-w)+cos w sin(W-w) = sin w (1+O(tau)) = (-1)^{m-1}+O(tau).

For W/q = W e^{tau} = w e^{tau/2} = w(1+tau/2+...).  W/q - w = w tau/2 + ... = +(1/sqrt2)sqrt tau + O(tau^{3/2}).
   cos(W/q) = cos w cos((1/sqrt2)sqrt tau) - sin w sin((1/sqrt2)sqrt tau)
            = c_T sqrt tau sin w - sin w (1/sqrt2)sqrt tau + O(tau^{3/2})
            = sin w sqrt tau (c_T - 1/sqrt2) + O(tau^{3/2}).
   sin(W/q) = sin w (1+O(tau)) = (-1)^{m-1} + O(tau).

We VERIFY all of these against re-polished poles.
"""
import mpmath as mp

KSTART = 1
def Aq(k, q):  return 2 * q / (1 - q ** (k + 1))
def Cq(k, q):  return 2 * q ** (k + 3) / (1 - q ** (k + 2)) - 2 * q ** (k + 2) / (1 - q ** (k + 1))

def sig_t(q):
    tot = mp.mpf(0); prod = mp.mpf(1)
    tiny = mp.mpf(10) ** (-(mp.mp.dps + 12)); j = 0
    while True:
        kk = KSTART + 2*j
        tot += Aq(kk,q)*prod; prod *= Cq(kk,q)
        if abs(prod) < tiny and j > 60: break
        j += 1
    return tot

def repolish(seed): return mp.findroot(lambda Q: sig_t(Q)-1, seed)

if __name__ == "__main__":
    seeds = [l.strip() for l in open("poles.txt") if l.strip()]
    cT = mp.sqrt(2)/36
    test = [4, 8, 16, 30, 50, 79]
    # set dps from deepest
    qmax = mp.mpf(seeds[max(test)]); taumin = -mp.log(qmax)
    mp.mp.dps = 40 + int(2.5*mp.sqrt(2/taumin))
    print(f"# dps={mp.mp.dps},  c_T = sqrt2/36 = {mp.nstr(cT,10)}\n")

    hdr = f"{'m':>3} {'tau':>11} {'cosw/(st*sw)':>14} {'cosW/(st*sw)':>14} {'cosWq/(st*sw)':>15} {'|sinw|':>9} {'|sinWq|':>9}"
    print(hdr)
    print("# predictions: cosw/(st sw)->c_T=0.039284 ; cosW/(st sw)->c_T+1/sqrt2=%s ; cosWq/(st sw)->c_T-1/sqrt2=%s"
          % (mp.nstr(cT+1/mp.sqrt(2),8), mp.nstr(cT-1/mp.sqrt(2),8)))
    print("#               |sinw|->1 ; |sin(W/q)|->1")
    for i in test:
        q = repolish(seeds[i]); tau = -mp.log(q)
        w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2); Wq = W/q
        st = mp.sqrt(tau)
        sw = mp.sin(w); cw = mp.cos(w)
        cW = mp.cos(W); cWq = mp.cos(Wq); sWq = mp.sin(Wq)
        print(f"{i:>3} {mp.nstr(tau,5):>11} {mp.nstr(cw/(st*sw),9):>14} {mp.nstr(cW/(st*sw),9):>14} {mp.nstr(cWq/(st*sw),9):>15} {mp.nstr(abs(sw),6):>9} {mp.nstr(abs(sWq),6):>9}")

    print("\n# CHECK fact5 claim cos W ~ sqrt(tau/2) sin w:  sqrt(1/2)=%s ; our c_T+1/sqrt2=%s"
          % (mp.nstr(1/mp.sqrt(2),8), mp.nstr(cT+1/mp.sqrt(2),8)))
    print("# (If cosW/(st sw) -> 0.7464 not 0.7071, fact5's 'sqrt(tau/2)' is the LEADING T1 piece only; c_T adds sqrt2/36.)")
