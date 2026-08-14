"""
D4: Make the POLE PHASE rigorous.

The travel poles q_m satisfy Sig_t(q_m)=1.  We:
  (i)   re-polish each pole via mp.findroot(lambda Q: Sig_t(Q)-1, seed) from poles.txt
  (ii)  build the lem:cos structure Sig_t = (1-cos w) + c_T sqrt(tau) sin w + ... = 1
        => cos(w_m) = c_T sqrt(tau) sin(w_m) + O(tau^{3/2}),  c_T numerically sqrt2/36.
  (iii) determine sin(w_m), cos(w_m), sin(W_m/q), cos(W_m/q) to O(tau).

Conventions: tau=-ln q, w=sqrt(2/tau), W=w*exp(-tau/2).
"""
import sys
import mpmath as mp

# ---- travel block (fact 10) ----
KSTART = 1

def Aq(k, q):
    return 2 * q / (1 - q ** (k + 1))

def Cq(k, q):
    return 2 * q ** (k + 3) / (1 - q ** (k + 2)) - 2 * q ** (k + 2) / (1 - q ** (k + 1))

def sig_t(q, J=2000000):
    tot = mp.mpf(0); prod = mp.mpf(1)
    tiny = mp.mpf(10) ** (-(mp.mp.dps + 12))
    for j in range(J):
        kk = KSTART + 2 * j
        tot += Aq(kk, q) * prod
        prod *= Cq(kk, q)
        if abs(prod) < tiny and j > 60:
            break
    return tot

def repolish(seed):
    return mp.findroot(lambda Q: sig_t(Q) - 1, seed)

def load_seeds(path):
    seeds = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                seeds.append(line)
    return seeds

if __name__ == "__main__":
    path = "poles.txt"
    seeds = load_seeds(path)
    # choose which poles to test: small tau => high m.  Use a spread.
    # Set precision from the deepest pole we will touch.
    test_idx = [int(x) for x in (sys.argv[1].split(",") if len(sys.argv) > 1 else
                                 ["2","4","8","16","24","40","60","79"])]
    test_idx = [i for i in test_idx if 0 <= i < len(seeds)]
    # precision: dps = 40 + 2.5*sqrt(2/tau); tau smallest at largest m
    maxm = max(test_idx)
    qmax = mp.mpf(seeds[maxm])
    taumin = -mp.log(qmax)
    mp.mp.dps = 40 + int(2.5 * mp.sqrt(2 / taumin))
    print(f"# dps={mp.mp.dps}, taumin={mp.nstr(taumin,4)}")

    print(f"{'m':>3} {'tau':>12} {'cos(w)':>16} {'cosw/(sqrt(tau)sinw)':>22} {'resid Sig_t-1':>14}")
    cTs = []
    for i in test_idx:
        q = repolish(seeds[i])
        tau = -mp.log(q)
        w = mp.sqrt(2 / tau)
        W = w * mp.e ** (-tau / 2)
        cw = mp.cos(w); sw = mp.sin(w)
        ratio = cw / (mp.sqrt(tau) * sw)   # should -> c_T = sqrt2/36
        resid = sig_t(q) - 1
        cTs.append((tau, ratio))
        print(f"{i:>3} {mp.nstr(tau,6):>12} {mp.nstr(cw,8):>16} {mp.nstr(ratio,10):>22} {mp.nstr(resid,3):>14}")

    print("\n# target c_T = sqrt2/36 =", mp.nstr(mp.sqrt(2)/36, 10))
