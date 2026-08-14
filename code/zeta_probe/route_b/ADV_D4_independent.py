"""
ADVERSARIAL independent verification of D4 pole-phase claims.
Written from scratch. Does NOT import or reuse the D4_*.py code.

Claims under test:
  (C0) Travel poles: Sig_t(q_m)=1  with Sig_t = sum_j Aq(1+2j) prod_{i<j} Cq(1+2i).
  (C1) c_T := lim cos(w_m)/(sqrt(tau) sin(w_m)) = sqrt2/36 = 0.0392837100...
  (C2) cos(W_m)/(sqrt(tau) sin w_m) -> 1/sqrt2 + c_T = 0.7463905...
  (C3) cos(W_m/q)/(sqrt(tau) sin w_m) -> c_T - 1/sqrt2 = -17 sqrt2/36 = -0.6678231...
  (C4) sin w_m, sin W_m, sin(W_m/q) -> (-1)^{m-1}, |.|->1.
  (C5) eps_m := w_m - (m-1/2)pi = -c_T sqrt(tau) + O(tau).
  (C6) Direct Richardson on (Sig_t - (1-cos w))/(sqrt tau sin w) at sin w = 1 phases -> c_T.
       Bulk S_1 by analogous machinery -> -17 sqrt2/36.

Conventions (as stated): tau=-ln q, w=sqrt(2/tau), W=w*exp(-tau/2), W/q=w*exp(+tau/2).
"""
import mpmath as mp

# ---------- travel block (independent transcription of fact 10) ----------
def Aq(k, q):
    return 2*q/(1 - q**(k+1))

def Cq(k, q):
    return 2*q**(k+3)/(1 - q**(k+2)) - 2*q**(k+2)/(1 - q**(k+1))

def sig_t(q):
    """Sig_t(q) = sum_{j>=0} Aq(1+2j) * prod_{i<j} Cq(1+2i)."""
    tot = mp.mpf(0)
    prod = mp.mpf(1)
    tiny = mp.mpf(10)**(-(mp.mp.dps + 15))
    j = 0
    while True:
        kk = 1 + 2*j
        tot += Aq(kk, q)*prod
        prod *= Cq(kk, q)
        if abs(prod) < tiny and j > 80:
            break
        j += 1
        if j > 5_000_000:
            raise RuntimeError("sig_t did not converge")
    return tot

def repolish(seed):
    return mp.findroot(lambda Q: sig_t(Q) - 1, mp.mpf(seed))

# ---------- bulk S_1 (fact: alpha,gamma transcription) ----------
def alpha(k, q):
    return 2/(q**(-(k+1)) - 1)

def gamma(k, q):
    return alpha(k+1, q) - alpha(k, q)

def S1_bulk(q):
    tot = mp.mpf(0)
    prod = mp.mpf(1)
    tiny = mp.mpf(10)**(-(mp.mp.dps + 15))
    j = 0
    while True:
        kk = 1 + 2*j
        tot += alpha(kk, q)*prod
        prod *= gamma(kk, q)
        if abs(prod) < tiny and j > 80:
            break
        j += 1
        if j > 5_000_000:
            raise RuntimeError("S1_bulk did not converge")
    return tot


if __name__ == "__main__":
    seeds = [l.strip() for l in open("poles.txt") if l.strip()]
    cT = mp.sqrt(2)/36

    test = [2, 4, 8, 16, 30, 50, 79]
    # set precision off the deepest pole
    qmax = mp.mpf(seeds[max(test)])
    taumin = -mp.log(qmax)
    mp.mp.dps = 40 + int(2.5*mp.sqrt(2/taumin))
    print(f"# dps={mp.mp.dps}, taumin={mp.nstr(taumin,4)}")
    print(f"# c_T target sqrt2/36 = {mp.nstr(cT,14)}")
    print(f"# C2 target 1/sqrt2+c_T = {mp.nstr(1/mp.sqrt(2)+cT,12)}")
    print(f"# C3 target c_T-1/sqrt2 = -17sqrt2/36 = {mp.nstr(cT-1/mp.sqrt(2),12)}  (={mp.nstr(-17*mp.sqrt(2)/36,12)})")
    print()
    hdr = (f"{'m':>3} {'tau':>11} {'resid':>9} {'cosw/stsw':>13} {'cosW/stsw':>13} "
           f"{'cosWq/stsw':>13} {'sgn*sinw':>10} {'epscheck':>11}")
    print(hdr)
    for i in test:
        q = repolish(seeds[i])
        tau = -mp.log(q)
        w = mp.sqrt(2/tau)
        W = w*mp.e**(-tau/2)
        Wq = w*mp.e**(tau/2)   # = W/q independently constructed
        # cross-check W/q == Wq
        assert abs(W/q - Wq) < mp.mpf(10)**(-(mp.mp.dps-5)), "W/q mismatch"
        st = mp.sqrt(tau)
        sw = mp.sin(w); cw = mp.cos(w)
        cW = mp.cos(W); cWq = mp.cos(Wq)
        resid = sig_t(q) - 1
        c1 = cw/(st*sw)
        c2 = cW/(st*sw)
        c3 = cWq/(st*sw)
        # eps relative to nearest (m-1/2)pi
        kk = mp.nint(w/mp.pi - mp.mpf('0.5'))
        eps = w - (kk + mp.mpf('0.5'))*mp.pi
        eps_check = (eps + cT*st)/st     # -> 0
        sign = mp.sign(sw)
        print(f"{i:>3} {mp.nstr(tau,5):>11} {mp.nstr(resid,2):>9} "
              f"{mp.nstr(c1,9):>13} {mp.nstr(c2,9):>13} {mp.nstr(c3,9):>13} "
              f"{mp.nstr(sign*abs(sw),7):>10} {mp.nstr(eps_check,5):>11}")
