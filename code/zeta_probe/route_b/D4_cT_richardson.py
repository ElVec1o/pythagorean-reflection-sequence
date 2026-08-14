"""
D4 step 4b: high-precision Richardson for c_T = sqrt2/36 (travel) and -17sqrt2/36 (bulk).
Cancellation in Sigma_1 ~ e^w near q->1, so dps must exceed w/ln10 + margin.
"""
import mpmath as mp

KSTART = 1
def Aq(k, q):  return 2 * q / (1 - q ** (k + 1))
def Cq(k, q):  return 2 * q ** (k + 3) / (1 - q ** (k + 2)) - 2 * q ** (k + 2) / (1 - q ** (k + 1))
def alpha(k, q): return 2 / (q**(-(k+1)) - 1)
def gamma(k, q): return alpha(k+1, q) - alpha(k, q)

def sigma1_travel(q):
    tot = mp.mpf(0); prod = mp.mpf(1)
    tiny = mp.mpf(10) ** (-(mp.mp.dps + 12))
    j = 0
    while True:
        kk = KSTART + 2 * j
        tot += Aq(kk, q) * prod; prod *= Cq(kk, q)
        if abs(prod) < tiny and j > 60: break
        j += 1
    return tot

def S1_bulk(q):
    tot = mp.mpf(0); prod = mp.mpf(1)
    tiny = mp.mpf(10) ** (-(mp.mp.dps + 12))
    j = 0
    while True:
        kk = 1 + 2 * j
        tot += alpha(kk, q) * prod; prod *= gamma(kk, q)
        if abs(prod) < tiny and j > 60: break
        j += 1
    return tot

def measure(fn, N):
    w = (2*N + mp.mpf('0.5'))*mp.pi          # sin w = 1
    tau = 2/w**2
    q = mp.e**(-tau)
    s1 = fn(q)
    E = s1 - (1 - mp.cos(w))
    return tau, w, E/(mp.sqrt(tau))          # sin w = 1

if __name__ == "__main__":
    cT = mp.sqrt(2)/36
    cB = -17*mp.sqrt(2)/36

    print("=== TRAVEL: (Sigma_1-(1-cos w))/sqrt(tau) at sin w=1, c_T=sqrt2/36 ===")
    Ns = [10, 20, 40, 80]
    data = []
    for N in Ns:
        w = (2*N + mp.mpf('0.5'))*mp.pi
        # dps: cancellation ~ e^w ~ 10^{w/ln10}; need that + 30 margin
        mp.mp.dps = int(float(w)/2.302585) + 50
        tau, w2, val = measure(sigma1_travel, N)
        data.append((tau, val))
        print(f"  N={N:3d} dps={mp.mp.dps} tau={mp.nstr(tau,5)} w={mp.nstr(w2,8)} val={mp.nstr(val,14)} (val-c_T)={mp.nstr(val-cT,5)}")
    # Richardson: val ~ c_T + a*sqrt(tau). sqrt(tau) ratio between consecutive ~ w_N/w_{N+1}.
    print(f"  target sqrt2/36 = {mp.nstr(cT,14)}")
    # do iterated Richardson eliminating sqrt(tau):
    xs = [mp.sqrt(t) for (t,v) in data]; ys = [v for (t,v) in data]
    print("  Richardson tableau (eliminate sqrt(tau) powers):")
    col = ys[:]
    level = 0
    while len(col) > 1:
        newcol = []
        for i in range(len(col)-1):
            r = xs[i]/xs[i+1]
            newcol.append((col[i+1]*r - col[i])/(r-1))
        col = newcol
        # shrink xs to align
        xs = xs[1:]
        level += 1
        print(f"    level {level}: {[mp.nstr(c,12) for c in col]}")

    print("\n=== BULK: (S_1-(1-cos w))/sqrt(tau), c_1=-17sqrt2/36 ===")
    data = []
    for N in Ns:
        w = (2*N + mp.mpf('0.5'))*mp.pi
        mp.mp.dps = int(float(w)/2.302585) + 50
        tau, w2, val = measure(S1_bulk, N)
        data.append((tau, val))
        print(f"  N={N:3d} tau={mp.nstr(tau,5)} val={mp.nstr(val,14)} (val-c_1)={mp.nstr(val-cB,5)}")
    print(f"  target -17sqrt2/36 = {mp.nstr(cB,14)}")
    xs = [mp.sqrt(t) for (t,v) in data]; ys = [v for (t,v) in data]
    col = ys[:]; level=0
    while len(col) > 1:
        newcol=[]
        for i in range(len(col)-1):
            r = xs[i]/xs[i+1]; newcol.append((col[i+1]*r - col[i])/(r-1))
        col=newcol; xs=xs[1:]; level+=1
        print(f"    level {level}: {[mp.nstr(c,12) for c in col]}")
