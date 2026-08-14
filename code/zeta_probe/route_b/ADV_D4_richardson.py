"""
ADVERSARIAL: confirm the LIMIT is EXACTLY sqrt2/36 (and C2,C3 exact) via Richardson
extrapolation assuming an O(sqrt tau) error, AND verify the error really is O(sqrt tau)
(ratio of successive errors ~ ratio of sqrt(tau)).

Use the controlled "sin w = 1" phase family tau = 2/w^2 with w=(2N+1/2)pi (NOT the poles)
to get a clean tau-sequence, exactly as claim (C6) does. This isolates c_T from the pole
machinery and lets Richardson work on a geometric tau-ladder.

Also: the SAME machinery on the bulk S_1 must give -17 sqrt2/36.
"""
import mpmath as mp

def Aq(k, q): return 2*q/(1 - q**(k+1))
def Cq(k, q): return 2*q**(k+3)/(1 - q**(k+2)) - 2*q**(k+2)/(1 - q**(k+1))
def sig_t(q):
    tot = mp.mpf(0); prod = mp.mpf(1)
    tiny = mp.mpf(10)**(-(mp.mp.dps+15)); j=0
    while True:
        kk=1+2*j; tot += Aq(kk,q)*prod; prod *= Cq(kk,q)
        if abs(prod)<tiny and j>80: break
        j+=1
    return tot
def alpha(k,q): return 2/(q**(-(k+1))-1)
def gam(k,q): return alpha(k+1,q)-alpha(k,q)
def S1_bulk(q):
    tot=mp.mpf(0); prod=mp.mpf(1)
    tiny=mp.mpf(10)**(-(mp.mp.dps+15)); j=0
    while True:
        kk=1+2*j; tot+=alpha(kk,q)*prod; prod*=gam(kk,q)
        if abs(prod)<tiny and j>80: break
        j+=1
    return tot

if __name__=="__main__":
    cT = mp.sqrt(2)/36
    c1bulk = -17*mp.sqrt(2)/36

    print("=== Travel: (Sig_t-(1-cos w))/sqrt(tau) at sin w=1, w=(2N+1/2)pi ===")
    Ns = [40,80,160,320,640,1280]
    vals=[]; sts=[]
    for N in Ns:
        w=(2*N+mp.mpf('0.5'))*mp.pi
        tau=2/w**2
        mp.mp.dps = 50 + int(float(w)/mp.log(10) ) + 30   # enough to resolve cancellations
        # recompute w,tau at this precision
        w=(2*N+mp.mpf('0.5'))*mp.pi; tau=2/w**2; q=mp.e**(-tau)
        s1=sig_t(q)
        E=s1-(1-mp.cos(w))
        val=E/mp.sqrt(tau)           # sin w = 1
        vals.append(val); sts.append(mp.sqrt(tau))
        err = val-cT
        print(f"  N={N:5d} dps={mp.mp.dps} tau={mp.nstr(tau,5)} val={mp.nstr(val,14)} err={mp.nstr(err,4)}")
    # successive error ratios (should -> ratio of sqrt(tau) = sqrt( (2N+.5)^2 / (2N'+.5)^2 ) ~ N/N')
    print("  error ratios (consecutive):")
    for i in range(1,len(vals)):
        er0=vals[i-1]-cT; er1=vals[i]-cT
        rt = sts[i]/sts[i-1]
        print(f"    {mp.nstr(er1/er0,6)}   sqrt(tau) ratio={mp.nstr(rt,6)}")
    # Richardson eliminating linear-in-sqrt(tau)
    print("  Richardson (assume val = cT + a*sqrt tau + ...):")
    cur = vals[:]
    st = sts[:]
    level=0
    while len(cur)>=2:
        nxt=[]
        for i in range(1,len(cur)):
            r = st[i]/st[i-1]   # sqrt(tau) shrink factor
            # val_i = cT + a*st_i ; eliminate a:  (val_i - r*val_{i-1})/(1-r)
            nxt.append((cur[i]-r*cur[i-1])/(1-r))
        level+=1
        cur=nxt
        st=st[1:]
        print(f"    level {level}: last={mp.nstr(cur[-1],16)}  (cT={mp.nstr(cT,16)})")
        if len(cur)<2: break

    print("\n=== Bulk S_1: (S1-(1-cos w))/sqrt(tau) -> -17 sqrt2/36 ? ===")
    for N in [80,160,320]:
        w=(2*N+mp.mpf('0.5'))*mp.pi; tau=2/w**2
        mp.mp.dps=50+int(float(w)/mp.log(10))+30
        w=(2*N+mp.mpf('0.5'))*mp.pi; tau=2/w**2; q=mp.e**(-tau)
        s1=S1_bulk(q); E=s1-(1-mp.cos(w)); val=E/mp.sqrt(tau)
        print(f"  N={N} val={mp.nstr(val,14)} target={mp.nstr(c1bulk,14)} err={mp.nstr(val-c1bulk,4)}")
