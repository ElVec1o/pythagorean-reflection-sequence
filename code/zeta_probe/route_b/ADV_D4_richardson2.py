"""
ADVERSARIAL follow-up: the error in (Sig_t-(1-cos w))/sqrt(tau) decays as O(tau),
NOT O(sqrt tau) (error ratio 0.25 = tau ratio, not 0.5 = sqrt-tau ratio).
Redo Richardson assuming  val(tau) = cT + a*tau + b*tau^2 + ...  (powers of tau).
This should nail cT = sqrt2/36 to many digits.
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

if __name__=="__main__":
    cT = mp.sqrt(2)/36
    Ns=[40,80,160,320,640,1280]
    vals=[]; taus=[]
    for N in Ns:
        w=(2*N+mp.mpf('0.5'))*mp.pi; tau=2/w**2
        mp.mp.dps = 50 + int(float(w)/mp.log(10))+30
        w=(2*N+mp.mpf('0.5'))*mp.pi; tau=2/w**2; q=mp.e**(-tau)
        s1=sig_t(q); E=s1-(1-mp.cos(w)); val=E/mp.sqrt(tau)
        vals.append(val); taus.append(tau)
    # promote all to common high precision for the extrapolation arithmetic
    mp.mp.dps = 60
    vals=[mp.mpf(mp.nstr(v,50)) for v in vals]
    taus=[mp.mpf(mp.nstr(t,50)) for t in taus]
    print("Richardson assuming val = cT + a*tau + b*tau^2 + ... (powers of tau):")
    cur=vals[:]; tt=taus[:]; level=0
    while len(cur)>=2:
        nxt=[]
        for i in range(1,len(cur)):
            r = tt[i]/tt[i-1]   # tau shrink factor (~1/4)
            nxt.append((cur[i]-r*cur[i-1])/(1-r))   # eliminate leading a*tau^level
        level+=1; cur=nxt; tt=tt[1:]
        print(f"  level {level}: last={mp.nstr(cur[-1],22)}  err={mp.nstr(cur[-1]-cT,5)}")
        if len(cur)<2: break
    print(f"\n  cT = sqrt2/36 = {mp.nstr(cT,22)}")
