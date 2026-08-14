import mpmath as mp
mp.mp.dps=120
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def Se_So(q):
    onem=1-q;Se=mp.mpf(0);So=mp.mpf(0)
    for j in range(0,2000):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te;So+=to
        if j>10 and abs(te)+abs(to)<mp.mpf(10)**(-250):break
    return Se,So
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
# R1 reduces to: (So-Se)/Se -> 0.  Se~1/w, So-Se=O(tau) => (So-Se)/Se ~ tau*w = sqrt(2 tau)->0.
# Verify (So-Se)/(tau) bounded and (So-Se)/Se ~ sqrt(2 tau):
print("R1 tail: (So-Se) decomposition. Claim (So-Se)/Se -> 0 like sqrt(tau).")
print(f"{'m':>3} {'tau':>10} {'(So-Se)/tau':>13} {'(So-Se)/Se':>13} {'/sqrt(2tau)':>12}")
for m in [4,8,16,32,48,64,80]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    Se,So=Se_So(q)
    d=So-Se
    print(f"{m:>3} {float(tau):>10.6f} {float(d/tau):>13.7f} {float(d/Se):>13.7f} {float((d/Se)/mp.sqrt(2*tau)):>12.7f}")
