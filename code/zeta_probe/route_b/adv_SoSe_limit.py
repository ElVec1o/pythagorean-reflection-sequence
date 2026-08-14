import mpmath as mp
mp.mp.dps = 40
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def SoSe(q):
    onem=1-q;Se=mp.mpf(0);So=mp.mpf(0)
    for j in range(0,400):
        Se+=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        So+=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
    return So/Se, So, Se

poles=[mp.mpf(l) for l in open("poles.txt") if l.strip()]

print("=== KEY QUESTION: is So/Se -> 1+tau/2 a POLE phenomenon or true for ALL q->1? ===")
print("--- along travel poles ---")
for m,q in enumerate(poles[:8]):
    tau=-mp.log(q)
    r,So,Se=SoSe(q)
    print(f" m={m} q={float(q):.6f} So/Se={mp.nstr(r,12)} (So/Se-1)/tau={mp.nstr((r-1)/tau,8)}")
print("--- along a NON-pole q->1 sequence (q=1-1/n) ---")
for n in [20,50,100,200,500,1000,3000]:
    q=mp.mpf(1)-mp.mpf(1)/n
    tau=-mp.log(q)
    r,So,Se=SoSe(q)
    print(f" q={float(q):.6f} So/Se={mp.nstr(r,12)} (So/Se-1)/tau={mp.nstr((r-1)/tau,8)}  Se={mp.nstr(Se,6)}")
