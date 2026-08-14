import mpmath as mp
mp.mp.dps=40
def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(300/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=20):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print("Is the dispersion defect (1/24)Sum k^3 a BULK quantity (turning-point neighborhood negligible)?")
print(f"{'m':>3}{'tau':>9}{'n*':>6}{'full(1/24)Sk^3':>16}{'bulk n<0.7n* frac':>18}{'bulk n<0.9n* frac':>18}")
for m in [8,16,30,60]:
    if m>len(poles): continue
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau)
    ks=[]
    n=1
    while True:
        b=(1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
        if b>=2: break
        ks.append(mp.acos(b/2)); n+=1
    nstar=len(ks)
    full=sum(k**3 for k in ks)
    b70=sum(ks[i]**3 for i in range(int(0.7*nstar)))
    b90=sum(ks[i]**3 for i in range(int(0.9*nstar)))
    print(f"{m:>3}{float(tau):>9.5f}{nstar:>6}{float(full/24):>16.8f}{float(b70/full):>18.6f}{float(b90/full):>18.6f}")
print("\nIf 'bulk frac' -> 1 already at 70-90% of n* (i.e. the last 10-30% near the turning point adds ~nothing),")
print("then Sum k^3 is a BULK quantity: rigorous bulk discrete-WKB (slow variation holds, |Dk/k|=O(tau) there)")
print("gives the defect, and the turning-point neighborhood is negligible for it => self-contained leading.")
# also: where is the slow-variation good? check |Dk/k| in the bulk (n<0.7 n*)
for m in [30]:
    q=refine(poles[m-1]);tau=-mp.log(q)
    ks=[]
    n=1
    while True:
        b=(1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
        if b>=2: break
        ks.append(mp.acos(b/2)); n+=1
    nstar=len(ks)
    adia_bulk=max(abs(ks[i+1]/ks[i]-1) for i in range(int(0.7*nstar)))
    print(f"\nm=30: max|Dk/k| over BULK n<0.7n* = {float(adia_bulk):.5f}  (/tau={float(adia_bulk/tau):.2f}) -- O(tau) in bulk?")
