import mpmath as mp
mp.mp.dps=40
def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(220/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=16):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print("3b' phase check: Theta(n*)=sum_j arccos(b_j/2) [smooth, NO oscillation] vs its integral+EM form.")
print(f"{'m':>2}{'tau':>9}{'n*':>6}{'Theta_sum':>13}{'Theta_int':>13}{'sum-int':>11}{'Theta/pi frac':>14}")
for m in [6,8,10,12,16]:
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau)
    def kf(j):
        bn=(1+q**3-2*(1-q)*q**(2*j+2))/q**mp.mpf('1.5')
        return mp.acos(bn/2) if abs(bn)<2 else mp.mpf(0)
    # find n*
    nstar=1
    while True:
        bn=(1+q**3-2*(1-q)*q**(2*nstar+2))/q**mp.mpf('1.5')
        if abs(bn)>=2: break
        nstar+=1
    Th_sum=mp.fsum(kf(j) for j in range(1,nstar))
    # integral form: int_{1/2}^{nstar-1/2} arccos(b(j)/2) dj  (EM midpoint)
    Th_int=mp.quad(kf,[mp.mpf('0.5'),nstar-mp.mpf('0.5')])
    frac=(Th_sum/mp.pi)-mp.floor(Th_sum/mp.pi)
    print(f"{m:>2}{float(tau):>9.5f}{nstar:>6}{float(Th_sum):>13.6f}{float(Th_int):>13.6f}{float(Th_sum-Th_int):>11.2e}{float(frac):>14.6f}")
print("\nIf sum-int is tiny (EM midpoint => O(k'/24) per pt, smooth) => Theta computable to high precision by")
print("a smooth integral (a dilog) -- NO oscillatory cancellation. That's the crux 3b' being tractable.")
print("frac->3/4 confirms the recessive Airy condition; deviation 3/4-frac ~ c sqrt(tau) is the suppression.")
