import mpmath as mp
mp.mp.dps=40
def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(220/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=18):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print("Pole deviation w_m - (m+1/2)pi  (is it O(sqrt tau) [sharp lem:cos] or O(tau^{1/4}) [lem:T2abs]?)")
print(f"{'m':>2}{'tau':>9}{'w_m':>11}{'(m+.5)pi':>11}{'dev':>11}{'dev/sqrt(tau)':>14}{'dev/tau^.25':>12}")
for m in [6,8,10,12,16,20,28]:
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau)
    dev=w-(m+mp.mpf('0.5'))*mp.pi
    print(f"{m:>2}{float(tau):>9.5f}{float(w):>11.5f}{float((m+0.5)*mp.pi):>11.5f}{float(dev):>11.6f}"
          f"{float(dev/mp.sqrt(tau)):>14.5f}{float(dev/tau**mp.mpf('0.25')):>12.5f}")
print(f"\nsqrt(2)/36 = {float(mp.sqrt(2)/36):.5f}  (sharp lem:cos pole-phase coeff)")
print("If dev/sqrt(tau) -> const (~-sqrt2/36): pole dev is O(sqrt tau) (TRUTH), and PROVING it = sharp lem:cos.")
print("lem:T2abs only gives O(tau^{1/4}); the gate needs the sharp O(sqrt tau) => U inherits sharp lem:cos for the POLE.")
