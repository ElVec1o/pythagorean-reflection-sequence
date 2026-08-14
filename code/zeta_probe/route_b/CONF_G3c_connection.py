"""
3c' + 3d': pin the Airy connection formula P12 = F(amplitude, delta, W) and tie delta to the pole index.
Quantities per pole:
  P12 (full cocycle, true value)
  W=w e^{-tau/2}; turning point n* (b_{n*}=2), at Bessel x=3/(2W)
  Theta(n*)=sum_{j<n*} arccos(b_j/2); N=floor(Theta/pi); delta=(N+3/4)pi - Theta(n*)  [signed dev from recessive]
  A = WKB invariant R_n sqrt(sin k_n) (amplitude, ~const in n)
  BY0 = -sqrt(2/pi) W^{-3/2}   (Y_{3/2} dominant-mode limit B^Y(x->0))
Test forms:  P12 / (A*delta*BY0)  and its tau-power; check N=m-1; identify delta/(pi sqrt(tau)).
"""
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

def analyze(m):
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
    Nconv=int((mp.mp.dps+15)*2.3026/tau)+200
    # WKB invariant A at reference n=5
    def bn_(n): return (1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
    a,b=mp.mpf(1),mp.mpf(0); qn=mp.mpf(1); z=[mp.mpf(0)]
    Theta=mp.mpf(0); nstar=None; Aref=None
    for n in range(1,Nconv+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        a,b=a*(1+2*q2n)-2*b*qn, 2*a*q3n+b*(1-2*q2n)
        z.append(q**(-mp.mpf(3)*n/2)*b)
        bn=bn_(n)
        if abs(bn)<2:
            kn=mp.acos(bn/2); Theta+=kn
            if n==6:
                kp=mp.acos(bn_(5)/2)
                R=mp.sqrt((z[6]**2+z[5]**2-2*mp.cos(kp)*z[6]*z[5])/mp.sin(kp)**2)
                Aref=R*mp.sqrt(mp.sin(kn))
        elif nstar is None:
            nstar=n
    P12=b
    N=int(mp.floor(Theta/mp.pi)); delta=(N+mp.mpf(3)/4)*mp.pi-Theta
    BY0=-mp.sqrt(2/mp.pi)*W**(-mp.mpf(3)/2)
    return dict(m=m,tau=tau,W=W,P12=P12,nstar=nstar,Theta=Theta,N=N,delta=delta,A=Aref,BY0=BY0)

print(f"{'m':>2}{'tau':>9}{'N':>4}{'N=m-1?':>7}{'delta/(pi sqrt tau)':>20}{'P12/(A*delta*BY0)':>20}{'/tau^.5':>10}")
rows=[]
for m in [6,8,10,12,14,16,20]:
    d=analyze(m); rows.append(d)
    ratio=d['P12']/(d['A']*d['delta']*d['BY0'])
    print(f"{m:>2}{float(d['tau']):>9.5f}{d['N']:>4}{str(d['N']==m-1):>7}"
          f"{float(d['delta']/(mp.pi*mp.sqrt(d['tau']))):>20.6f}{float(ratio):>20.6f}{float(ratio/mp.sqrt(d['tau'])):>10.4f}")
print("\nIf P12/(A delta BY0) ~ c tau^{1/2} (const c): connection pinned => 3c' target known.")
print("If delta/(pi sqrt tau)=const: 3d' the pole condition gives delta=c' sqrt(tau). Identify c'.")
c=rows[-1]['delta']/(mp.pi*mp.sqrt(rows[-1]['tau']))
print(f"\ndelta/(pi sqrt tau) -> {mp.nstr(c,8)}; candidates: sqrt2/36*pi-ish? 1/sqrt(26)={mp.nstr(1/mp.sqrt(26),6)}, "
      f"identify={mp.identify(c,['sqrt(2)','pi'])}")
