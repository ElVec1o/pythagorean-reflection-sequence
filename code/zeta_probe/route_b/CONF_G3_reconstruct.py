"""
END-TO-END validation: reconstruct the deeply-suppressed P12 (~tau^{3/2}, a 1e5-fold cancellation) from
PURELY SMOOTH non-oscillatory inputs via the turning-point/Airy connection law:
   P12 = C sqrt(tau) * A * delta * BY0,   C=-0.3583 (universal),
   A    = 2 q^{3/2}/sqrt(sin k_1)         (WKB amplitude from INITIAL data),
   delta= (m-1/4)pi - Theta(n*)           (Theta from the SMOOTH phase integral; N=m-1 from pole index),
   BY0  = -sqrt(2/pi) W^{-3/2}.
If recon/true -> 1, P12 is computed WITHOUT ever forming the oscillatory cancellation.
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
def true_P12(q):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    N=int((mp.mp.dps+15)*2.3026/(-mp.log(q)))+200
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y
C=mp.mpf('-0.3583')
print("END-TO-END: reconstruct P12 from SMOOTH inputs (no cancellation) vs true P12.")
print(f"{'m':>2}{'tau':>9}{'P12 true':>15}{'P12 recon':>15}{'recon/true':>11}")
for m in [6,8,10,12,14,16,20]:
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
    def bn_(n): return (1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
    rhs=(1-q**mp.mpf('1.5'))**2/(2*(1-q)); nstar=mp.log(rhs)/(2*mp.log(q))-1
    kf=lambda j:(mp.acos(bn_(j)/2) if bn_(j)/2<1 else mp.mpf(0))
    Th=mp.quad(kf,[mp.mpf('0.5'), nstar*mp.mpf('0.999999')])
    delta=(m-mp.mpf(1)/4)*mp.pi - Th
    k1=mp.acos(bn_(1)/2); A=2*q**mp.mpf('1.5')/mp.sqrt(mp.sin(k1))
    BY0=-mp.sqrt(2/mp.pi)*W**(-mp.mpf(3)/2)
    P12_recon=mp.re(C*mp.sqrt(tau)*A*delta*BY0)
    P12_true=true_P12(q)
    print(f"{m:>2}{float(tau):>9.5f}{mp.nstr(P12_true,8):>15}{mp.nstr(P12_recon,8):>15}{float(P12_recon/P12_true):>11.5f}")
print("\nrecon/true -> 1 => the deep cancellation (1e5-fold) is BYPASSED: P12 from smooth WKB amp + smooth phase")
print("integral + pole index. Residual %% = higher-order WKB/Airy, absorbed by the 4x gate margin.")
