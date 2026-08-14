"""
PHASE 2: complex saddle of the EXPLICIT dilog L(k)=log d_k, careful steepest descent, check Y3 = 2 Re[SP].
This should fix the scope failure (the explicit dilog form gives unambiguous branches for Li2, log(1-z)).
L(k) = i pi k + k log(2(1-q)q^3) + k^2 log q - log(q^2;q^2)_k - log(q^5;q^2)_k   (dilog form, phase1b-verified to O(sqrt tau))
L'(k) = i pi + log(2(1-q)q^3) - 2k tau - log(1-z2) - log(1-z5) + tau z2/(1-z2) + tau z5/(1-z5)   (z2=q^{2k+2}, z5=q^{2k+5})
L''(k) = -2 tau + 2 tau z2/(1-z2) + 2 tau z5/(1-z5) + O(tau^2)
n=0 Poisson term = int e^{L(x)} dx ~ e^{L(k*)} sqrt(2 pi/(-L''(k*))); Y3 = 2 Re[that] (n=1 = conjugate).
"""
import mpmath as mp
mp.mp.dps = 40; I = mp.mpc(0,1)

def qpoch_k(a,q2,k):
    p=mp.mpf(1) if not isinstance(a,mp.mpc) else mp.mpc(1); aj=a
    for _ in range(k): p*=(1-aj); aj*=q2
    return p
def qpoch_inf(a,q2):
    p=mp.mpf(1) if not isinstance(a,mp.mpc) else mp.mpc(1); aj=a
    terms=int((mp.mp.dps+10)*2.3026/abs(mp.log(abs(q2))))+40
    for _ in range(terms):
        p*=(1-aj); aj*=q2
        if abs(aj)<mp.mpf(10)**(-(mp.mp.dps+8)): break
    return p
def Y3_sum(q):
    q2=q*q;P2i=qpoch_inf(q2,q2);P5i=qpoch_inf(q**5,q2)
    S=mp.mpf(0);k=0
    while True:
        dk=((-2)**k)*((1-q)**k)*q**(k*k+3*k)/(qpoch_k(q2,q2,k)*qpoch_k(q**5,q2,k))
        S+=dk
        if k>10 and abs(dk)<mp.mpf(10)**(-(mp.mp.dps+6)):break
        k+=1
    return S
def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(220/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=14):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def make_L(q,tau):
    q2=q*q
    q_q=qpoch_inf(q,q);q2q2=qpoch_inf(q2,q2)
    log_q5_inf=mp.log(q_q)-mp.log(q2q2)-mp.log(1-q)-mp.log(1-q**3)
    c2=-mp.pi**2/(12*tau)+mp.mpf('0.5')*mp.log(mp.pi/tau)+tau/12   # = log(q^2;q^2)_inf
    def L(k):
        z2=q**(2*k+2);z5=q**(2*k+5)
        log2=(1/(2*tau))*(mp.polylog(2,z2)-mp.pi**2/6)+mp.mpf('0.5')*mp.log(mp.pi/(tau*(1-z2)))+(tau/12)*(1+z2)/(1-z2)
        tail=-(1/(2*tau))*mp.polylog(2,z5)+mp.mpf('0.5')*mp.log(1-z5)+(tau/12)*(1+z5)/(1-z5)
        log5=log_q5_inf-tail
        return I*mp.pi*k+k*mp.log(2*(1-q)*q**3)+k*k*mp.log(q)-log2-log5
    def Lp(k):
        z2=q**(2*k+2);z5=q**(2*k+5)
        return (I*mp.pi+mp.log(2*(1-q)*q**3)-2*k*tau-mp.log(1-z2)-mp.log(1-z5)
                +tau*z2/(1-z2)+tau*z5/(1-z5))
    def Lpp(k):
        z2=q**(2*k+2);z5=q**(2*k+5)
        return -2*tau+2*tau*z2/(1-z2)+2*tau*z5/(1-z5)
    return L,Lp,Lpp

def find_saddle(q,tau,w,Lp,Lpp):
    # closed-form leading guess: (1-z)^2 = -2 tau z => 1-z = tau - i sqrt(2 tau - tau^2); z=q^{2k+2} => k
    wz=tau - I*mp.sqrt(2*tau - tau*tau); zc=1-wz
    k0=-mp.log(zc)/(2*tau) - 1
    # coarse |Lp| min on a small box around k0 to be safe
    best=k0; bv=abs(Lp(k0))
    for dr in [mp.mpf(j)/4 for j in range(-6,7)]:
        for di in [mp.mpf(j)/4 for j in range(-6,7)]:
            kk=k0+mp.mpc(float(dr),float(di))
            try:
                v=abs(Lp(kk))
                if v<bv: bv=v; best=kk
            except: pass
    ks=best
    for _ in range(120):                       # damped Newton
        d=Lp(ks)/Lpp(ks)
        if abs(d)>mp.mpf('0.4'): d=d*mp.mpf('0.4')/abs(d)
        ks=ks-d
        if abs(d)<mp.mpf(10)**(-26): break
    return ks

print("PHASE 2: complex saddle of dilog L, check Y3 = 2 Re[SP].  (resolves the scope 2Re mismatch?)")
print(f"{'m':>2}{'tau':>9}{'saddle k*':>26}{'|Lp(k*)|':>9}{'Y3 actual':>15}{'2Re[SP]':>15}{'ratio':>8}")
for m in [2,4,6,8]:
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau)
    Y3=Y3_sum(q)
    L,Lp,Lpp=make_L(q,tau)
    ks=find_saddle(q,tau,w,Lp,Lpp)
    L2=Lpp(ks)
    SP=mp.e**(L(ks))*mp.sqrt(2*mp.pi/(-L2))
    twoRe=2*mp.re(SP)
    print(f"{m:>2}{float(tau):>9.5f}{'  '+mp.nstr(ks,7):>26}{float(abs(Lp(ks))):>9.0e}{mp.nstr(Y3,7):>15}{mp.nstr(twoRe,7):>15}{float(twoRe/Y3):>8.4f}")
