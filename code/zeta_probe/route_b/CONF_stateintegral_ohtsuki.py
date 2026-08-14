"""
Two-saddle version. The real integrand on real xi axis: I(-xi) = conj(I(xi)) because
 D(-xi) = conj(D(xi)) (q-poch with e^{-ixi}=conj(e^{ixi}), real q). And e^{-xi^2/4tau} even.
So INT = 2 Re INT_{0}^{...}, and the steepest descent picks up saddle xi* (Re>0,Im<0) AND its
mirror -conj(xi*) = (-Re, -Im)? Actually the saddle in the LOWER half (Im<0) and its reflection.
The REAL integral = saddle xi* contribution + conjugate-reflected saddle = 2 Re[ saddle(xi*) ].
TEST: does 2 Re[Gauss(xi*)] reproduce INT_true to relative O(tau)?  And +1-loop?
"""
import mpmath as mp

def qpoch_sumlog(a,p,tol=None,NM=4000000):
    if tol is None: tol=mp.mpf(10)**(-(mp.mp.dps+10))
    s=mp.mpc(0); ai=a
    for _ in range(NM):
        s+=mp.log(1-ai); ai*=p
        if abs(ai)<tol: break
    return s
def W(xi,tau):
    q=mp.e**(-tau); e=mp.e**(1j*xi)
    return -xi**2/(4*tau) - qpoch_sumlog(-q**4*e,q**2) - qpoch_sumlog(-2*(1-q)*q*e,q**2)
def saddle(tau):
    eta0=0.5*mp.log(1/tau)
    return mp.findroot(lambda xi: mp.diff(lambda x:W(x,tau),x=xi), mp.pi/2-1j*eta0, tol=mp.mpf(10)**-20)
def Y3_series(x,q,K=8000):
    def qk(a,p,k):
        r=mp.mpf(1); aj=a
        for _ in range(k): r*=(1-aj); aj*=p
        return r
    s=mp.mpf(0)
    for k in range(K):
        dk=(mp.mpf(-2))**k*(1-q)**k*q**(k*k+3*k)/(qk(q**2,q**2,k)*qk(q**5,q**2,k))
        t=dk*x**(2*k+3); s+=t
        if k>10 and abs(t)<mp.mpf(10)**(-(mp.mp.dps+5))*max(abs(s),mp.mpf(1)): break
    return s

for tau in [mp.mpf('0.1'),mp.mpf('0.05'),mp.mpf('0.025'),mp.mpf('0.0125')]:
    mp.mp.dps=45
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    xs=saddle(tau)
    Wpp=mp.diff(lambda x:W(x,tau),xs,2)
    W3=mp.diff(lambda x:W(x,tau),xs,3); W4=mp.diff(lambda x:W(x,tau),xs,4)
    sig2=-1/Wpp
    pref=mp.e**(W(xs,tau))*mp.sqrt(2*mp.pi*sig2)
    corr1=sig2**2*(W4/8)+sig2**3*(5*W3**2/24)
    # two-saddle real combination:
    two0 = 2*mp.re(pref)
    two1 = 2*mp.re(pref*(1+corr1))
    Y3=Y3_series(1/q,q); p52=mp.e**(qpoch_sumlog(q**5,q**2))
    INT_true=(Y3*q**3*mp.sqrt(4*mp.pi*tau)*p52).real
    e0=abs(two0-INT_true)/abs(INT_true); e1=abs(two1-INT_true)/abs(INT_true)
    print(f"tau={float(tau):.4f}: INT_true={mp.nstr(INT_true,10)}  2Re-Gauss relerr={mp.nstr(e0,4)}  +1loop relerr={mp.nstr(e1,4)}  (e0/sqrt(tau)={mp.nstr(e0/mp.sqrt(tau),4)}, e1/tau={mp.nstr(e1/tau,4)})")
