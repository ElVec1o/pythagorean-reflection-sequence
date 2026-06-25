#!/usr/bin/env python3
# Test the TWO-saddle hypothesis: integrand H(x) on real line is the boundary value; the steepest
# descent picks up a conjugate pair x*, x*' = -conj(x*)? Let's locate ALL saddles of
# Phitot(x) = -x^2/4tau + log H(x) in a box and sum their leading contributions.
# Also directly: compare to high-accuracy numerical value of the integral (ground truth) and to Sigma.
import mpmath as mp
mp.mp.dps=30
def qpoch_inf(a,p,tol=mp.mpf(10)**(-30),NM=50000):
    r=mp.mpc(1);ai=a
    for i in range(NM):
        r*=(1-ai);ai*=p
        if abs(ai)<tol:break
    return r
def setup(tau):
    q=mp.e**(-tau);p=q*q;c=2*q**2*(1-q);return q,p,c
def logH(x,tau):
    q,p,c=setup(tau);e=mp.e**(1j*x);t=-c*e
    Sin=(1/t)*(1/qpoch_inf(t,p)-1)
    return mp.log(Sin)-mp.log(qpoch_inf(-p*e,p))
def Phitot(x,tau): return -x*x/(4*tau)+logH(x,tau)
def Sigma_direct(tau,K=400):
    q=mp.e**(-tau);p=q*q;u=2*q/(1-p);s=u
    for k in range(K):
        u*=-2*(1-q)*q**(2*k+3)/((1-q**(2*k+4))*(1-q**(2*k+3)));s+=u
        if abs(u)<mp.mpf(10)**(-40) and k>20:break
    return s
def Sigma_IZ_numeric(tau,T=None):
    # ground-truth numeric integral, high T, to confirm rep value == Sigma
    q,p,c=setup(tau)
    PRE=2*q/(mp.sqrt(4*mp.pi*tau)*qpoch_inf(p**mp.mpf(1.5),p))
    if T is None: T=max(30, 12*mp.sqrt(2*tau)*0+30)
    def integ(x): return (mp.e**(Phitot(x,tau))).real
    val=mp.quad(integ,[-T,0,T])
    return PRE*val

h=mp.mpf("1e-7")
def Pp(x,tau):return (Phitot(x+h,tau)-Phitot(x-h,tau))/(2*h)
def Ppp(x,tau):return (Phitot(x+h,tau)-2*Phitot(x,tau)+Phitot(x-h,tau))/h**2

for tau in [mp.mpf("0.1"),mp.mpf("0.05")]:
    q,p,c=setup(tau);w=mp.sqrt(2/tau)
    PRE=2*q/(mp.sqrt(4*mp.pi*tau)*qpoch_inf(p**mp.mpf(1.5),p))
    # ground truth
    Snum=Sigma_IZ_numeric(tau); Sd=Sigma_direct(tau)
    print(f"tau={mp.nstr(tau,3)} w={mp.nstr(w,5)}: rep_numeric={mp.nstr(Snum,12)}  Sigma={mp.nstr(Sd,12)}  (match {mp.nstr(Snum-Sd,3)})",flush=True)
    # find saddles from a grid of starts
    saddles=[]
    for re0 in [mp.mpf(r) for r in [-2.5,-1.5,1.5,2.5]]:
        for im0 in [mp.mpf(im) for im in [-1.5,-0.8,0.8,1.5]]:
            try:
                xs=mp.findroot(lambda x:Pp(x,tau), mp.mpc(re0,im0))
                # filter: keep only saddles in a sane box and with moderate RePhi
                if abs(xs.real)<4 and abs(xs.imag)<4 and Phitot(xs,tau).real < 5:
                    if all(abs(xs-s)>mp.mpf("1e-6") for s in saddles): saddles.append(xs)
            except: pass
    # report saddles with Re Phitot (descending order of contribution)
    contribs=[]
    for xs in saddles:
        try:
            ph=Phitot(xs,tau)
            if ph.real>5: continue
            pp2=Ppp(xs,tau)
            I=mp.e**(ph)*mp.sqrt(2*mp.pi/(-pp2))
            contribs.append((xs,PRE*I,ph.real))
        except: pass
    contribs.sort(key=lambda z:-z[2])
    print("  saddles (x*, PRE*I, RePhitot):",flush=True)
    for xs,ci,rp in contribs[:6]:
        print(f"    x*={mp.nstr(xs,8):>26}  contrib={mp.nstr(ci,8):>26}  RePhi={mp.nstr(rp,6)}",flush=True)
    # sum of the two dominant (conjugate?) saddles
    if len(contribs)>=2:
        tot=contribs[0][1]+contribs[1][1]
        print(f"  sum of top-2 saddle contribs = {mp.nstr(tot,10)}  (Sigma={mp.nstr(Sd,8)})",flush=True)
