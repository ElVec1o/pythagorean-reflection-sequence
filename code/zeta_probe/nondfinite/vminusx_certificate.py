# Interval-arithmetic certificate for the derivative constants K2 (psi''), K3 (phi'''), K6 (phi^(6))
# on the box tau in (0,taubar], |t|<=tau, and the resulting eps1, eps2 of the V(-x_m) bracket proof.
from mpmath import iv, mp, mpf
import sys
iv.dps=int(sys.argv[1]) if len(sys.argv)>1 else 30
N=int(sys.argv[2]) if len(sys.argv)>2 else 3000
tb=iv.mpf('5e-3'); G=iv.mpf(14)
qb=iv.exp(-tb)
lam = iv.exp(tb)*iv.sqrt(tb/(1-qb))            # sup lambda  (increasing in tau and t)
kap_lo = iv.exp(-2*tb)/2                        # inf kappa2
kap_hi = iv.exp(2*tb)/(1+qb)                    # sup kappa2
beta = kap_hi*tb                                # sup of 2 kappa2 sigma^2 = kappa2*tau
rhob = iv.sqrt(2*(1-qb))*iv.exp(tb)             # sup rho
K3 = 2*iv.sqrt(2)*iv.sqrt(1-qb)*iv.exp(3*tb)/(9*qb**2*(1-rhob/qb))   # sup of sum_{n>=3} rho^n/(n(1-q^n))
sigb = iv.sqrt(tb/2)
def binom(k,j):
    from math import comb; return comb(k,j)
def He(j,g):
    a,b=iv.mpf(1),g
    if j==0: return a
    for n in range(1,j): a,b=b,g*b-n*a
    return b
def absup(x):  # upper bound of |x| for an interval
    return max(abs(x.a),abs(x.b))
def Pbar(k,g,phi):
    if not phi: return absup(He(k,g))
    return sum(binom(k,j)*(sigb.b/2)**(k-j)*absup(He(j,g)) for j in range(k+1))
def integral(k,phi):
    tot=iv.mpf(0); dg=G/N
    for i in range(N):
        cell=iv.mpf([ (i*dg).a, ((i+1)*dg).b ])
        f=iv.exp(lam*cell+(beta-iv.mpf(1)/2)*cell**2)*Pbar(k,cell,phi)
        tot+=f*dg
    tot=2*tot/iv.sqrt(2*iv.pi)
    # tail g>=G: g^k e^{lam g-(1/2-beta)g^2} e^{g} decreasing there => tail <= const*G^k e^{lam G-(1/2-beta)G^2}
    Pk = sum(binom(k,j)*(sigb.b/2)**(k-j)*(2*G)**j for j in range(k+1)) if phi else (2*G)**k  # |He_j(g)|<= (2g)^j for g>=2? crude, g>=G
    tail=2*Pk*iv.exp(lam*G-(iv.mpf(1)/2-beta)*G**2)/iv.sqrt(2*iv.pi)
    return tot+tail
pref_phi = iv.exp(tb/2+K3-kap_lo)
pref_psi = iv.exp(K3-kap_lo)
K2 = pref_psi*integral(2,False)
K3p= pref_phi*integral(3,True)
K6 = pref_phi*integral(6,True)
print('lambda<=',lam.b,'kappa_lo',kap_lo.a,'kappa_hi',kap_hi.b,'K3exp',K3.b)
#print('lambda<=',lam.b,' kappa in [',kap_lo.a,',',kap_hi.b,'] K3exp<=',K3.b)
print('K2 (|psi\'\'|<=K2 w^2)  <=',K2.b)
print('K3 (|phi\'\'\'|<=K3 w^3) <=',K3p.b)
print('K6 (|phi^(6)|<=K6 w^6) <=',K6.b)
# A_low = inf over tau of sqrt((1-q)/tau)*sqrt(1-0.61 Z) - (tau/3) K3  (all monotone, worst at taubar)
Zb=iv.sqrt(2*(1-qb)/qb)
A_low = iv.sqrt((1-qb)/tb)*iv.sqrt(1-iv.mpf('0.61')*Zb) - tb/3*K3p
hb=tb/2
gam = 2*(iv.exp(hb)-iv.exp(-hb))+2-(iv.exp(hb)+iv.exp(-hb))
eps1 = (gam/90+iv.mpf(1)/3+4*(iv.mpf(2)/45+iv.mpf(1)/360))*K6*iv.sqrt(tb)/(4*iv.sqrt(2)*A_low)
eps2 = K2*iv.sqrt(tb)/(2*iv.sqrt(2)*A_low)
print('A_low >=',A_low.a,' Z<=',Zb.b)
print('eps1 <=',eps1.b,'   eps2 <=',eps2.b)
print('B/tau^2 >= (1/8)(1-eps1)/(1+eps2) >=', ((1-eps1)/(1+eps2)/8).a)
# --- assembly with the ROUNDED-UP constants quoted in the text ---
K2r,K3r,K6r=iv.mpf('3.24'),iv.mpf('5.68'),iv.mpf('53.3')
assert K2r>K2 and K3r>K3p and K6r>K6
Ar = iv.sqrt((1-qb)/tb)*iv.sqrt(1-iv.mpf('0.61')*Zb) - tb/3*K3r
e1 = (gam/90+iv.mpf(1)/3+4*(iv.mpf(2)/45+iv.mpf(1)/360))*K6r*iv.sqrt(tb)/(4*iv.sqrt(2)*Ar)
e2 = K2r*iv.sqrt(tb)/(2*iv.sqrt(2)*Ar)
Db=4-gam/3; Lam_hi=iv.exp(hb/2)*(iv.exp(hb)-iv.exp(-hb))/(4*hb*Db)
print('rounded: A_low>=',Ar.a,' eps1<=',e1.b,'=',(e1/iv.sqrt(tb)).b,'*sqrt(tau)  eps2<=',e2.b,'=',(e2/iv.sqrt(tb)).b,'*sqrt(tau)')
print('Lambda(taubar)<=',Lam_hi.b,'  beta/tau^2 in [',((1-e1)/(1+e2)/8).a,',',(Lam_hi*(1+e1)/(1-e2)).b,']')
