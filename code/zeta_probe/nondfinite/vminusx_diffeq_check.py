# Numerical check: bracket B = t1-(1-x)/(2x) at travel poles; phi-decomposition
from mpmath import mp, mpf, findroot, sqrt, exp, log, sinh, cosh, binomial
import sys
mp.dps=int(sys.argv[2]) if len(sys.argv)>2 else 80
def coeffs(q,J):
    a=[mpf(1)]; p=mpf(1)
    for j in range(1,J):
        p*=(1-q**(2*j-1))*(1-q**(2*j))
        a.append((-1)**j*q**(j*j+j)/p)
    return a
def Jof(q):
    tau=abs(log(abs(q))); return int(40/tau**0.75)+60
def g(q):
    Z2=2*(1-q)/q; a=coeffs(q,Jof(q))
    return sum(a[j]*Z2**j for j in range(len(a)))
def psi_der(q,k,t,a=None):
    Z2=2*(1-q)/q
    if a is None: a=coeffs(q,Jof(q))
    return sum(a[j]*(2*j)**k*(Z2*exp(2*t))**j for j in range(len(a)))
def phi_der(q,k,t,a):
    # phi=e^{-t/2}psi ; phi^(k)=e^{-t/2} sum C(k,i)(-1/2)^{k-i} psi^(i)
    return exp(-t/2)*sum(binomial(k,i)*(mpf(-1)/2)**(k-i)*psi_der(q,i,t,a) for i in range(k+1))
guesses=[mpf('0.4494536306')]+[mpf(l.strip()) for l in open('/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/poles.txt').readlines()]
M=int(sys.argv[1]) if len(sys.argv)>1 else 12
for m,g0 in enumerate(guesses[:M],1):
    q=findroot(g,(g0*(1-mpf(10)**-9),g0*(1+mpf(10)**-12)),solver="anderson",tol=mpf(10)**(-mp.dps+15))
    tau=-log(q); h=tau/2; x=sqrt(q); a=coeffs(q,Jof(q))
    psi=lambda t: psi_der(q,0,t,a)
    Se=psi(-h); P12=-(psi(h)+psi(-h))/2; t1=P12/Se
    B=t1-(1-x)/(2*x)
    # identity check (E') at t=0.3h
    phi=lambda t: exp(-t/2)*psi(t)
    tt=mpf('0.3')*h
    Eres=phi(tt+2*h)+phi(tt-2*h)-(2*cosh(h)-4*sinh(h)*exp(2*tt))*phi(tt)
    A1=phi_der(q,1,0,a); gam=4*sinh(h)+2-2*cosh(h); D=4-gam/3
    main=4*h**2*sinh(h)/D*A1
    E2=phi(h)+phi(-h)
    w=sqrt(2/tau)
    M6=max(abs(phi_der(q,6,s*tau/8,a)) for s in range(-8,9))
    print(m,'tau=%s'%mp.nstr(tau,6),'B/tau^2=',mp.nstr(B/tau**2,10),'E2/main-1=',mp.nstr(E2/main-1,5),
          'Eres=',mp.nstr(Eres,3),'phi\'(0)/w=',mp.nstr(A1/w,6),'M6/w^5~',mp.nstr(M6/w**5,5),'M6/w^6',mp.nstr(M6/w**6,4),flush=True)
