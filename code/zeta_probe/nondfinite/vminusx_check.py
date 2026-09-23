# Numerical check at travel poles: bracket B, B/tau^2, the certified bounds vs true values.
from mpmath import mp, mpf, findroot, sqrt, exp, log, sinh, cosh, binomial
import sys
mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 45
def coeffs(q,J,odd=False):
    a=[]; p=mpf(1)
    for j in range(J):
        if odd:
            p*= (1-q) if j==0 else (1-q**(2*j))*(1-q**(2*j+1))
        elif j>0: p*=(1-q**(2*j-1))*(1-q**(2*j))
        a.append((-1)**j*q**(j*j+j)/p)
    return a
def Jof(q):
    tau=abs(log(abs(q))); return int(30/tau**0.75)+60
def g(q):
    Z2=2*(1-q)/q; a=coeffs(q,Jof(q)); return sum(a[j]*Z2**j for j in range(len(a)))
def psi_der(q,k,t,a):
    Z2=2*(1-q)/q; return sum(a[j]*(2*j)**k*(Z2*exp(2*t))**j for j in range(len(a)))
def phi_der(q,k,t,a):
    return exp(-t/2)*sum(binomial(k,i)*(mpf(-1)/2)**(k-i)*psi_der(q,i,t,a) for i in range(k+1))
guesses=[mpf('0.4494536306')]+[mpf(l.strip()) for l in open('/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/poles.txt').readlines()]
m0,m1=int(sys.argv[1]),int(sys.argv[2])
for m in range(m0,m1+1):
    g0=guesses[m-1]
    q=findroot(g,(g0*(1-mpf(10)**-9),g0*(1+mpf(10)**-12)),solver="anderson",tol=mpf(10)**(-mp.dps+12))
    tau=-log(q); h=tau/2; x=sqrt(q); w=sqrt(2/tau); J=Jof(q); a=coeffs(q,J)
    Z=sqrt(2*(1-q)/q)
    psi=lambda t: psi_der(q,0,t,a)
    Se=psi(-h); P12=-(psi(h)+psi(-h))/2; t1=P12/Se
    B=t1-(1-x)/(2*x)
    # s(Z)=sin(Z;q^2) = sum (-1)^j Z^{2j+1} q^{j^2+j}/(q;q)_{2j+1}
    ao=coeffs(q,J,odd=True); sZ=sum(ao[j]*Z**(2*j+1) for j in range(J))
    idres=psi(-2*h)-q*Z*sZ            # f(qZ)=qZ s(Z)
    A1=phi_der(q,1,0,a)
    D=4-(4*sinh(h)+2-2*cosh(h))/3; Lam=exp(h/2)*sinh(h)/(2*h*D)
    ts=[s*tau/4 for s in range(-4,5)]
    k2=max(abs(psi_der(q,2,t,a)) for t in ts)/w**2
    k3=max(abs(phi_der(q,3,t,a)) for t in ts)/w**3
    k6=max(abs(phi_der(q,6,t,a)) for t in ts)/w**6
    print(m,'tau=%s'%mp.nstr(tau,6),'B=%s'%mp.nstr(B,6),'B/tau^2=%s'%mp.nstr(B/tau**2,10),'B/(Lam tau^2)-1=%s'%mp.nstr(B/(Lam*tau**2)-1,4),
          '|a|/w=%s'%mp.nstr(abs(A1)/w,6),'|s(Z)|=%s'%mp.nstr(abs(sZ),6),'sqrt(1-.61Z)=%s'%mp.nstr(sqrt(1-mpf('0.61')*Z),6),
          'id=%s'%mp.nstr(idres,2),'k2,k3,k6=%s,%s,%s'%(mp.nstr(k2,4),mp.nstr(k3,4),mp.nstr(k6,4)),flush=True)
