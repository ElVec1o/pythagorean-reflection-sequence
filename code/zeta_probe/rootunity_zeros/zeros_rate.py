# zeros_rate.py -- zeros t*_j of B(q)=cos(Z;q^2), q=-e^{-t}, near t0_j=(log4+i pi)/(2j+3/2):
# prints |t*_j - t0_j| j^3 (-> ~0.18), distance to the zero of 1+e^{Lam_t/t}, and (arg t*_j - theta1) j^2.
# 80-digit working precision (the series for B cancels heavily as |t| -> 0).  Used in paper2a prop:minusone.
from mpmath import mp, mpf, mpc, exp, log, pi, findroot, arg, nstr, atan
mp.dps=80
def B(q):
    s=mpc(1); poch=mpc(1); a=-2*(1-q); big=1; k=1
    while True:
        poch*=(1-q**(2*k-1))*(1-q**(2*k)); term=a**k*q**(k*k)/poch
        s+=term; big=max(big,abs(term))
        if abs(term)<mpf(10)**(-mp.dps-5)*big and k>10: break
        k+=1
    return s
th1=atan(pi/log(4)); L=log(4)
from mpmath import polylog, sqrt
x0=log(2+sqrt(5))/2; Phi0=x0*L-x0**2-polylog(2,exp(-4*x0))/4+pi**2/24
Lp=lambda t: log(2*(1+exp(-t)))
for j in [3,5,8,10,15,20,30,40,60]:
    t0=(L+1j*pi)/(2*j+mpf(3)/2)
    tm=t0
    for it in range(80): tm=(Lp(tm)+1j*pi)/(2*j+1)   # zero of 1+e^{Lam'/t}
    try:
        tz=findroot(lambda tt: B(-exp(-tt))*exp(-Phi0/tt), tm, tol=mpf(10)**-50)
    except Exception as e:
        print(j,'fail',str(e)[:60]); continue
    print(j,'|t|=%.4f'%float(abs(tz)),' |tz-t0|j^3=',nstr(abs(tz-t0)*j**3,5),' |tz-tmodel|=',nstr(abs(tz-tm),4),' r*log|tz-tm| =',nstr(abs(tz)*log(abs(tz-tm)),4), ' (arg tz-th1)*j^2=',nstr((arg(tz)-th1)*j**2,5),flush=True)
