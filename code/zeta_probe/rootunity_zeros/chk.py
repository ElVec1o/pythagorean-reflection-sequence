from mpmath import mp, mpf, mpc, exp, log, pi, sqrt, nstr, polylog, atan, cos, sin
mp.dps=40
def B(q):
    s=mpc(1); poch=mpc(1); a=-2*(1-q); big=1; k=1
    while True:
        poch*=(1-q**(2*k-1))*(1-q**(2*k))
        term=a**k*q**(k*k)/poch
        s+=term; big=max(big,abs(term))
        if abs(term)<mpf(10)**(-mp.dps-5)*big and k>10: break
        k+=1
    return s
L=log(4); x0=-log(sqrt(5)-2)/2
Phi0=x0*L-x0**2-polylog(2,exp(-4*x0))/4+pi**2/24
amp=sqrt(2/sqrt(5))*exp(-x0/2-log(1-exp(-2*x0))/2)
print('amp=',amp)
for deg in [0,40,60,66.19,72,78]:
  for r in [0.2,0.1,0.05,0.025]:
    t=r*exp(1j*deg*pi/180)
    Lp=log(2*(1+exp(-t)))
    th=1+exp((-pi**2+1j*pi*Lp)/t)
    R=B(-exp(-t))/(th*amp*exp(Phi0/t))
    print('deg=%6.2f |t|=%.3f  B/(amp e^{Phi0/t} (1+e^{Lam/t})) ='%(deg,r), nstr(R,10), '  |e^{Lam/t}|=',nstr(abs(th-1),4))
