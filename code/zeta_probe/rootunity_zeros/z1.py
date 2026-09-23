# zeros of B near q=-1 vs theta-function prediction t_j=(L'(t)+i pi)/(2j+1), q=-e^{-t}
from mpmath import mp, mpf, mpc, exp, log, pi, findroot, fabs, arg, nstr
mp.dps=40
def B(q):
    s=mpc(1); poch=mpc(1); a=-2*(1-q); big=1
    k=1
    while True:
        poch*=(1-q**(2*k-1))*(1-q**(2*k))
        term=a**k*q**(k*k)/poch
        s+=term; big=max(big,abs(term))
        if abs(term)<mpf(10)**(-mp.dps-5)*big and k>10: break
        k+=1
    return s
Lp=lambda t: log(2*(1+exp(-t)))
for j in range(3,26):
    t=(log(4)+1j*pi)/(2*j+1)
    for it in range(50): t=(Lp(t)+1j*pi)/(2*j+1)
    tz=findroot(lambda tt: B(-exp(-tt)), t)
    print(j, 'pred t=',nstr(t,12),' zero t=',nstr(tz,12),' |diff|=',nstr(abs(tz-t),3), ' |t|=',nstr(abs(t),4),' q=',nstr(-exp(-tz),8))
