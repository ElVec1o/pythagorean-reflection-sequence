# second Stokes ray at zeta=-1: predicted zeros t=(L'(t)+3 i pi)/(2a+1) (zeros of the full theta function)
from mpmath import mp, mpf, mpc, exp, log, pi, findroot, nstr, arg
mp.dps=50
def B(q):
    s=mpc(1); poch=mpc(1); a=-2*(1-q); big=1; k=1
    while True:
        poch*=(1-q**(2*k-1))*(1-q**(2*k))
        term=a**k*q**(k*k)/poch
        s+=term; big=max(big,abs(term))
        if abs(term)<mpf(10)**(-mp.dps-5)*big and k>10: break
        k+=1
    return s
Lp=lambda t: log(2*(1+exp(-t)))
for b,al in ((3,(35,40,50,60)),(5,(60,80,100,130))):
  for a in al:
    t=(log(4)+b*1j*pi)/(2*a+1)
    for it in range(60): t=(Lp(t)+b*1j*pi)/(2*a+1)
    try:
        tz=findroot(lambda tt: B(-exp(-tt)), t, tol=mpf(10)**-40)
        print('ray (2n-1)=%d a=%d pred t='%(b,a),nstr(t,10),' zero=',nstr(tz,10),' |diff|=',nstr(abs(tz-t),3),' arg(t)=',nstr(arg(t)*180/pi,6),' |q|=',nstr(abs(exp(-t)),6))
    except Exception as ex: print(b,a,'fail',ex)
