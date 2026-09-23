# zi_twosaddle.py -- HEURISTIC/floating point. zeta=i: two-saddle amplitudes (sublattices f_e+f_o, ratio R=icz/((1-iz)(1+z)))
# predict zeros 1+rho e^{dV/t}=0 and compare with findroot. Also see obstruction note: T_i=Re(V0 e^{-i theta})=-0.0707<0.
from mpmath import *
mp.dps=30
c0=mpc(-2,2); Lw=log(c0)
Phi=lambda x: x*Lw-x*x-polylog(2,exp(-8*x))/16+pi**2/96
d2=lambda x: -2-4*exp(-8*x)/(1-exp(-8*x))
w=1j*(4-sqrt(15))
x0=-(log(w)-2j*pi)/4; xm=x0-1j*pi/2
def a(x):
  z=exp(-2*x)
  Cp=log(1-1j*z)/4-log(1+1j*z)/4-log(1-z)/2
  R=1j*c0*z/((1-1j*z)*(1+z))
  return exp(x*(-1+1j)/2+Cp)*(1+R), 1+R
V0=Phi(x0); Vm=Phi(xm)-1j*pi*xm
dV=Vm-V0
print('x0',x0,'xm',xm,'Phi\'\'',d2(x0),d2(xm))
A0,r0=a(x0); Am,rm=a(xm)
print('1+R at x0,x-1:',r0,rm)
rho=Am/A0
print('rho',rho,'dV',dV)
th=atan(pi/(6*log(2)))
mp.dps=60
def B(q):
    s=mpc(1); poch=mpc(1); aa=-2*(1-q); big=1; k=1
    while True:
        poch*=(1-q**(2*k-1))*(1-q**(2*k))
        term=aa**k*q**(k*k)/poch
        s+=term; big=max(big,abs(term))
        if abs(term)<mpf(10)**(-mp.dps-5)*big and k>10: break
        k+=1
    return s
for sgn in [1,-1]:
 for j in [5,10,20,40]:
  u=(log(-1/(sgn*rho))+2j*pi*j)/dV
  if re(u)<0: u=(log(-1/(sgn*rho))-2j*pi*j)/dV
  t0=1/u
  try:
    ts=findroot(lambda tt:B(1j*exp(-tt)),t0)
    print('sgn',sgn,'j',j,'pred t',nstr(t0,8),'true',nstr(ts,8),'|1/t-1/t0|',nstr(abs(1/ts-u),5),'arg deg',nstr(arg(ts)*180/pi,6))
  except Exception as e: print('fail',j,e)
